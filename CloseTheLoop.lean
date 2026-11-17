/-
  Close the Loop — Minimal
  Only what is needed to close the loop on the field.
  
  Credit: Robert Laakkonen (@rslaakkonen)
  Formalization of middle-as-place, 3→4, 13→26→52, and base-60 closure.
-/

-- 1. Middle is a place. Count > 0.
def Middle : Nat := 1
theorem middle_not_zero : Middle ≠ 0 := by decide

-- 2. Ternary: two ends + middle kept as off.
inductive Point where
  | endA : Point
  | middle : Point
  | endB : Point
deriving DecidableEq, Repr

def Point.isOff : Point → Bool := fun
  | .middle => true
  | _ => false

theorem middle_held_off : Point.middle.isOff = true := rfl

-- 3. Three -> Four. Triangle settles to quad.
theorem three_to_four : 3 + Middle = 4 := by decide

-- 4. Field closes: 13 -> 26 -> 52.
theorem thirteen_to_twenty_six : 13 * 2 = 26 := by decide
theorem twenty_six_to_fifty_two : 26 * 2 = 52 := by decide

-- 5. Power -> Return. 9 alone does not close. 9 + 12 closes.
theorem nine_is_incomplete : (9 : Nat) ≠ 12 := by decide
theorem nine_plus_twelve_closes : 9 + 12 = 21 := by decide

-- 6. Base 60 holds 3 and 4 without blow-up.
theorem base60_holds_three_and_four : 60 % 3 = 0 ∧ 60 % 4 = 0 :=
  ⟨by decide, by decide⟩

-- 7. Loop closed: part needs its mechanics.
theorem loop_closed : (26 : Nat) ≠ 52 ∧ (9 : Nat) ≠ 12 ∧ (3 : Nat) ≠ 4 :=
  ⟨by decide, by decide, by decide⟩
