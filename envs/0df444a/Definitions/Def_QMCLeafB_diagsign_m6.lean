-- Prove2me | Definitions.Def_QMCLeafB_diagsign_m6
-- name    : QMCLeafB_diagsign_m6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:57:09.787832+00:00
-- url     : https://prove2.me/theorems/ac38ef39-304f-4524-8167-8df34f1a4b39
-- title:
--   QMCLeafB diagsign_m6
-- statement:
--   # leaf B phase 16 — the diagonal-sign dilation direction (member m6, direction d9 follow-up)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
/-
# leaf B phase 16 — the diagonal-sign dilation direction (member m6, direction d9 follow-up)

Brick 4 needs a direction `d` in which the relaxed body lies *above* the query centre (`hbody`,
needed by `RunPartsDilate.runParts_of_dilated`).  The identity direction used so far needs the
centre's diagonal `≤ 1 − dq/4` (`hdiagc`), which is unsatisfiable at the actual programme states: a
PSD/threshold round has the diagonal exactly `1`.

The *diagonal-sign* direction `d i = sign (1 − c i)` works instead whenever the centre's diagonal
avoids the two open bands `(1 − dq/4, 1)` and `(1, 1 + dq/4)`: if `c i < 1` the body has
`x i ≥ 1 − dq/4 ≥ c i`, if `c i > 1` it has `x i ≤ 1 + dq/4 ≤ c i`, and if `c i = 1` the coordinate
contributes nothing.  Note the band condition is *strictly weaker* than `hdiagc`: `c i = 1` is
allowed (that is exactly the threshold-round case), and so is any `c i ≥ 1 + dq/4`.

This file proves the pointwise inequality and the resulting body condition.  It is the arithmetic of
the `dM := flat(diagSign)` repair; the programme-side consequence is that the round can keep querying
`stX` (no scaled query needed) at the price of the band condition.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
set_option autoImplicit false

namespace QMCLeafB.DiagSign

/-- The sign of `1 − c` as a real number. -/
noncomputable def sgn1 (c : ℝ) : ℝ := if c < 1 then 1 else if 1 < c then -1 else 0

/-- **The diagonal-sign direction puts the body above the centre**, from the slab clause
`|x i − 1| ≤ dq/4` and the two band conditions on the centre. -/
theorem body_above_centre_of_bands {N : ℕ} {x c : Fin N → ℝ} {dq : ℝ}
    (hbody : ∀ i, |x i - 1| ≤ dq / 4)
    (hlow : ∀ i, c i < 1 → c i ≤ 1 - dq / 4)
    (hhigh : ∀ i, 1 < c i → 1 + dq / 4 ≤ c i) :
    0 ≤ ∑ i, sgn1 (c i) * (x i - c i) := by
  apply Finset.sum_nonneg
  intro i _
  have hx := hbody i
  rw [abs_le] at hx
  unfold sgn1
  by_cases h1 : c i < 1
  · rw [if_pos h1]
    have hb := hlow i h1
    nlinarith [hx.1, hx.2, hb]
  · by_cases h2 : 1 < c i
    · rw [if_neg h1, if_pos h2]
      have hb := hhigh i h2
      nlinarith [hx.1, hx.2, hb]
    · rw [if_neg h1, if_neg h2]
      ring_nf
      exact le_refl 0

/-- The same in the dilation assembly's own pairing form `d ⪝ (x − c)`. -/
theorem body_above_centre_dot {N : ℕ} {x c : Fin N → ℝ} {dq : ℝ}
    (hbody : ∀ i, |x i - 1| ≤ dq / 4)
    (hlow : ∀ i, c i < 1 → c i ≤ 1 - dq / 4)
    (hhigh : ∀ i, 1 < c i → 1 + dq / 4 ≤ c i) :
    0 ≤ (fun i => sgn1 (c i)) ⬝ᵥ (x - c) := by
  rw [dotProduct]
  simpa [Pi.sub_apply] using body_above_centre_of_bands hbody hlow hhigh

/-- **The band condition follows from `hdiagc`** (`c i ≤ 1 − dq/4`): so the diagonal-sign direction
supersedes the identity direction (whose blocker was `c i = 1`). -/
theorem bands_of_le {N : ℕ} {c : Fin N → ℝ} {dq : ℝ} (hdq : 0 < dq)
    (hlow : ∀ i, c i ≤ 1 - dq / 4) :
    ∀ i, c i < 1 → c i ≤ 1 - dq / 4 := fun i _ => hlow i

/-! ## Axiom audit -/

#print axioms QMCLeafB.DiagSign.body_above_centre_of_bands
#print axioms QMCLeafB.DiagSign.body_above_centre_dot
#print axioms QMCLeafB.DiagSign.bands_of_le

end QMCLeafB.DiagSign


