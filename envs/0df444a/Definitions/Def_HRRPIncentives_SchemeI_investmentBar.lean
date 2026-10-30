-- Prove2me | Definitions.Def_HRRPIncentives_SchemeI_investmentBar
-- name    : HRRPIncentives_SchemeI_investmentBar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:13:58.659199+00:00
-- url     : https://prove2.me/theorems/87ad23f9-8bbd-49f1-83fd-2753808c9092
-- title:
--   Investment-cost yardstick $\bar R_i=\frac1{N-1}\sum_{k\ne i}R(r_k,c_k)$
-- statement:
--   Given the actions $(r_k,c_k)$ of $N$ hospitals, the investment-cost yardstick of hospital $i$ is the average investment cost of the other hospitals (display (6)):
--
--   $$\bar R_i=\frac{1}{N-1}\sum_{k\neq i}R_k,\qquad R_k=R(r_k,c_k).$$
--
--   It is the lump-sum part of hospital $i$'s transfer; it does not depend on hospital $i$'s own action.
--
--   **Formalization Note** Named `investmentBar` rather than `Rbar` so that its module name does not coincide, up to letter case, with that of $\bar r_i$. Theorems using it assume $N\ge2$.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, display (6), p. 11

import Mathlib

namespace HRRPIncentives.SchemeI

/-- The investment-cost yardstick of hospital `i` in (6):
`R̄_i = (1/(N−1)) Σ_{k ≠ i} R_k` with `R_k = R(r_k, c_k)`, the average investment cost of the
other `N − 1` hospitals.

(Named `investmentBar` rather than `Rbar` so that its module name does not clash, up to
letter case, with that of `rbar`.)

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, display (6), p. 11.

**Formalization Note.** A profile is `x : Fin N → ℝ × ℝ`; `N` is cast to `ℝ` before
subtracting 1; the theorems assume `2 ≤ N`. -/
noncomputable def investmentBar (R : ℝ × ℝ → ℝ) {N : ℕ} (x : Fin N → ℝ × ℝ) (i : Fin N) :
    ℝ :=
  (1 / ((N : ℝ) - 1)) * ∑ k ∈ Finset.univ.erase i, R (x k)

end HRRPIncentives.SchemeI


