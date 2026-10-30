-- Prove2me | Definitions.Def_HRRPIncentives_SchemeI_rbar
-- name    : HRRPIncentives_SchemeI_rbar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:13:48.678075+00:00
-- url     : https://prove2.me/theorems/411b67b8-35f3-4205-9425-5e7ccd59c859
-- title:
--   Readmission yardstick $\bar r_i=\frac1{N-1}\sum_{k\ne i}r_k$
-- statement:
--   Given the actions $(r_k,c_k)$ of $N$ hospitals, the readmission yardstick of hospital $i$ is the average readmission rate of the other hospitals (display (6)):
--
--   $$\bar r_i=\frac{1}{N-1}\sum_{k\neq i}r_k .$$
--
--   It is the target readmission level against which hospital $i$ is penalized or rewarded; it does not depend on hospital $i$'s own action.
--
--   **Formalization Note** Profiles are maps from $\{0,\dots,N-1\}$ to pairs $(r_k,c_k)$; theorems using it assume $N\ge2$.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, display (6), p. 11

import Mathlib

namespace HRRPIncentives.SchemeI

/-- The readmission yardstick of hospital `i` in (6): `r̄_i = (1/(N−1)) Σ_{k ≠ i} r_k`, the
average readmission rate of the other `N − 1` hospitals.

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, display (6), p. 11.

**Formalization Note.** A profile is `x : Fin N → ℝ × ℝ`, with `(x k).1 = r_k`. `N` is cast to
`ℝ` before subtracting 1; the theorems assume `2 ≤ N`. -/
noncomputable def rbar {N : ℕ} (x : Fin N → ℝ × ℝ) (i : Fin N) : ℝ :=
  (1 / ((N : ℝ) - 1)) * ∑ k ∈ Finset.univ.erase i, (x k).1

end HRRPIncentives.SchemeI


