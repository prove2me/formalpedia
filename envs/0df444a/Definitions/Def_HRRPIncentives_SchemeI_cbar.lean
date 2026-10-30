-- Prove2me | Definitions.Def_HRRPIncentives_SchemeI_cbar
-- name    : HRRPIncentives_SchemeI_cbar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:13:33.483392+00:00
-- url     : https://prove2.me/theorems/01611212-9b9e-4157-a223-019b6c690d4a
-- title:
--   Cost yardstick $\bar c_i=\frac1{N-1}\sum_{k\ne i}c_k$
-- statement:
--   Given the actions $(r_k,c_k)$ of $N$ hospitals, the cost yardstick of hospital $i$ is the average marginal cost of the other hospitals (display (6)):
--
--   $$\bar c_i=\frac{1}{N-1}\sum_{k\neq i}c_k .$$
--
--   It is the per-visit reimbursement hospital $i$ receives under yardstick competition; it does not depend on hospital $i$'s own action.
--
--   **Formalization Note** Profiles are maps from $\{0,\dots,N-1\}$ to pairs $(r_k,c_k)$; theorems using it assume $N\ge2$.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, display (6), p. 11

import Mathlib

namespace HRRPIncentives.SchemeI

/-- The cost yardstick of hospital `i` in (6): `c̄_i = (1/(N−1)) Σ_{k ≠ i} c_k`, the average
marginal cost of the other `N − 1` hospitals.

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, display (6), p. 11.

**Formalization Note.** A profile is `x : Fin N → ℝ × ℝ`, with `(x k).2 = c_k`. `N` is cast to
`ℝ` before subtracting 1; the theorems assume `2 ≤ N`. -/
noncomputable def cbar {N : ℕ} (x : Fin N → ℝ × ℝ) (i : Fin N) : ℝ :=
  (1 / ((N : ℝ) - 1)) * ∑ k ∈ Finset.univ.erase i, (x k).2

end HRRPIncentives.SchemeI


