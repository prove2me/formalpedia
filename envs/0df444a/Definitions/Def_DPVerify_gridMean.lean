-- Prove2me | Definitions.Def_DPVerify_gridMean
-- name    : DPVerify_gridMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:29.719212+00:00
-- url     : https://prove2.me/theorems/433bf0dd-c37f-4976-a39a-e41e2ed79332
-- title:
--   Expectation over $\mathrm{Unif}\{1/L,\dots,1\}$
-- statement:
--   For a positive integer $L$ and a function $f$, the expectation of $f(u)$ for $u$ uniform on the grid $\{1/L,2/L,\dots,1\}$ is
--
--   $$
--   \mathbb E_u f(u)=\frac1L\sum_{k=1}^{L}f\!\left(\frac kL\right).
--   $$
--
--   In Theorem 4.1's proof each hash value $U_m(r)$ is uniform on this grid when $r$ is drawn at random, so expectations over $r$ of functions of $U_m(r)$ are of this form.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Theorem 4.1's proof, p.11 (PDF p.14)

import Mathlib

set_option autoImplicit false

namespace DPVerify

/-- The expectation `E_u f(u)` for `u ∼ Unif{1/L, 2/L, …, 1}` (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Theorem 4.1's proof, p.11 =
PDF p.14: "`U_m(r) ∼ Unif{1/L, . . . , 1}`"), namely `(1/L) ∑_{k=1}^{L} f(k/L)`.

**Formalization Note** For each fixed `m`, `U_m(r)` with `r ∼ R` has exactly this law, so
`E_{r∼R} f(U_m(r))` is `gridMean L f`. -/
noncomputable def gridMean (L : ℕ) (f : ℝ → ℝ) : ℝ :=
  (1 / (L : ℝ)) * ∑ k ∈ Finset.Icc 1 L, f ((k : ℝ) / L)

end DPVerify


