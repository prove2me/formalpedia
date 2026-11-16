-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_hardP
-- name    : BorderDiffEq_Supplement_hardP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:52:22.222218+00:00
-- url     : https://prove2.me/theorems/dc4ceb47-a4ac-4414-be7c-e92f3461ed62
-- title:
--   The polynomial $P_{k+1,d}=\sum_{i=1}^{k+1}\prod_{j=1}^d x_{i,j}$
-- statement:
--   For integers $k,d$,
--   $$
--   P_{k+1,d}(x)=\sum_{i=1}^{k+1}\prod_{j=1}^{d}x_{i,j},
--   $$
--   a polynomial in the $N=(k+1)d$ variables $x_{i,j}$. It is the hard polynomial of the top fan-in hierarchy (Theorem 2.3).
--
--   **Formalization Note** The variable $x_{i,j}$ ($0$-indexed) is `finProdFinEquiv (i, j)` in `Fin ((k+1)*d)`, matching the `Fin N` variables of the published `InBorderSPS`.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §2.1.3, p.7; Theorem 9.4, p.68

import Mathlib

namespace BorderDiffEq.Supplement

/-- **The polynomial `P_{k+1,d}`** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of
Structured Algebraic Circuits via Differential Equations*, manuscript (STOC 2027 submission),
§2.1.3, p.7, and Theorem 9.4, p.68):
`P_{k+1,d}(x) := ∑_{i=1}^{k+1} ∏_{j=1}^{d} x_{i,j}`, in `N = (k+1)d` variables.

**Formalization Note.** The variable `x_{i,j}` (`i ∈ [k+1]`, `j ∈ [d]`, 0-indexed) is the variable
`finProdFinEquiv (i, j)` of `Fin ((k+1)*d)`, so the polynomial lives in the same `Fin N` variable
convention as the base mission's `InBorderSPS`. -/
noncomputable def hardP (F : Type) [CommRing F] (k d : ℕ) : MvPolynomial (Fin ((k + 1) * d)) F :=
  ∑ i : Fin (k + 1), ∏ j : Fin d, MvPolynomial.X (finProdFinEquiv (i, j))

end BorderDiffEq.Supplement


