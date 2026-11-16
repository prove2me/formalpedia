-- Prove2me | Definitions.Def_SmoothedNash_Supplement_alg4Runtime
-- name    : SmoothedNash_Supplement_alg4Runtime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:07:49.640306+00:00
-- url     : https://prove2.me/theorems/58e527b9-9d1f-4d12-b6f8-b9280def56f2
-- title:
--   Running time of Algorithm 4: $(\#\mathrm{calls} + N + 1)(n+1)^\kappa$
-- statement:
--   In the cost model of Theorem 4.5 ("a constant number of these calls and polynomially many arithmetic operations in $n$ for a kernel computation and a linear-system solve" per iteration), the running time of a run with $N$ iterations is
--   $$
--   (\#\text{oracle calls} + N + 1)\,(n + 1)^\kappa .
--   $$
--
--   **Formalization Note** The polynomial is unspecified in the paper; theorems quantify over every exponent $\kappa$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Theorem 4.5, pp.28–29

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_alg4Calls
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The running time of a run of Algorithm 4 with `N` loop iterations, in the cost model of
Theorem 4.5 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Theorem 4.5, pp.28–29: "each iteration uses a constant number of these calls and
polynomially many arithmetic operations in `n` for a kernel computation and a linear-system solve"):
`(#oracle calls + N + 1) · (n + 1)^κ`.

**Formalization Note** The paper leaves the polynomial unspecified; the theorems are quantified over
every exponent `κ`. Each oracle call and each iteration's kernel computation and linear solve is
charged `(n + 1)^κ`. -/
noncomputable def alg4Runtime (κ : ℕ) {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (ε : ℝ) (N : ℕ) : ℝ :=
  ((alg4Calls F ε N : ℝ) + N + 1) * ((n : ℝ) + 1) ^ κ

end SmoothedNash.Supplement


