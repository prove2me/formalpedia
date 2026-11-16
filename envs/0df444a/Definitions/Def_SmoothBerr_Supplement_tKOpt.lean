-- Prove2me | Definitions.Def_SmoothBerr_Supplement_tKOpt
-- name    : SmoothBerr_Supplement_tKOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:54:48.425399+00:00
-- url     : https://prove2.me/theorems/022abc3a-1b0b-4693-b827-5e5664020acb
-- title:
--   $t_{k\text{-opt}}(A,b)$, Eq. (19)
-- statement:
--   Given a test $\mathrm{acc}$, the quantity
--   $$
--   t_{k\text{-opt}}(A,b):=\min\bigl\{2k+1:\ k\ge0,\ \exists\,x\in R_k(A,b)\text{ with }\mathrm{acc}(A,b,x)=1\bigr\}
--   $$
--   is the number of matvecs an idealized Krylov method on the normal equations needs before its Krylov subspace $R_k(A,b)$ contains a vector passing the test. It is the benchmark of Theorems 6.2 and 6.4.
--
--   **Formalization Note** The minimum is taken in $\mathbb N\cup\{\infty\}$, with value $\infty$ when no $k$ works.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), §6, Eq. (19), p.17

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_rightKrylov

namespace SmoothBerr.Supplement

/-- **`t_k-opt(A, b)`** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward
error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, §6,
Eq. (19), p.17): the least odd number `2k + 1` (`k ≥ 0`) such that the right-side Krylov subspace
`R_k(A, b)` contains a vector `x` passing the test, `acc(A, b, x) = 1`.

**Formalization Note** The minimum is taken in `ℕ∞` (`⊤` when no `k` works); the test is a
predicate. -/
noncomputable def tKOpt {n : ℕ}
    (acc : Matrix (Fin n) (Fin n) ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Prop)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : ∃ x ∈ rightKrylov A b k, acc A b x), ((2 * k + 1 : ℕ) : ℕ∞)

end SmoothBerr.Supplement


