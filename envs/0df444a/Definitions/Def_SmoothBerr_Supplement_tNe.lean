-- Prove2me | Definitions.Def_SmoothBerr_Supplement_tNe
-- name    : SmoothBerr_Supplement_tNe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:55:23.948569+00:00
-- url     : https://prove2.me/theorems/6d2ae002-9272-403d-9fe8-4b571a9ec7a2
-- title:
--   $t_{\mathrm{ne}}(A,b)$, Eq. (2)
-- statement:
--   For a tolerance $\varepsilon$, the quantity
--   $$
--   t_{\mathrm{ne}}(A,b):=\min\bigl\{2k+1:\ k\ge0,\ \exists\,x\in K_k(A^\top A,A^\top b)\text{ with }\mathrm{berr}(A,b,x)\le\varepsilon\bigr\}
--   $$
--   is the odd number of matvecs a Krylov method on the normal equations needs before its Krylov subspace contains an $\varepsilon$-backward-error solution. It is the benchmark of Theorem 4.4.
--
--   **Formalization Note** The minimum is taken in $\mathbb N\cup\{\infty\}$, with value $\infty$ when no $k$ works; $K_k$ has the $k+1$ generators $(A^\top A)^jA^\top b$, $0\le j\le k$.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), §4.2, Eq. (2), p.6

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_BerrLe
import Definitions.Def_SmoothBerr_Supplement_rightKrylov

namespace SmoothBerr.Supplement

/-- **`t_ne(A, b)`** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error:
The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, §4.2, Eq. (2),
p.6): the least odd degree `2k + 1` (`k ≥ 0`) such that the Krylov subspace
`K_k(AᵀA, Aᵀb)` of the normal equations contains a vector `x` with `berr(A, b, x) ≤ ε`.

**Formalization Note** The minimum is taken in `ℕ∞` (`⊤` when no `k` works). `K_k(AᵀA, Aᵀb)` is
`rightKrylov A b k`, with `k + 1` generators `(AᵀA)^j Aᵀb`, `0 ≤ j ≤ k`. -/
noncomputable def tNe {n : ℕ} (ε : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : ∃ x ∈ rightKrylov A b k, BerrLe A b x ε), ((2 * k + 1 : ℕ) : ℕ∞)

end SmoothBerr.Supplement


