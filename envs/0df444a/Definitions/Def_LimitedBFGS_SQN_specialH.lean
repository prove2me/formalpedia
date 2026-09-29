-- Prove2me | Definitions.Def_LimitedBFGS_SQN_specialH
-- name    : LimitedBFGS_SQN_specialH
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:22:48.492305+00:00
-- url     : https://prove2.me/theorems/cb54399c-d723-4b48-a1cb-34a4a051824c
-- title:
--   Special BFGS matrices (4)–(5): $H_0$ updated by the last $\min(K, m)$ correction pairs
-- statement:
--   Fix an initial matrix $H_0 \in \mathbb{R}^{n\times n}$, a number $m$ of stored corrections, and sequences of correction pairs $(s_j, y_j)_{j \ge 0}$ in $\mathbb{R}^n$. For a list of pairs $(s_{j_1}, y_{j_1}), \dots, (s_{j_r}, y_{j_r})$ (oldest first), let $\mathrm{upd}(H_0; \text{list})$ be $H_0$ updated by the BFGS product form $H \mapsto v^T H v + \rho s s^T$ once for each pair, oldest first.
--
--   The **special BFGS matrix** $H_K$ is $H_0$ updated by the pairs
--
--   $$(s_j, y_j), \qquad j = K - \min(K, m), \dots, K - 1 .$$
--
--   Writing $K = k+1$: for $k + 1 \le m$ these are all pairs $j = 0, \dots, k$, and
--
--   $$H_{k+1} = v_k^T \cdots v_0^T H_0 v_0 \cdots v_k + v_k^T \cdots v_1^T \rho_0 s_0 s_0^T v_1 \cdots v_k + \cdots + v_k^T \rho_{k-1} s_{k-1} s_{k-1}^T v_k + \rho_k s_k s_k^T,$$
--
--   which is the usual BFGS matrix, formula (4); for $k + 1 > m$ only the $m$ most recent pairs $j = k-m+1, \dots, k$ are used, and
--
--   $$H_{k+1} = v_k^T \cdots v_{k-m+1}^T H_0 v_{k-m+1} \cdots v_k + v_k^T \cdots v_{k-m+2}^T \rho_{k-m+1} s_{k-m+1} s_{k-m+1}^T v_{k-m+2} \cdots v_k + \cdots + \rho_k s_k s_k^T,$$
--
--   which is Nocedal's special update, formula (5). Here $\rho_j = 1/y_j^T s_j$ and $v_j = I - \rho_j y_j s_j^T$.
--
--   These are the matrices of the limited-memory BFGS method: only the last $m$ correction pairs are kept, and the matrix is rebuilt from $H_0$ each time. The module defines both the list form (`specialHList`) and the sequence form (`specialH`).
--
--   **Formalization Note** `specialHList H₀ pairs` folds the product-form BFGS step over the list, head first; `specialH H₀ m s y K` is `specialHList` of the pairs $j = K - \min(K,m), \dots, K-1$. $H_0$ is an arbitrary matrix here; positive definiteness is a hypothesis of the theorems that need it. The paper's $H_0$ is "positive definite and diagonal" on p. 774 (for storage) and "a given positive definite matrix" on p. 775, where these matrices are defined; diagonality is not imposed.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 775, eqs. (4)–(5) ('special BFGS matrices')

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_bfgsStep

open Matrix

namespace LimitedBFGS.SQN

/-- `H₀` updated by the BFGS product form (3) once for each pair `(s, y)` of the list, oldest
(head) first: `specialHList H₀ [(s₀,y₀), …, (s_k,y_k)]` is the right-hand side of (4)
(Nocedal 1980, p. 775). -/
noncomputable def specialHList {n : ℕ} (H₀ : Matrix (Fin n) (Fin n) ℝ)
    (pairs : List ((Fin n → ℝ) × (Fin n → ℝ))) : Matrix (Fin n) (Fin n) ℝ :=
  pairs.foldl (fun H p => bfgsStep H p.1 p.2) H₀

/-- The special BFGS matrix `H_K` of (4)–(5) (Nocedal 1980, p. 775) built from the sequences
`s, y : ℕ → ℝⁿ` with at most `m` stored corrections: `H₀` updated by the pairs
`(s_j, y_j)`, `j = K − min(K, m), …, K − 1`, oldest first. For `K = k + 1 ≤ m` these are
`j = 0, …, k` (formula (4)); for `K = k + 1 > m` they are `j = k − m + 1, …, k` (formula (5)). -/
noncomputable def specialH {n : ℕ} (H₀ : Matrix (Fin n) (Fin n) ℝ) (m : ℕ)
    (s y : ℕ → Fin n → ℝ) (K : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  specialHList H₀
    ((List.range (min K m)).map fun i => (s (K - min K m + i), y (K - min K m + i)))

end LimitedBFGS.SQN


