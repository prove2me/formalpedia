-- Prove2me | Definitions.Def_DoublyEffIP_expandedBatch
-- name    : DoublyEffIP_expandedBatch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:05.410027+00:00
-- url     : https://prove2.me/theorems/fe795a04-8e7d-4919-9a73-104c32e9361c
-- title:
--   The expanded batch $x^{\nwarrow}$ read from a matrix
-- statement:
--   From a $k\times(\lambda+1)$ matrix $M$ of configurations, the **expanded batch** is the batch of $k\lambda$ transition claims
--
--   $$
--   x^{\nwarrow}=\big((M[i,j],\,M[i,j+1])\big)_{i\in[k],\ j\in\{0,\dots,\lambda-1\}},
--   $$
--
--   the pairs of consecutive entries of each row. Applied to the true midpoint matrix it gives the paper's $x^{\nwarrow}$, a batch of claims of length $t/\lambda$; applied to the prover-defined matrix $M^*$ it gives $x^{\nwarrow*}$.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Table 1, p.20; p.25

import Mathlib

set_option autoImplicit false

namespace DoublyEffIP

/-- **The expanded batch read from a matrix** — `x^↖ = (x_{i,j})_{(i,j)∈[k]×[0,λ−1]}` (Table 1,
p.20) and "Let x^{↖*} be the instance of L^{k↖}_{t↖} read from M*" (p.25) in Chen–Hong–Kalai–Xi,
*Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799 (version of 2026-11-02,
sha256 14d170db…).

From a `k × (λ + 1)` matrix `M` of configurations, the batch of `kλ` transition claims
`(M[i, j], M[i, j+1])` for `i < k`, `j < λ`, each a claim of length `t/λ`.

**Formalization Note.** The `kλ` claims are indexed by `Fin k × Fin λ` (row, column), and the
claim at `(i, j)` is the pair of consecutive entries of row `i`, so that `x^↖` collects the
sub-transitions between the midpoints. -/
def expandedBatch {C : Type*} {k lam : ℕ} (M : Fin k → Fin (lam + 1) → C) :
    Fin k × Fin lam → C × C :=
  fun p => (M p.1 p.2.castSucc, M p.1 p.2.succ)

end DoublyEffIP


