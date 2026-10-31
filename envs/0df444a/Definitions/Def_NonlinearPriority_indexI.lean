-- Prove2me | Definitions.Def_NonlinearPriority_indexI
-- name    : NonlinearPriority_indexI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:30.062005+00:00
-- url     : https://prove2.me/theorems/338505eb-e9e5-43d5-a446-b9d6680a91b5
-- title:
--   The index $I(\pi_i)$ of Corollary A.1
-- statement:
--   For $i,j\in\{k,k+1\}$, $j\ne i$,
--   $$I(\pi_i)\equiv\frac{\delta^{\pi_i}_i\mu_i-\delta^{\pi_i}_j\mu_j}{\bar\rho_{k-1}-\rho_i},\qquad I(\bar\pi_k)\equiv0.$$
--   Corollary A.1 ranks the three policies $\pi_k,\pi_{k+1},\bar\pi_k$ by this index.
--
--   **Formalization Note** With 0-based types the paper's $\bar\rho_{k-1}$ is `rhoBar k`. $I(\bar\pi_k)=0$ is used directly in the statements.
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, Corollary A.1, p.18 (PDF 19)

import Mathlib
import Definitions.Def_NonlinearPriority_Params
import Definitions.Def_NonlinearPriority_delta

open MeasureTheory

namespace NonlinearPriority

variable {K : ℕ}

/-- **The index `I(π_i)` of Corollary A.1** (p. 18, PDF 19). Ouyang, Argon and Ziya, Management
Science (2021), doi:10.1287/mnsc.2020.3952:

`I(π̄k) ≡ 0` and `I(πi) ≡ (δ^{πi}_i μi − δ^{πi}_j μj)/(ρ̄_{k−1} − ρi)` for `i, j ∈ {k, k+1}`,
`j ≠ i`.

This is `I(π_i)` for the type `i` of the pair and the other type `j`; `I(π̄_k) = 0` is used
directly.

**Formalization Note.** With 0-based types the pair is `k, k+1` and the paper's `ρ̄_{k−1}` is
`rhoBar k = 1 − Σ_{j < k} ρⱼ` (sum over the types before the pair). -/
noncomputable def indexI (P : Params K) (C : Fin K → ℝ → ℝ)
    (w : (Fin K → ℕ) → Fin K → ProbabilityMeasure ℝ) (k : ℕ) (i j : Fin K) : ℝ :=
  (deltaBar C w k (prioPolicy k i) i * P.mu i - deltaBar C w k (prioPolicy k i) j * P.mu j) /
    (P.rhoBar k - P.rho i)

end NonlinearPriority


