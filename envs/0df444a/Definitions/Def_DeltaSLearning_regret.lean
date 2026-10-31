-- Prove2me | Definitions.Def_DeltaSLearning_regret
-- name    : DeltaSLearning_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:10:17.487549+00:00
-- url     : https://prove2.me/theorems/12ea43f6-5c4b-4f29-bb4a-e8bf1b5d072a
-- title:
--   Regret $R_N$ over $N$ epochs
-- statement:
--   For the $(\delta,S)$ learning algorithm with parameters $J,(\eta^n),(\Delta^n)$ and initial targets $S^1$, the regret over $N$ epochs is
--   $$R_N := \mathbb E\Bigl[\sum_{t=1}^{T_N}\tilde C_t\Bigr]-V^*\,\mathbb E[T_N],$$
--   where $\tilde C_t$ is the pseudo cost (7) the algorithm incurs in period $t$, $T_N$ is the last period of epoch $N$, and $V^*$ is the optimal long-run average pseudo cost.
--
--   **Formalization Note** Definition 2 measures regret over $T$ periods against the clairvoyant optimal policy; Theorem 3 indexes regret by epochs, and the proof writes the benchmark as $TV^*$ (first line of (23)). Pseudo costs drop the term $p\,d_t$, which no policy affects; when $\mathbb E[D]<\infty$, Wald's identity makes the true-cost regret against $T_N(V^*+p\mathbb E[D])$ the same number, and the pseudo-cost form needs no moment of the demand.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Definition 2, p.8; eq. (23), p.19; Theorem 3, p.17

import Mathlib
import Definitions.Def_DeltaSLearning_algState__6eb4c5
import Definitions.Def_DeltaSLearning_optAvgCost

open MeasureTheory

namespace DeltaSLearning

/-- The regret over `N` epochs of the `(δ, S)` learning algorithm with parameters `J`, `η`, `Δ`
and initial targets `S₁`: `R_N := E[Σ_{t ≤ T_N} C̃_t] - V* E[T_N]`, where `C̃_t` is the pseudo
cost (7) the algorithm incurs in period `t` and `T_N` is the last period of epoch `N`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Definition 2,
p.8; first line of (23), p.19 ("−TV*"); Theorem 3, p.17.

**Formalization Note** Definition 2 measures regret over `T` periods against the clairvoyant
optimal policy; Theorem 3 indexes it by epochs. The benchmark is `T_N · V*` (the paper's (23)),
and costs are pseudo costs, which drop `p d_t`, a term no policy affects; with `E[D] < ∞` and
Wald's identity the true-cost regret is the same number. The initial order (`x¹ = 0`, order up to
`S¹` in period 1) is part of the incurred cost. -/
noncomputable def regret {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℕ → Ω → ℝ)
    (cp : Params) (J : ℕ) (η Δ : ℕ → ℝ) (S₁ : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∫ ω, (algState cp J η Δ S₁ (fun t => D t ω) N).cost ∂P)
    - optAvgCost P D cp * ∫ ω, ((algState cp J η Δ S₁ (fun t => D t ω) N).t : ℝ) ∂P

end DeltaSLearning


