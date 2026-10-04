-- Prove2me | Definitions.Def_RegretBandits_Contextual_Exp4
-- name    : RegretBandits_Contextual_Exp4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:10:12.201507+00:00
-- url     : https://prove2.me/theorems/8a4cc44d-a24f-4a6f-8d5d-05239614c56d
-- title:
--   Exp4 without mixing (Fig. 4.1) with adaptive expert advice
-- statement:
--   Bandits with expert advice (Section 4.2 of Bubeck and Cesa-Bianchi). At each round $t$ each of $N$ experts $j$ provides a probability distribution $\xi^j_t$ over the $K$ arms; the advice may depend on the realization of the forecaster's past plays.
--
--   **Exp4 without mixing** (Fig. 4.1), with a sequence of learning rates $(\eta_t)$, keeps a distribution $q_t$ over experts, $q_1$ uniform, and at round $t$:
--
--   1. draws $I_t$ from $p_{i,t} = \mathbb E_{j\sim q_t} \xi^j_{i,t} = \sum_j q_{j,t}\,\xi^j_{i,t}$;
--   2. computes the arm-loss estimates $\widetilde\ell_{i,t} = \frac{\ell_{i,t}}{p_{i,t}}\mathbb 1_{I_t = i}$ and the expert-loss estimates $\widetilde y_{j,t} = \mathbb E_{i\sim\xi^j_t}\widetilde\ell_{i,t}$;
--   3. updates $\widetilde Y_{j,t} = \sum_{s=1}^t \widetilde y_{j,s}$ and
--   $$q_{j,t+1} = \frac{\exp(-\eta_t \widetilde Y_{j,t})}{\sum_{k=1}^N \exp(-\eta_t \widetilde Y_{k,t})} .$$
--
--   **Formalization Note** Rounds are numbered from $0$: Lean round $t$ is the book's round $t+1$ and uses $q$ computed from the estimates of rounds $0,\dots,t-1$ with rate `η t`, which is the book's $\eta_t$ applied to $\widetilde Y_t$. At $t = 0$ the estimates are zero, so $q$ is uniform whatever `η 0` is. Advice is a function of the round and the past plays.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 45-47, Section 4.2, Fig. 4.1

import Mathlib
import Definitions.Def_RegretBandits_Contextual_Protocol

namespace RegretBandits.Contextual

/-- Adaptive expert advice: `ξ t h j : Fin K → ℝ` is the distribution over arms recommended by
expert `j` at round `t` (0-based) when the forecaster's plays of rounds `0, …, t-1` were `h`. -/
abbrev AdaptiveAdvice (K N : ℕ) := (t : ℕ) → (Fin t → Fin K) → Fin N → Fin K → ℝ

/-- Estimated cumulative expert losses of Exp4 without mixing (Bubeck–Cesa-Bianchi,
arXiv:1204.5721v2, Fig. 4.1, p. 47), after the plays `h` of rounds `0, …, t-1`:
`Ỹ_{j,t} = ∑_{τ<t} ỹ_{j,τ}` with `ỹ_{j,τ} = ∑_i ξ^j_{i,τ} ℓ̃_{i,τ}`,
`ℓ̃_{i,τ} = ℓ_{i,τ}/p_{i,τ} · 1{I_τ = i}`, `p_{i,τ} = ∑_j q_{j,τ} ξ^j_{i,τ}` and
`q_τ = expWeights (η τ) Ỹ_τ`. -/
noncomputable def exp4CumLoss {K N : ℕ} (η : ℕ → ℝ) (ℓ : AdaptiveLosses K)
    (ξ : AdaptiveAdvice K N) : (t : ℕ) → (Fin t → Fin K) → Fin N → ℝ
  | 0, _ => fun _ => 0
  | t + 1, h => fun j =>
      let prev := exp4CumLoss η ℓ ξ t (Fin.init h)
      let q := expWeights (η t) prev
      let p : Fin K → ℝ := fun i => ∑ k, q k * ξ t (Fin.init h) k i
      let est : Fin K → ℝ := fun i =>
        if h (Fin.last t) = i then ℓ t (Fin.init h) i / p i else 0
      prev j + ∑ i, ξ t (Fin.init h) j i * est i

/-- The distribution `q_t` over experts maintained by Exp4 (Fig. 4.1, step (6)):
`q_{j,t} ∝ exp(-η_{t-1} Ỹ_{j,t-1})` in the book's 1-based indexing; here, 0-based,
`q t h = expWeights (η t) (Ỹ after rounds 0, …, t-1)`. At `t = 0` it is uniform. The sequence
`η : ℕ → ℝ` is the book's `(η_t)`; `η 0` is never effective. -/
noncomputable def exp4ExpertDist {K N : ℕ} (η : ℕ → ℝ) (ℓ : AdaptiveLosses K)
    (ξ : AdaptiveAdvice K N) (t : ℕ) (h : Fin t → Fin K) : Fin N → ℝ :=
  expWeights (η t) (exp4CumLoss η ℓ ξ t h)

/-- Exp4 without mixing (Fig. 4.1, step (2)): the arm at round `t` is drawn from
`p_{i,t} = E_{j∼q_t} ξ^j_{i,t} = ∑_j q_{j,t} ξ^j_{i,t}`. -/
noncomputable def exp4Rule {K N : ℕ} (η : ℕ → ℝ) (ℓ : AdaptiveLosses K)
    (ξ : AdaptiveAdvice K N) : PlayRule K :=
  fun t h i => ∑ j, exp4ExpertDist η ℓ ξ t h j * ξ t h j i

end RegretBandits.Contextual


