-- Prove2me | Definitions.Def_RegretBandits_Contextual_Exp3Sampled
-- name    : RegretBandits_Contextual_Exp3Sampled
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:10:20.49072+00:00
-- url     : https://prove2.me/theorems/72232125-0812-488a-b684-410094c60d3c
-- title:
--   Exp3 run on arms drawn from an external distribution (Theorem 4.3)
-- statement:
--   The setting of Theorem 4.3 of Bubeck and Cesa-Bianchi. The arm $I_t$ played at round $t$ is drawn from a distribution $q_t$ over the $K$ arms that may depend on the past; Exp3 without mixing is run alongside, but its own distribution $p_t$ is not used for drawing. Exp3 uses the estimates
--   $$\widetilde\ell_{i,t} = \frac{\ell_{i,t}}{q_{i,t}}\,\mathbb 1_{I_t = i},$$
--   their cumulative sums $\widetilde L_{i,t} = \sum_{s \le t}\widetilde\ell_{i,s}$, and a constant learning rate $\eta$:
--   $$p_{i,t+1} = \frac{\exp(-\eta \widetilde L_{i,t})}{\sum_{k=1}^K \exp(-\eta\widetilde L_{k,t})},\qquad p_1 \text{ uniform}.$$
--
--   **Formalization Note** Rounds are numbered from $0$; `exp3SampledDist η q ℓ t h` is the distribution Exp3 uses at Lean round $t$ (book's round $t+1$), computed from the plays $h$ of the earlier rounds. The sampling rule $q$ is a function of the round and the past plays.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 50, Theorem 4.3; Exp3 on p. 23

import Mathlib
import Definitions.Def_RegretBandits_Contextual_Protocol

namespace RegretBandits.Contextual

/-- Cumulative estimated losses of Exp3 without mixing when the played arms are drawn from an
external sampling rule `q` (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, Theorem 4.3, p. 50):
`L̃_{i,t} = ∑_{τ<t} ℓ̃_{i,τ}` with `ℓ̃_{i,τ} = ℓ_{i,τ}/q_{i,τ} · 1{I_τ = i}`,
after the plays `h` of rounds `0, …, t-1` (0-based). -/
noncomputable def exp3SampledCumLoss {K : ℕ} (q : PlayRule K) (ℓ : AdaptiveLosses K) :
    (t : ℕ) → (Fin t → Fin K) → Fin K → ℝ
  | 0, _ => fun _ => 0
  | t + 1, h => fun i =>
      exp3SampledCumLoss q ℓ t (Fin.init h) i +
        (if h (Fin.last t) = i then ℓ t (Fin.init h) i / q t (Fin.init h) i else 0)

/-- The distribution `p_t` computed by Exp3 without mixing with constant learning rate `η`
(Section 3.1, p. 23) from the estimates `ℓ̃_{i,τ} = ℓ_{i,τ}/q_{i,τ} · 1{I_τ = i}`:
`p_{i,t} ∝ exp(-η L̃_{i,t-1})` (book's 1-based indexing). The arms are *not* drawn from `p_t`
but from `q_t`. -/
noncomputable def exp3SampledDist {K : ℕ} (η : ℝ) (q : PlayRule K) (ℓ : AdaptiveLosses K)
    (t : ℕ) (h : Fin t → Fin K) : Fin K → ℝ :=
  expWeights η (exp3SampledCumLoss q ℓ t h)

end RegretBandits.Contextual


