-- Prove2me | Definitions.Def_SambaPG_excursionTimes
-- name    : SambaPG_excursionTimes
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:55.705256+00:00
-- url     : https://prove2.me/theorems/b726c932-9bc1-438c-9da7-124b1069b8c4
-- title:
--   The stopping times $\tau^{(k)}$ and $\sigma^{(k)}$ of (11)
-- statement:
--   For a path $q(t)=q_{a^\star}(t)=1-p_{a^\star}(t)$, the times of (11) are $\tau^{(0)}=\sigma^{(0)}=0$ and, for $k\in\mathbb N$,
--
--   $$
--   \tau^{(k)}=\min\Big\{t\ge\sigma^{(k-1)}:q(t)<\tfrac12\Big\},\qquad \sigma^{(k)}=\min\Big\{t\ge\tau^{(k)}:q(t)\ge\tfrac12\Big\},
--   $$
--
--   each equal to $\infty$ when no such time exists. The intervals $[\tau^{(k)},\sigma^{(k)})$ are the periods in which the optimal arm has probability above $1/2$, and $[\sigma^{(k)},\tau^{(k+1)})$ the excursions in which it does not.
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, §4.2, p.9, eq. (11)

import Mathlib
import Definitions.Def_SambaPG_firstHitFrom

namespace SambaPG

/-- **The stopping times `τ^{(k)}`, `σ^{(k)}` of (11).**
Denisov & Walton, arXiv:2007.10229v3, §4.2, p.9, eq. (11): "`τ^{(0)} = 0`, `σ^{(0)} = 0`, and, for
`k ∈ ℕ`, `σ^{(k)} = min{t ≥ τ^{(k)} : q_{a⋆}(t) ≥ 1/2}`, `τ^{(k)} = min{t ≥ σ^{(k−1)} : q_{a⋆}(t) < 1/2}`.
If no such time exists for some `k` in (11) then we let `σ^{(k)} = ∞` (resp., `τ^{(k)} = ∞`)."

For a path `q : ℕ → ℝ` (the probability `q_{a⋆}(t) = 1 − p_{a⋆}(t)` of not playing the optimal arm),
`excursionTimes q k = (τ^{(k)}, σ^{(k)})`. -/
noncomputable def excursionTimes (q : ℕ → ℝ) : ℕ → ℕ∞ × ℕ∞
  | 0 => (0, 0)
  | k + 1 =>
      let τ := firstHitFrom (fun t => q t < 1 / 2) (excursionTimes q k).2
      (τ, firstHitFrom (fun t => 1 / 2 ≤ q t) τ)

/-- `σ^{(k)}` of (11). -/
noncomputable def sigmaExc (q : ℕ → ℝ) (k : ℕ) : ℕ∞ := (excursionTimes q k).2

/-- `τ^{(k)}` of (11). -/
noncomputable def tauExc (q : ℕ → ℝ) (k : ℕ) : ℕ∞ := (excursionTimes q k).1

end SambaPG


