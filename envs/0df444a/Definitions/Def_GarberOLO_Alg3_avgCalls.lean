-- Prove2me | Definitions.Def_GarberOLO_Alg3_avgCalls
-- name    : GarberOLO_Alg3_avgCalls
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:02:05.204998+00:00
-- url     : https://prove2.me/theorems/323b1843-c8cc-45b6-8b64-d5616cb85649
-- title:
--   Average number of oracle calls per round of Algorithm 3
-- statement:
--   Let $\mathrm{calls}_t$ be the number of calls to $\mathcal O_K$ made by the Algorithm 2 call of round $t$ of Algorithm 3. The **average number of oracle calls per iteration** over $T$ rounds is
--   $$\frac1T \sum_{t=1}^{T-1} \mathrm{calls}_t .$$
--
--   It is the quantity $K(\eta, \varepsilon)$ bounded in Theorem 1.
--
--   **Formalization Note** The sum runs over rounds $1, \dots, T-1$, as in the paper's proof (p. 15): the round-$T$ call only produces $s_{T+1}$, which is never played.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Theorem 1, p. 14; proof of Theorem 1, p. 15

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_alg3Call

namespace GarberOLO.Alg3

/-- **The average number of oracle calls per round of Algorithm 3** (Theorem 1, Reading 3).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Theorem 1, p. 14: "the average number of calls to the approximation oracle of K per
iteration"; proof of Theorem 1, p. 15: "K(η, ε) = O((1/T) Σ_{t=1}^{T−1} k_t d² ln((α+1)R/ε))".

`avgCalls … T = (1/T) Σ_{t=1}^{T−1} calls_t`, where `calls_t` is the number of calls to O_K made
by the Algorithm 2 call of round `t` (`(alg3Call … t).calls`).

**Formalization Note.** (Reading 3.) The sum runs over rounds 1, …, T − 1, as in the paper's
proof: the round-T call only produces s_{T+1}, which is never played. Each Ellipsoid iteration
makes exactly one call of Ô_K, which is one call of O_K. -/
noncomputable def avgCalls {d : ℕ} (S : Setting d)
    (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (sel : (N : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin N → EuclideanSpace ℝ (Fin d)) → Fin N → ℝ)
    (c : ℝ) (s₁ : EuclideanSpace ℝ (Fin d)) (η ε : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : ℝ :=
  (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 (T - 1), ((alg3Call S OK sel c s₁ η ε f t).calls : ℝ)

end GarberOLO.Alg3


