-- Prove2me | Definitions.Def_GarberOLO_Alg3_alphaRegret
-- name    : GarberOLO_Alg3_alphaRegret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:49:18.124238+00:00
-- url     : https://prove2.me/theorems/8f06aedb-b8f6-4dcb-ae99-0197a3be4ba6
-- title:
--   The $\alpha$-regret (eq. (1))
-- statement:
--   For points $x_1, \dots, x_T$ and vectors $f_1, \dots, f_T$, the **α-regret** is
--   $$\alpha\text{-regret}(\{(x_t,f_t)\}_{t\in[T]}) = \begin{cases} \dfrac1T\sum_{t=1}^T x_t\cdot f_t - \alpha \min_{x\in K}\dfrac1T\sum_{t=1}^T x\cdot f_t & \alpha \ge 1,\\[2mm] \alpha \max_{x\in K}\dfrac1T\sum_{t=1}^T x\cdot f_t - \dfrac1T\sum_{t=1}^T x_t\cdot f_t & \alpha < 1.\end{cases}$$
--
--   It compares the player's average loss (payoff) with $\alpha$ times the best fixed action in hindsight, the benchmark achievable with an $\alpha$-approximation oracle.
--
--   **Formalization Note** Rounds are indexed $1, \dots, T$ (index $0$ is unused). The min and max are the infimum and supremum of the image of $K$, which are attained when $K$ is compact and nonempty.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, eq. (1), p. 4

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting

open scoped RealInnerProductSpace

namespace GarberOLO.Alg3

/-- **The α-regret** (eq. (1)).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, eq. (1), p. 4:
"α − regret({(x_t, f_t)}_{t∈[T]}) := (1/T) Σ_{t=1}^T x_t · f_t − α · min_{x∈K} (1/T) Σ_{t=1}^T x · f_t
if α ≥ 1; α · max_{x∈K} (1/T) Σ_{t=1}^T x · f_t − (1/T) Σ_{t=1}^T x_t · f_t if α < 1."

`alphaRegret S x f T` is this quantity for the points `x 1, …, x T` and the vectors
`f 1, …, f T` (rounds are numbered from 1; the values at index 0 and above T are not used).

**Formalization Note.** The min and max over K are `sInf`/`sSup` of the image of K under the
continuous map `z ↦ (1/T) Σ_t ⟪z, f t⟫`; for compact nonempty K (which holds whenever an oracle
exists) the image is compact and nonempty, so these are the attained minimum and maximum. The
paper divides by T; every theorem of the mission assumes `1 ≤ T`. -/
noncomputable def alphaRegret {d : ℕ} (S : Setting d)
    (x f : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : ℝ :=
  if 1 ≤ S.α then
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, ⟪x t, f t⟫ -
      S.α * sInf ((fun z => (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, ⟪z, f t⟫) '' S.K)
  else
    S.α * sSup ((fun z => (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, ⟪z, f t⟫) '' S.K) -
      (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, ⟪x t, f t⟫

end GarberOLO.Alg3


