-- Prove2me | Definitions.Def_PriceCapacities_LowerBound_DualCost
-- name    : PriceCapacities_LowerBound_DualCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:22:18.299784+00:00
-- url     : https://prove2.me/theorems/74f84b3e-9f4f-4c70-922d-2709409f6a45
-- title:
--   Pointwise dual cost $f_{C,\beta}$ (eq. (1)) and the unconstrained cost $\mathrm{cost}_S(C)$
-- statement:
--   For a center tuple $C=(c_1,\dots,c_k)\in X^k$ and prices $\beta\in\mathbb R^k$, the **pointwise dual cost** is
--   $$f_{C,\beta}(x)=\min_{i\in[k]}\big\{d(x,c_i)^z+\beta_i\big\},$$
--   and for a weighted point set $W$, $f_{C,\beta}(W)=\sum_{x\in W}W(x)f_{C,\beta}(x)$. With zero prices this is the ordinary (**unconstrained**) clustering cost
--   $$\mathrm{cost}_S(C)=\sum_{x\in S}S(x)\min_{i\in[k]}d(x,c_i)^z .$$
--   These are the objects of eq. (1), Lemma 10.5 and §10.7.
--
--   **Formalization Note.** `pricedCost z C β x` is the infimum over `i : Fin k`, a minimum for $k\ge1$; for $k=0$ it is $0$ (an empty minimum, never used). $f_{C,\beta}(W)$ is `wsum W (pricedCost z C β)`; `unconstrainedCost z S C = wsum S (pricedCost z C 0)`.
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 5, eq. (1); p. 35 (f_{C,β} in §10.3); p. 40, §10.7 (cost_S(C))

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets

open scoped BigOperators NNReal

namespace PriceCapacities.LowerBound

/-!
# The pointwise dual cost `f_{C,β}` (eq. (1)) and the unconstrained clustering cost

Prabhu, Schwiegelshohn, Shyam, *The Price of Capacities for Clustering Coresets*, STOC 2027
submission (manuscript sha256 ec35f5ef…), p. 5, eq. (1); p. 35 (`f_{C,β}(y) = min_i {‖y − c_i‖^z +
β_i}`); p. 40, §10.7 (`cost_S(C)`).

* `pricedCost z C β x = f_{C,β}(x) = min_{i ∈ [k]} {d(x, c_i)^z + β_i}` (real exponent `z`).
  For `k ≥ 1` the infimum over the finite index set `Fin k` is a minimum; for `k = 0` it is `0`
  (an empty minimum, never used: every statement has `k ≥ 1`).
* `f_{C,β}(W)` is `wsum W (pricedCost z C β)`.
* `unconstrainedCost z S C = cost_S(C) = Σ_{x ∈ S} S(x) min_i d(x, c_i)^z`, the ordinary
  (unconstrained) `(k, z)`-clustering cost, i.e. `f_{C,0}(S)`.
-/

/-- The pointwise dual cost `f_{C,β}(x) = min_{i} {d(x, c_i)^z + β_i}`. -/
noncomputable def pricedCost {X : Type*} [PseudoMetricSpace X] {k : ℕ} (z : ℝ) (C : Fin k → X)
    (β : Fin k → ℝ) (x : X) : ℝ :=
  ⨅ i : Fin k, (dist x (C i) ^ z + β i)

/-- The unconstrained clustering cost `cost_S(C) = Σ_{x ∈ S} S(x) min_i d(x, c_i)^z`. -/
noncomputable def unconstrainedCost {X : Type*} [PseudoMetricSpace X] {k : ℕ} (z : ℝ) (S : WeightedSet X)
    (C : Fin k → X) : ℝ :=
  wsum S (pricedCost z C (fun _ => 0))

end PriceCapacities.LowerBound


