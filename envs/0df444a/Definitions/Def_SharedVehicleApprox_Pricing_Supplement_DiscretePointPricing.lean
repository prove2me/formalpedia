-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Supplement_DiscretePointPricing
-- name    : SharedVehicleApprox_Pricing_Supplement_DiscretePointPricing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:43:13.792719+00:00
-- url     : https://prove2.me/theorems/d77476c8-3113-48c6-8b41-86eafeeede36
-- title:
--   App. C — discrete point policies and Algorithm 7 rounding
-- statement:
--   Algorithm 7 rounds the unrestricted point optimum $q'_i$ to the greatest available quantile not exceeding it. The predicate `IsAlg7Output` includes membership and maximality, so the set of candidates must be nonempty. A discrete point policy uses a grid quantile at every nonempty origin and encodes an empty origin by zero, as in §2.2. These definitions state the explicit refutation of Theorem 29.
-- source:
--   Banerjee, Freund & Lykouris, arXiv:1608.06819v4, pp. 37–38 (PDF 38–39), App. C and Algorithm 7

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_PointPricing

namespace SharedVehicleApprox.Pricing.Supplement

/-- Algorithm 7: round an unrestricted optimum down to the greatest available quantile.
`IsGreatest` includes membership, so the allowed set below `q' i` must be nonempty. -/
def IsAlg7Output {n : ℕ} (grid : Fin n → Finset ℝ) (q' qt : Fin n → ℝ) : Prop :=
  ∀ i, IsGreatest {v : ℝ | v ∈ grid i ∧ v ≤ q' i} (qt i)

/-- Discrete point policies still encode unavailability by zero at empty origins. -/
def IsDiscretePointPolicy (n m : ℕ) (grid : Fin n → Finset ℝ)
    (q : (Fin n → ℕ) → Fin n → ℝ) : Prop :=
  IsPolicy n m (pointPolicy q) ∧
    ∀ x ∈ QueueingFundamentals.Networks.states n m, ∀ i, 0 < x i → q x i ∈ grid i

end SharedVehicleApprox.Pricing.Supplement


