-- Prove2me | Definitions.Def_HybridXorLift_weightedPotential
-- name    : HybridXorLift_weightedPotential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:20:36.091281+00:00
-- url     : https://prove2.me/theorems/36436ca6-1ed9-4c0a-b6d7-f2c102d430d2
-- title:
--   Weighted potential $F_{J,\xi}(h)$
-- statement:
--   For $J \subseteq [n]$ and $\xi \in \{0,1\}^J$, with $\theta_I(h) = \prod_{i \in I} \theta_i(h)$, the **weighted potential** is
--   $$
--   F_{J,\xi}(h) = \sum_{\varnothing \ne I \subseteq \bar J} \theta_I(h)\, \Phi^\xi_I(h).
--   $$
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §4.2, Eq. (4.10) and the display after it, p.16 (PDF p.18)

import Definitions.Def_HybridXorLift_theta
import Definitions.Def_HybridXorLift_phi

namespace HybridXorLift

/-- The weighted potential `F_{J,ξ}(h) = Σ_{∅ ≠ I ⊆ J̄} θ_I(h) Φ^ξ_I(h)` with
`θ_I(h) = ∏_{i∈I} θ_i(h)` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §4.2, Eq. (4.10) and the display after it, p.16 (PDF p.18)). -/
noncomputable def weightedPotential {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α)
    (q : ℕ) (J : Finset (Fin n)) (ξ : Fin n → Bool) (h : List (Step (Fin n × Fin r))) : ℝ :=
  ∑ I ∈ Jᶜ.powerset.filter (·.Nonempty), (∏ i ∈ I, theta A q h i) * phi A q I J ξ h

end HybridXorLift


