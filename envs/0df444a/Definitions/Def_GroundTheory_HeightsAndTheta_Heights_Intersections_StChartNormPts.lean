-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartNormPts
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StChartNormPts
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:18.160193+00:00
-- url     : https://prove2.me/theorems/953231ac-2715-5025-a233-29f52ab9469c
-- title:
--   St Chart Norm Pts
-- statement:
--   Definitions and structural lemmas for St Chart Norm Pts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StChartNormPts.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreSide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
def ChartNormPts.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
    (G : GenFibre v P') (j : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsMultiHomogIdeal P' → (∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0) →
    ∀ z' : (Σ k', ι' k') → ℂ, (fun p => z' (v p)) ∈ mcPts (imageZ v P') →
      (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1) →
      (z' ∈ mcPts P' ↔ ∀ F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι),
        eval₂ ((algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom)
          (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) F = 0 →
        eval₂ (eval₂Hom (Int.castRingHom ℂ) fun p => z' (v p)) (fun q => z' ⟨q.1.1, q.2⟩) F = 0)
section Inhabitants
open IndefiniteRowSideFullHecke.Inter
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


