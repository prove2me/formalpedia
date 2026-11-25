-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverChart
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverChart
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:41.962078+00:00
-- url     : https://prove2.me/theorems/3b29c521-c7f9-4a16-abf3-63efea30347c
-- title:
--   Pts Over Chart
-- statement:
--   Definitions and structural lemmas for Pts Over Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PtsOverChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverPt
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
section Over
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
def ptsOverChart (P' : Ideal (MRing ι')) (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k'))
    (j : ∀ k : FibreBlock κ, ι' k.1) (z : (Σ k, ι k) → ℂ) : Set (Set ((Σ k', ι' k') → ℂ)) :=
  {O | ∃ z' ∈ mcPts P', O = {z'' | SameOrbit z'' z'} ∧ SameOrbit (fun p => z' (v p)) z ∧
    ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0}
end Over
def GenericPointsInAffineChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (j : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    (∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0) →
    ∃ (D : MRing ι) (a : K → ℕ), IsMultiHomog D a ∧ D ∉ imageZ v P' ∧
      ∀ z ∈ mcPts (imageZ v P'), eval z (map (Int.castRingHom ℂ) D) ≠ 0 →
        (ptsOverChart P' κ v j z).Finite ∧
        (ptsOverChart P' κ v j z).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
          (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩)) ∧
        ∀ z' ∈ mcPts P', SameOrbit (fun p => z' (v p)) z → (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0) →
          ∀ q : Σ k : FibreBlock κ, ι' k.1, G.x' ⟨q.1.1, q.2⟩ ≠ 0 → z' ⟨q.1.1, q.2⟩ ≠ 0
end GroundTheory.Heights₂.Heights.Inter


