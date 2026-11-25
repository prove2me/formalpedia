-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverPt
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverPt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:33.670727+00:00
-- url     : https://prove2.me/theorems/4aed4645-25e8-5da4-9763-1cbc602cdeb3
-- title:
--   Pts Over Pt
-- statement:
--   Definitions and structural lemmas for Pts Over Pt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PtsOverPt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOver
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
def ptsOverPt (P' : Ideal (MRing ι')) (v : (Σ k, ι k) → (Σ k', ι' k')) (z : (Σ k, ι k) → ℂ) :
    Set (Set ((Σ k', ι' k') → ℂ)) :=
  {O | ∃ z' ∈ mcPts P', O = {z'' | SameOrbit z'' z'} ∧ SameOrbit (fun p => z' (v p)) z}
end Over
def GenericPointsAvoidBadLocus.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (i : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    (∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0) →
    ∃ (D : MRing ι) (a : K → ℕ), IsMultiHomog D a ∧ D ∉ imageZ v P' ∧
      ∀ z ∈ mcPts (imageZ v P'), eval z (map (Int.castRingHom ℂ) D) ≠ 0 →
        (ptsOverPt P' v z).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
          (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩))
section Inhabitants
open IndefiniteRowSideFullHecke.Inter
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


