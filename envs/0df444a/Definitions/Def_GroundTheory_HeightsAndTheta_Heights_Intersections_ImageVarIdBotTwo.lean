-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImageVarIdBotTwo
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImageVarIdBotTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:34.602645+00:00
-- url     : https://prove2.me/theorems/7eef6b63-adf3-4d15-86c2-345d1365769b
-- title:
--   Image Var Id Bot Two
-- statement:
--   Definitions and structural lemmas for Image Var Id Bot Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImageVarIdBotTwo.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalSpanTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_Inhabit
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
def VerticalDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) [Fact p.Prime] (W' : Ideal (MRing ι')) (n : ℕ)
    (i' : ∀ k', ι' k'),
    IsBlockMap κ v → ((p : ℕ) : MRing ι') ∈ W' →
    IsProjVarF (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) n →
    IsProjVarF (imageVar (ZMod p) v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) n →
    IsChart (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' →
    ∀ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
      (fnDeg v (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) i' : ℤ) = J' (fibreIdeal κ G') 0 Fin.elim0
section Inhabitants
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


