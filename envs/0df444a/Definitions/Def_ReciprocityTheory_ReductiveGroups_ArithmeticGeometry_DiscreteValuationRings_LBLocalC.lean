-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:45.868021+00:00
-- url     : https://prove2.me/theorems/ffa9df47-c7e4-4efb-826c-fcc56238e647
-- title:
--   LBLocal C
-- statement:
--   Definitions and structural lemmas for LBLocal C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
def gw {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : K → L.ι) :
    Γ(Y, LB.wchart L ψ j ⊓ LB.wchart L ψ j')ˣ :=
  ∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L ψ j k)) (inf_le_right.trans (LB.wchart_le L ψ j' k)) :
      LB.wchart L ψ j ⊓ LB.wchart L ψ j' ≤ ψ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
    (pullU (ψ k) _ (L.g (j k) (j' k)))) ^ (ε k)
def IsGenW {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : ∀ j : K → L.ι, Γ(Y, LB.wchart L ψ j)ˣ) : Prop :=
  ∀ j j' : K → L.ι, res (inf_le_left : LB.wchart L ψ j ⊓ LB.wchart L ψ j' ≤ LB.wchart L ψ j) (s j) =
    gw L ψ ε j j' * res (inf_le_right : LB.wchart L ψ j ⊓ LB.wchart L ψ j' ≤ LB.wchart L ψ j') (s j')
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
end ReciprocityTheory.ChartRestriction.G.DVR


