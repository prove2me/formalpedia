-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:49.418715+00:00
-- url     : https://prove2.me/theorems/8714f0e1-0387-4cda-9c70-ec40061659ad
-- title:
--   Exists Unique Sec Eq Mul Gen
-- statement:
--   Definitions and structural lemmas for Exists Unique Sec Eq Mul Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueSecEqMulGen.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.EvVal
def pullSec {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (ψ : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = ψ k)
    (le : ∀ j, LB.wchart L ψ j ≤ h ⁻¹ᵁ LB.wchart L φ j) (s : LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb L ψ ε) where
  f := fun j => (Y'.presheaf.map (homOfLE (le j)).op).hom ((h.app _).hom (s.f j))
  compat := fun (j j' : K → L.ι) => Geo.Tor.fn_ext fun y hy => by
    have v : ∀ j : K → L.ι, y ∈ LB.wchart L ψ j →
        Geo.Tor.gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE (le j)).op).hom ((h.app _).hom (s.f j))) =
        Geo.Tor.gs (𝟙 Y' ≫ h) y (LB.wchart L φ j) (s.f j) := fun j hj =>
      (Geo.Tor.gs_res _ y _ hj _).trans (Geo.Tor.gs_pull _ h y _ (le j hj) _)
    refine ((Geo.Tor.gs_res (𝟙 Y') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_
      ((Geo.Tor.gs_mul (𝟙 Y') y _ hy _ _).trans
      (congrArg₂ (· * ·) ((Geo.Tor.gs_unit (𝟙 Y') y _ hy _).trans
        (congrArg Units.val (Geo.Tor.gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2)))
        ((Geo.Tor.gs_res (𝟙 Y') y _ hy _).trans (v j' hy.2)))).symm)
    rw [Geo.Tor.sec_trans s (𝟙 Y' ≫ h) y (le j hy.1) (le j' hy.2)]
    simp only [Geo.Tor.trF, Category.assoc, e]
end GlobalTheory.EvVal


