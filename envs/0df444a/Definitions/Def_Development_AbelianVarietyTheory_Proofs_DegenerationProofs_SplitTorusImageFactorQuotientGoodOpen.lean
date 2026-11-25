-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusImageFactorQuotientGoodOpen
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusImageFactorQuotientGoodOpen
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T16:32:19.208594+00:00
-- url     : https://prove2.me/theorems/31ccc86c-520f-5568-b366-ef91db6418cd
-- title:
--   Split Torus Image Factor Quotient Good Open
-- statement:
--   Definitions and structural lemmas for Split Torus Image Factor Quotient Good Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusImageFactorQuotientGoodOpen.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSumsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Theorems.Thm_GlobalTheory_SplitTorus_charUnit_val
import Theorems.Thm_GlobalTheory_SplitTorus_val_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_charUnit_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.TorusImage
theorem appLE_res {Z Y : Scheme.{0}} (g : Z ⟶ Y) {U V : Y.Opens} (hV : V ≤ U) (h : ⊤ ≤ g ⁻¹ᵁ V) (h' : ⊤ ≤ g ⁻¹ᵁ U)
    (f : Γ(Y, U)) : (g.appLE V ⊤ h).hom ((Y.presheaf.map (homOfLE hV).op).hom f) = (g.appLE U ⊤ h').hom f := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
theorem appTop_charUnit {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) :
    t.left.appTop.hom (charUnit S X χ).val = SplitTorus.val t χ := by
  rw [SplitTorus.charUnit_val, SplitTorus.val_eq]
theorem wt_res {U V : G.left.Opens} (hV : V ≤ U) {u : Γ(G.left, U)} {χ : X} (h : Wt i U u χ) :
    Wt i V ((G.left.presheaf.map (homOfLE hV).op).hom u) χ := by
  intro Z t g h₁ h₂
  rw [appLE_res _ hV h₁ (h₁.trans fun _ hx => hV hx), appLE_res _ hV h₂ (h₂.trans fun _ hx => hV hx)]
  exact h Z t g _ _
theorem wt_one (U : G.left.Opens) : Wt i U 1 0 := by
  intro Z t g h₁ h₂
  rw [appTop_charUnit, SplitTorus.val_zero, map_one, map_one, _root_.mul_one]
theorem wt_mul {U : G.left.Opens} {u v : Γ(G.left, U)} {χ ψ : X} (h : Wt i U u χ) (h' : Wt i U v ψ) :
    Wt i U (u * v) (χ + ψ) := by
  intro Z t g h₁ h₂
  rw [map_mul, map_mul, h Z t g h₁ h₂, h' Z t g h₁ h₂, appTop_charUnit, appTop_charUnit, appTop_charUnit,
    SplitTorus.val_add]
  ring
theorem wt_inv {U : G.left.Opens} {u v : Γ(G.left, U)} (e : u * v = 1) {χ : X} (h : Wt i U u χ) :
    Wt i U v (-χ) := by
  intro Z t g h₁ h₂
  have a := h Z t g h₁ h₂
  have b := congrArg (((t ≫ i) * g).left.appLE U ⊤ h₁).hom e
  have c := congrArg (g.left.appLE U ⊤ h₂).hom e
  have d : SplitTorus.val t χ * SplitTorus.val t (-χ) = 1 := by
    rw [← SplitTorus.val_add, add_neg_cancel, SplitTorus.val_zero]
  rw [map_mul, map_one] at b c
  rw [appTop_charUnit] at a ⊢
  rw [a] at b
  linear_combination (SplitTorus.val t (-χ) * (g.left.appLE U ⊤ h₂).hom v) * b
    - (((t ≫ i) * g).left.appLE U ⊤ h₁).hom v * (SplitTorus.val t χ * SplitTorus.val t (-χ)) * c
    - (((t ≫ i) * g).left.appLE U ⊤ h₁).hom v * d
variable (i) in

def weights [IrreducibleSpace G.left] : AddSubgroup X where
  carrier := {χ | ∃ (U : G.left.Opens) (u : Γ(G.left, U)), (U : Set G.left).Nonempty ∧ IsUnit u ∧ Wt i U u χ}
  zero_mem' := ⟨⊤, 1, Set.univ_nonempty, isUnit_one, wt_one _⟩
  add_mem' := by
    rintro χ ψ ⟨U, u, hU, hu, h⟩ ⟨V, v, hV, hv, h'⟩
    exact ⟨U ⊓ V, _, nonempty_preirreducible_inter U.2 V.2 hU hV,
      (hu.map _).mul (hv.map _), wt_mul (wt_res inf_le_left h) (wt_res inf_le_right h')⟩
  neg_mem' := by
    rintro χ ⟨U, u, hU, hu, h⟩
    obtain ⟨v, e⟩ := hu.exists_right_inv
    exact ⟨U, v, hU, IsUnit.of_mul_eq_one_right u e, wt_inv e h⟩
end
end GlobalTheory.TorusImage


