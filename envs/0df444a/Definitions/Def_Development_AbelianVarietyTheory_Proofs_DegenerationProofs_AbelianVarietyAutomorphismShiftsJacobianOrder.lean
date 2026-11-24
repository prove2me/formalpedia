-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyAutomorphismShiftsJacobianOrder
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyAutomorphismShiftsJacobianOrder
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T19:28:18.69684+00:00
-- url     : https://prove2.me/theorems/ce0ea148-f82c-4299-be53-c91acf9acd8f
-- title:
--   Abelian Variety Automorphism Shifts Jacobian Order
-- statement:
--   Definitions and structural lemmas for Abelian Variety Automorphism Shifts Jacobian Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AbelianVarietyAutomorphismShiftsJacobianOrder.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
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
noncomputable section
namespace GlobalTheory.SS.OrdTwist
variable {K : Type} [Field K] {A : Over (Sp K)} {I : Type} [Fintype I] [DecidableEq I]
abbrev rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom
def toDer (D : VF A) (V : A.left.Opens) :
    letI := (cstK A V).toAlgebra
    Derivation K Γ(A.left, V) Γ(A.left, V) :=
  letI := (cstK A V).toAlgebra
  Derivation.mk'
    { toFun := D.D V
      map_add' := map_add _
      map_smul' := fun c a => by
        show D.D V (cstK A V c * a) = cstK A V c * D.D V a
        rw [D.leibniz, D.const, mul_zero, add_zero] }
    (fun a b => D.leibniz V a b)
section Pull
variable {A' : Over (Sp K)} (g : A ⟶ A')
theorem app_rs {X Y : Scheme.{0}} (g : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) :
    (g.app V).hom (rs h a) = rs (g.preimage_mono h) ((g.app U).hom a) :=
  congr($(g.naturality (homOfLE h).op) a)
theorem app_cstK (V : A'.left.Opens) (c : K) : (g.left.app V).hom (cstK A' V c) = cstK A _ c := by
  have h : A'.hom.appLE ⊤ V le_top ≫ g.left.app V = A.hom.appLE ⊤ (g.left ⁻¹ᵁ V) le_top := by
    rw [Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE g.left A'.hom ⊤ V _ le_top le_rfl).trans ?_
    simp only [Over.w g]
  exact congr($h ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c))
variable [IsIso g.left]
def appE (V : A'.left.Opens) : Γ(A'.left, V) ≃+* Γ(A.left, g.left ⁻¹ᵁ V) :=
  (asIso (g.left.app V)).commRingCatIsoToRingEquiv
theorem app_symm (V : A'.left.Opens) (a : Γ(A.left, g.left ⁻¹ᵁ V)) :
    (g.left.app V).hom ((appE g V).symm a) = a := (appE g V).apply_symm_apply a
def transport (D : VF A) : VF A' where
  D V := (appE g V).symm.toAddMonoidHom.comp ((D.D _).comp (appE g V).toAddMonoidHom)
  leibniz V a b := by
    apply (appE g V).injective
    simp [D.leibniz]
  const V c := by
    show (appE g V).symm (D.D _ ((g.left.app V).hom (cstK A' V c))) = 0
    rw [app_cstK, D.const, map_zero]
  res U V h a := by
    apply (appE g V).injective
    show (g.left.app V).hom ((appE g V).symm (D.D _ ((g.left.app V).hom (rs h a)))) =
      (g.left.app V).hom (rs h ((appE g U).symm (D.D _ ((g.left.app U).hom a))))
    rw [app_symm, app_rs, app_rs, app_symm]
    exact D.res _ _ _ _
end Pull
def cstR {R : Type} [CommRing R] [Algebra R K] (M : Model R A) (U : M.Y.left.Opens) : R →+* Γ(M.Y.left, U) :=
  (M.Y.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
end GlobalTheory.SS.OrdTwist
end


