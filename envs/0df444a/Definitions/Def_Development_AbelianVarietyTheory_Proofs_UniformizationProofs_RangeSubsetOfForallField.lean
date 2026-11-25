-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RangeSubsetOfForallField
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RangeSubsetOfForallField
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:39:20.883555+00:00
-- url     : https://prove2.me/theorems/24df7cb7-8b84-5110-915f-f1d9379b2801
-- title:
--   Range Subset Of Forall Field
-- statement:
--   Definitions and structural lemmas for Range Subset Of Forall Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RangeSubsetOfForallField.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonsingularIffNodal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.restrictPoints_val


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.NodalCubic
open GlobalTheory.WeierstrassCurve
noncomputable def evalAt {Z : Scheme.{0}} {k : Type} [CommRing k] (x : Spec (.of k) ⟶ Z) :
    Γ(Z, ⊤) →+* k := (x.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom
section Torus
variable {S : Scheme.{0}} {Z : Over S}
noncomputable def unitOf (t : Z ⟶ splitTorus S ℤ) : Γ(Z.left, ⊤)ˣ :=
  splitTorusPointsEquiv S ℤ Z t (Multiplicative.ofAdd 1)
noncomputable def valOf {k : Type} [CommRing k] {s : Spec (.of k) ⟶ S}
    (t : Over.mk s ⟶ splitTorus S ℤ) : kˣ :=
  Units.map (Scheme.ΓSpecIso (.of k)).hom.hom.toMonoidHom (unitOf t)
variable {k : Type} [CommRing k] {s : Spec (.of k) ⟶ S}
end Torus
def param {A : Type} [CommRing A] (u : A) : Fin 3 → A := ![u * (1 - u), u ^ 2, (1 - u) ^ 3]
abbrev node (K : Type) [CommRing K] : WeierstrassCurve K := ⟨1, 0, 0, 0, 0⟩
theorem node_map {K A : Type} [CommRing K] [CommRing A] (ρ : K →+* A) :
    (node K).map ρ = node A := by
  ext <;> simp
theorem isUnimodularSol_param {K A : Type} [CommRing K] [CommRing A] (ρ : K →+* A) (u : Aˣ) :
    IsUnimodularSol ((node K).map ρ) (param (u : A)) := by
  refine .of_isUnit ?_ 1 (u.isUnit.pow 2)
  rw [node_map, WeierstrassCurve.Projective.equation_iff]
  simp [param]
  ring
variable (K : Type) [Field K]
noncomputable def constHom (Z : Over (Spec (.of K))) : K →+* Γ(Z.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ Z.hom.appTop).hom
noncomputable def paramHom : (splitTorus (Spec (.of K)) ℤ).left ⟶ scheme (node K) :=
  (splitTorus (Spec (.of K)) ℤ).left.toSpecΓ ≫
    ptHom (node K) (constHom K _) (param (unitOf (𝟙 _)).val) (isUnimodularSol_param _ _)
variable {K}
section Locus
variable (U : (scheme (node K)).Opens)
  (hU : ∀ (k : Type) [Field k] (ρ : K →+* k) (P : Fin 3 → k)
    (h : IsUnimodularSol ((node K).map ρ) P),
    ⊤ ≤ ptHom (node K) ρ P h ⁻¹ᵁ U ↔ ((node K).map ρ).toProjective.Nonsingular P)
include hU
end Locus
end GlobalTheory.NodalCubic


