-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondGroupActionExplicitConstructorFacts20261017
-- name    : MazurTransfer_Order13ActualPicardGeometricDiamondGroupActionExplicitConstructorFacts20261017
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T20:19:21.303567+00:00
-- url     : https://prove2.me/theorems/e4391a25-f499-4473-a761-998af6a886f2
-- title:
--   The actual rational scheme diamond and original geometric arithmetic class homomorphism
-- statement:
--   Retain the existing generic-compatible rational diamond as an actual endomorphism of the same represented Picard scheme. For every perfect characteristic-zero field K and a two-affine cover of the literal curve over K, retain the original group homomorphism from its K-valued Picard points to the multiplicative form of the actual arithmetic Pic0 group. The original Poincare unit facts supply the identity constructor law. Both complete constructor values, both original unit-fact types, both scalar algebra providers and the original Picard group-object provider are compared. The named downstream consumer is the geometric cyclotomic and genuine nineteen-norm scheme identity. The two already accepted kernel and multiplication proofs needed by these constructor laws are retained with explicit local instance names. This is a constructor export of existing checked mathematics, with no additional owned theorem acceptance credit.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGeometricDiamondGroupAction.schemeDiamond and geometricClassHom constructors, with the two original unit structural facts from Order13ActualPicardGeometricArithmeticGroup. Official Anthropic FLT Poincare identity inputs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain the actual rational Picard diamond morphism and the
original multiplicative geometric arithmetic class homomorphism. Named
downstream consumer: geometric-point cyclotomic identities and genuine
nineteen-norm scheme morphisms. The two original Poincare unit structural
facts are explicit constructor inputs. Complete original MazurTheorem
constructors and unit proofs; official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticClassDataExplicitPublicConstructors20261017
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_eq_of_presentation
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricPointDegreeZeroPresentation_degreeZero_divisor_presentation
import Definitions.Def_MazurTransfer_PicardGeometricFieldPointDegreeZeroConditionData
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
import Theorems.Thm_MazurTransfer_FieldDivisorComparison_nonempty_iso_tensorUnit_of_principal_presentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticGroupData
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Theorems.Thm_MazurTransfer_FieldDivisorComparison_presentationTensorPrincipal_of_constantsAreBase
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open MazurTransfer.Order13GeometricRelativeCurveChange MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition MazurTransfer.LineBundleFieldComparison
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
namespace MazurTransfer.GeometricArithmeticKernelQuotientHelpers20261017
section QuotientComparison
variable {K : Type u} [Field K] {F : Type u} [Field F] [Algebra K F]
theorem pic_mk_eq_iff (D E : Divisor K F) :
    (QuotientAddGroup.mk D : Pic K F) = QuotientAddGroup.mk E ↔ Divisor.IsPrincipal (D - E) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, Divisor.mem_principal]
theorem pic0_mk_eq_iff (D E : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = Pic0.mk E ↔ (QuotientAddGroup.mk (D : Divisor K F) : Pic K F) = QuotientAddGroup.mk (E : Divisor K F) := by
  rw [pic_mk_eq_iff, Pic0.mk, Pic0.mk, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_sub, Divisor.mem_principal]
end QuotientComparison

end MazurTransfer.GeometricArithmeticKernelQuotientHelpers20261017
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance pairedKernelProvider120261017 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance pairedKernelProvider220261017 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance pairedKernelProvider320261017 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

theorem geometricKernelLineBundleInvertible20261017
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    Scheme.Modules.IsInvertible (actualGeometricPointLineBundle K a) :=
  geometricPointLineBundle_isInvertible (curveToBase ℚ) infinitySection actualPicard actualRepresentation
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (geometricCurveEmbedding K) a

theorem MazurTransfer.Order13ActualPicardGeometricArithmeticKernel.geometricArithmeticClass_eq_zero_iff_lineBundle_iso_unit
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    geometricArithmeticClass K 𝒱 a = 0 ↔
      Nonempty (actualGeometricPointLineBundle K a ≅ 𝟙_ (curveScheme K).Modules) := by
  letI : GeometricallyIntegral (curveToBase K) :=
    MazurTransfer.order13_actual_good_characteristic_geometric_integrality K Fact.out
  constructor
  · intro ha
    obtain ⟨E, φ, hp⟩ := MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 a
    have hmk : Pic0.mk E = Pic0.mk 0 := by
      rw [Pic0.mk_zero, geometricArithmeticClass_eq_of_presentation K 𝒱 a E φ hp, ha]
    have hP : Divisor.IsPrincipal E.1 := by
      have hp0 := (MazurTransfer.GeometricArithmeticKernelQuotientHelpers20261017.pic_mk_eq_iff E.1 0).mp ((MazurTransfer.GeometricArithmeticKernelQuotientHelpers20261017.pic0_mk_eq_iff E 0).mp hmk)
      simpa only [sub_zero] using hp0
    have hχ := geometricPointLineBundle_curveEulerChar_eq (curveToBase ℚ)
      infinitySection actualPicard actualRepresentation
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (curveToBase K) (geometricCurveEmbedding K)
      (geometricCurveEmbedding_snd K) a 𝒱
    exact MazurTransfer.FieldDivisorComparison.nonempty_iso_tensorUnit_of_principal_presentation
      (curveToBase K) 𝒱 (actualGeometricPointLineBundle K a)
      (geometricKernelLineBundleInvertible20261017 K a) hχ E.1 φ hp hP
  · rintro ⟨e⟩
    obtain ⟨φ, _, hnat, hsmul, hinj, hrange⟩ :=
      Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero (curveToBase K)
    have hp : IsPresentation (curveToBase K) (𝟙_ (curveScheme K).Modules) 0 φ :=
      ⟨hnat, hsmul, hinj, hrange⟩
    have hpN := hp.of_iso e
    have hz := geometricArithmeticClass_eq_of_presentation K 𝒱 a 0
      (fun U => (φ U).comp (Scheme.Modules.Hom.app e.hom U).hom) hpN
    exact hz.symm.trans Pic0.mk_zero


end
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open MazurTransfer.Order13ActualPicardGeometricArithmeticGroup
open MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition
open MazurTransfer.Order13GeometricRelativeCurveChange
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open scoped CategoryTheory.MonObj
namespace MazurTransfer.GeometricArithmeticGroupAdditionQuotientHelpers20261017
section QuotientComparison
variable {K : Type u} [Field K] {F : Type u} [Field F] [Algebra K F]
theorem pic_mk_eq_iff (D E : Divisor K F) :
    (QuotientAddGroup.mk D : Pic K F) = QuotientAddGroup.mk E ↔ Divisor.IsPrincipal (D - E) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, Divisor.mem_principal]
theorem pic0_mk_eq_iff (D E : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = Pic0.mk E ↔ (QuotientAddGroup.mk (D : Divisor K F) : Pic K F) = QuotientAddGroup.mk (E : Divisor K F) := by
  rw [pic_mk_eq_iff, Pic0.mk, Pic0.mk, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_sub, Divisor.mem_principal]
end QuotientComparison

end MazurTransfer.GeometricArithmeticGroupAdditionQuotientHelpers20261017
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance pairedMultiplicationProvider120261017 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance pairedMultiplicationProvider220261017 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance pairedMultiplicationProvider320261017 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)

theorem geometricGroupAdditionBundleInvertible20261017
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    Scheme.Modules.IsInvertible (actualGeometricPointLineBundle K a) :=
  geometricPointLineBundle_isInvertible (curveToBase ℚ) infinitySection actualPicard actualRepresentation
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (geometricCurveEmbedding K) a

theorem MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_mul :
    letI := (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
      (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
    ∀ a b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase,
      geometricArithmeticClassOver K 𝒱 (a * b) =
        geometricArithmeticClassOver K 𝒱 a + geometricArithmeticClassOver K 𝒱 b := by
  let hG : RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard := actualRepresentation
  letI := hG.grpObj
  intro a b
  let pa := pointOfOverHom K a
  let pb := pointOfOverHom K b
  let pab := pointOfOverHom K (a * b)
  obtain ⟨Ea, φa, ha⟩ :=
    MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 pa
  obtain ⟨Eb, φb, hb⟩ :=
    MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 pb
  obtain ⟨Eab, φab, hab⟩ :=
    MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 pab
  obtain ⟨i⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso hG a b
  let i' : actualGeometricPointLineBundle K pab ≅
      actualGeometricPointLineBundle K pa ⊗ actualGeometricPointLineBundle K pb :=
    (Scheme.Modules.pullback (geometricCurveEmbedding K)).mapIso i ≪≫
      Scheme.Modules.pullbackTensorObjIso (geometricCurveEmbedding K) _ _
  have hp := hab.of_iso i'.symm
  have hP := MazurTransfer.FieldDivisorComparison.presentationTensorPrincipal_of_constantsAreBase
    (curveToBase K) (actual_constantsAreBase_good_characteristic K)
    (actualGeometricPointLineBundle K pa) (actualGeometricPointLineBundle K pb)
    (geometricGroupAdditionBundleInvertible20261017 K pa)
    (geometricGroupAdditionBundleInvertible20261017 K pb)
    Ea.1 Eb.1 Eab.1 φa ha.nat ha.smul ha.inj ha.range φb hb.nat hb.smul hb.inj hb.range
    (fun U => (φab U).comp (Scheme.Modules.Hom.app i'.symm.hom U).hom)
    hp.nat hp.smul hp.inj hp.range
  have hcl : Pic0.mk Eab = Pic0.mk (Ea + Eb) :=
    (MazurTransfer.GeometricArithmeticGroupAdditionQuotientHelpers20261017.pic0_mk_eq_iff Eab (Ea + Eb)).mpr ((MazurTransfer.GeometricArithmeticGroupAdditionQuotientHelpers20261017.pic_mk_eq_iff _ _).mpr (by
      simpa only [AddSubgroup.coe_add, sub_add_eq_sub_sub] using hP))
  rw [Pic0.mk_add,
    geometricArithmeticClass_eq_of_presentation K 𝒱 pab Eab φab hab,
    geometricArithmeticClass_eq_of_presentation K 𝒱 pa Ea φa ha,
    geometricArithmeticClass_eq_of_presentation K 𝒱 pb Eb φb hb] at hcl
  exact hcl



end
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGenericFieldAction
open MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open MazurTransfer.Order13ActualPicardGeometricArithmeticGroup
open MazurTransfer.Order13GeometricRelativeCurveChange
open scoped CategoryTheory.MonObj
namespace MazurTransfer.GeometricDiamondGroupActionUnitHelpers20261017
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)

theorem geometricPointLineBundle_over_one_iso_unit :
    letI := (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
      (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
    Nonempty (actualGeometricPointLineBundle K (pointOfOverHom K 1) ≅
      𝟙_ (curveScheme K).Modules) := by
  let hG : RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard := actualRepresentation
  letI := hG.grpObj
  obtain ⟨i⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso hG
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))))
  exact ⟨(Scheme.Modules.pullback (geometricCurveEmbedding K)).mapIso i ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (geometricCurveEmbedding K)⟩

theorem geometricArithmeticClassOver_one :
    letI := (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
      (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
    geometricArithmeticClassOver K 𝒱 1 = 0 := by
  letI := (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
  exact (MazurTransfer.Order13ActualPicardGeometricArithmeticKernel.geometricArithmeticClass_eq_zero_iff_lineBundle_iso_unit K 𝒱 _).mpr
    (geometricPointLineBundle_over_one_iso_unit K)

end MazurTransfer.GeometricDiamondGroupActionUnitHelpers20261017
namespace MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local instance : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

def schemeDiamond : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase :=
  schemeHomOverToOverHom (actualFieldHom Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv)

variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)

def geometricClassHom :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase) →*
      Multiplicative (Pic0 K (actualCurveFunctionField K)) where
  toFun a := Multiplicative.ofAdd (geometricArithmeticClassOver K 𝒱 a)
  map_one' := MazurTransfer.GeometricDiamondGroupActionUnitHelpers20261017.geometricArithmeticClassOver_one K 𝒱
  map_mul' := geometricArithmeticClassOver_mul K 𝒱


end MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
#print axioms MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction.schemeDiamond
#print axioms MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction.geometricClassHom


