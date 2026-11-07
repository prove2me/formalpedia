-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:47:11.576976+00:00
-- url     : https://prove2.me/theorems/eb70192c-e09c-4fcd-a3a4-e4bc4cdfe947
-- title:
--   Index Representation
-- statement:
--   Definitions and structural lemmas for Index Representation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicBMatrix_det
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_baseScalar
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_mul_indexConstantGL
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_div_one_add
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_one_add_ne_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexRatioUnit_orderOf
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
noncomputable def indexBMatrix
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (ResidueField P r level) :=
  cyclicBMatrix r (indexPlaceY P r level)
theorem indexBMatrix_eq_one_sub_indexCyclicGenerator_inv
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexBMatrix P r level =
      1 - ((indexCyclicGeneratorGL P r level)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (ResidueField P r level)) := by
  cases r <;> rfl
theorem indexBMatrix_det
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.det (indexBMatrix P r level) =
      (indexRatioUnit P r level : ResidueField P r level) := by
  rw [indexBMatrix,
    cyclicBMatrix_det r (indexPlaceY P r level)
      (indexPlaceY_one_add_ne_zero P r level),
    indexPlaceY_div_one_add]
theorem indexBMatrix_isUnit
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsUnit (indexBMatrix P r level) := by
  rw [Matrix.isUnit_iff_isUnit_det, indexBMatrix_det]
  exact (indexRatioUnit P r level).isUnit
noncomputable def indexBGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  (indexBMatrix_isUnit P r level).unit
@[simp] theorem indexBGL_coe
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexBGL P r level :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) =
      indexBMatrix P r level :=
  IsUnit.unit_spec (indexBMatrix_isUnit P r level)
theorem indexBGL_det
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup.det (indexBGL P r level) =
      indexRatioUnit P r level := by
  apply Units.ext
  change Matrix.det (indexBMatrix P r level) =
    (indexRatioUnit P r level : ResidueField P r level)
  exact indexBMatrix_det P r level
theorem indexCyclicGeneratorGL_commute_indexBGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexCyclicGeneratorGL P r level * indexBGL P r level =
      indexBGL P r level * indexCyclicGeneratorGL P r level := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, indexCyclicGeneratorGL_coe,
    indexBGL_coe, indexBMatrix_eq_one_sub_indexCyclicGenerator_inv,
    mul_sub, sub_mul, mul_one, one_mul]
  have hzRight :
      indexCyclicGeneratorMatrix P r level *
          ((indexCyclicGeneratorGL P r level)⁻¹ :
            Matrix.GeneralLinearGroup (Fin r.matrixRank)
              (ResidueField P r level)) = 1 := by
    simpa only [← indexCyclicGeneratorGL_coe,
      Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_one] using congrArg Units.val
        (mul_inv_cancel (indexCyclicGeneratorGL P r level))
  have hzLeft :
      ((indexCyclicGeneratorGL P r level)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ResidueField P r level)) *
        indexCyclicGeneratorMatrix P r level = 1 := by
    simpa only [← indexCyclicGeneratorGL_coe,
      Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_one] using congrArg Units.val
        (inv_mul_cancel (indexCyclicGeneratorGL P r level))
  rw [hzRight, hzLeft]
noncomputable def indexB
    (P : BasePrime) (r : Rank) (level : Nat) : PGL P r level :=
  Matrix.ProjGenLinGroup.mk (indexBGL P r level)
theorem residueProjectiveDetClass_indexB
    (P : BasePrime) (r : Rank) (level : Nat) :
    residueProjectiveDetClass P r level (indexB P r level) =
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) := by
  rw [indexB, residueProjectiveDetClass]
  change QuotientGroup.mk' _
      (Matrix.GeneralLinearGroup.det (indexBGL P r level)) = _
  rw [indexBGL_det]
  rfl
noncomputable def indexCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.GeneralLinearGroup (Fin r.matrixRank)
      (ResidueField P r level) :=
  indexConstantGL P r level u * indexBGL P r level *
    (indexConstantGL P r level u)⁻¹
theorem indexCartwrightStegerGeneratorGL_eq
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    indexCartwrightStegerGeneratorGL P r level u =
      indexConstantGL P r level u * indexBGL P r level *
        indexConstantGL P r level u⁻¹ := by
  rw [indexCartwrightStegerGeneratorGL]
  have hinv :
      (indexConstantGL P r level u)⁻¹ =
        indexConstantGL P r level u⁻¹ := by
    change (Units.map
      (indexConstantMatrixEmbedding P r level).toMonoidHom u)⁻¹ =
      Units.map (indexConstantMatrixEmbedding P r level).toMonoidHom u⁻¹
    exact (map_inv (Units.map
      (indexConstantMatrixEmbedding P r level).toMonoidHom) u).symm
  rw [hinv]
theorem indexConstantGL_conj_indexCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (a u : (ConstantExtension P r)ˣ) :
    indexConstantGL P r level a *
        indexCartwrightStegerGeneratorGL P r level u *
          (indexConstantGL P r level a)⁻¹ =
      indexCartwrightStegerGeneratorGL P r level (a * u) := by
  rw [indexCartwrightStegerGeneratorGL_eq,
    indexCartwrightStegerGeneratorGL_eq]
  change
    indexConstantGLHom P r level a *
        (indexConstantGLHom P r level u * indexBGL P r level *
          indexConstantGLHom P r level u⁻¹) *
        (indexConstantGLHom P r level a)⁻¹ =
      indexConstantGLHom P r level (a * u) * indexBGL P r level *
        indexConstantGLHom P r level (a * u)⁻¹
  simp only [map_mul, map_inv]
  group
theorem indexCyclicGeneratorGL_conj_indexCartwrightStegerGeneratorGL
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    indexCyclicGeneratorGL P r level *
        indexCartwrightStegerGeneratorGL P r level u *
          (indexCyclicGeneratorGL P r level)⁻¹ =
      indexCartwrightStegerGeneratorGL P r level
        (indexConstantFrobeniusUnit P r u) := by
  let z := indexCyclicGeneratorGL P r level
  let C := indexConstantGLHom P r level
  let φ := indexConstantFrobeniusUnit P r
  have hconstant (w : (ConstantExtension P r)ˣ) :
      z * C w * z⁻¹ = C (φ w) := by
    change
      indexCyclicGeneratorGL P r level * indexConstantGL P r level w *
          (indexCyclicGeneratorGL P r level)⁻¹ =
        indexConstantGL P r level (indexConstantFrobeniusUnit P r w)
    rw [indexCyclicGeneratorGL_mul_indexConstantGL]
    group
  have hb : z * indexBGL P r level * z⁻¹ =
      indexBGL P r level := by
    dsimp [z]
    rw [indexCyclicGeneratorGL_commute_indexBGL]
    group
  rw [indexCartwrightStegerGeneratorGL_eq,
    indexCartwrightStegerGeneratorGL_eq]
  change z * (C u * indexBGL P r level * C u⁻¹) * z⁻¹ =
    C (φ u) * indexBGL P r level * C (φ u)⁻¹
  calc
    z * (C u * indexBGL P r level * C u⁻¹) * z⁻¹ =
        (z * C u * z⁻¹) *
          (z * indexBGL P r level * z⁻¹) *
            (z * C u⁻¹ * z⁻¹) := by group
    _ = C (φ u) * indexBGL P r level * C (φ u⁻¹) := by
      rw [hconstant, hb, hconstant]
    _ = C (φ u) * indexBGL P r level * C (φ u)⁻¹ := by
      rw [map_inv, map_inv]
def generatorFirstIndex (r : Rank) : Fin r.matrixRank :=
  ⟨0, by cases r <;> decide⟩
def generatorSecondIndex (r : Rank) : Fin r.matrixRank :=
  ⟨1, by cases r <;> decide⟩
noncomputable def indexCartwrightStegerGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) : PGL P r level :=
  Matrix.ProjGenLinGroup.mk
    (indexCartwrightStegerGeneratorGL P r level u)
theorem indexCartwrightStegerGenerator_eq_conj
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    indexCartwrightStegerGenerator P r level u =
      Matrix.ProjGenLinGroup.mk (indexConstantGL P r level u) *
        indexB P r level *
          (Matrix.ProjGenLinGroup.mk
            (indexConstantGL P r level u))⁻¹ := by
  simp [indexCartwrightStegerGenerator,
    indexCartwrightStegerGeneratorGL, indexB, map_mul, map_inv]
noncomputable def indexConstantPGLHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    (ConstantExtension P r)ˣ →* PGL P r level :=
  Matrix.ProjGenLinGroup.mk.comp (indexConstantGLHom P r level)
@[simp] theorem indexConstantPGLHom_baseScalar
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : (BaseField P)ˣ) :
    indexConstantPGLHom P r level (baseScalarUnitHom P r a) = 1 := by
  change Matrix.ProjGenLinGroup.mk
      (indexConstantGL P r level (baseScalarUnitHom P r a)) = 1
  rw [indexConstantGL_baseScalar, Matrix.ProjGenLinGroup.mk_scalar]
theorem indexConstantPGL_conj_indexCartwrightStegerGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (a u : (ConstantExtension P r)ˣ) :
    indexConstantPGLHom P r level a *
        indexCartwrightStegerGenerator P r level u *
          (indexConstantPGLHom P r level a)⁻¹ =
      indexCartwrightStegerGenerator P r level (a * u) := by
  exact congrArg Matrix.ProjGenLinGroup.mk
      (indexConstantGL_conj_indexCartwrightStegerGeneratorGL
        P r level a u)
theorem indexCyclicGeneratorPGL_conj_indexCartwrightStegerGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    Matrix.ProjGenLinGroup.mk (indexCyclicGeneratorGL P r level) *
        indexCartwrightStegerGenerator P r level u *
          (Matrix.ProjGenLinGroup.mk
            (indexCyclicGeneratorGL P r level))⁻¹ =
      indexCartwrightStegerGenerator P r level
        (indexConstantFrobeniusUnit P r u) := by
  simpa [indexCartwrightStegerGenerator, map_mul, map_inv] using
    congrArg Matrix.ProjGenLinGroup.mk
      (indexCyclicGeneratorGL_conj_indexCartwrightStegerGeneratorGL
        P r level u)
theorem indexCartwrightStegerGenerator_eq_of_quotientMk_eq
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : (ConstantExtension P r)ˣ)
    (hquotient :
      (QuotientGroup.mk u : ConstantProjectiveClass P r) =
        QuotientGroup.mk v) :
    indexCartwrightStegerGenerator P r level u =
      indexCartwrightStegerGenerator P r level v := by
  have hdiv : u / v ∈ baseScalarUnits P r :=
    QuotientGroup.eq_iff_div_mem.mp hquotient
  obtain ⟨a, ha⟩ := hdiv
  have hconstantDiv :
      indexConstantPGLHom P r level (u / v) = 1 := by
    rw [← ha, indexConstantPGLHom_baseScalar]
  have hconstant :
      indexConstantPGLHom P r level u =
        indexConstantPGLHom P r level v := by
    apply div_eq_one.mp
    simpa [map_div] using hconstantDiv
  have hconstant' :
      Matrix.ProjGenLinGroup.mk (indexConstantGL P r level u) =
        Matrix.ProjGenLinGroup.mk (indexConstantGL P r level v) := by
    simpa [indexConstantPGLHom, indexConstantGL] using hconstant
  rw [indexCartwrightStegerGenerator_eq_conj,
    indexCartwrightStegerGenerator_eq_conj, hconstant']
theorem residueProjectiveDetClass_indexCartwrightStegerGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    residueProjectiveDetClass P r level
        (indexCartwrightStegerGenerator P r level u) =
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) := by
  rw [indexCartwrightStegerGenerator_eq_conj, map_mul, map_mul, map_inv,
    residueProjectiveDetClass_indexB]
  rw [mul_comm _
    (QuotientGroup.mk (indexRatioUnit P r level) :
      ResiduePowerClass P r level),
    mul_assoc, mul_inv_cancel, mul_one]
noncomputable def indexCartwrightStegerClassGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) : PGL P r level :=
  indexCartwrightStegerGenerator P r level
    (constantClassRepresentative P r u)
theorem residueProjectiveDetClass_indexCartwrightStegerClassGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    residueProjectiveDetClass P r level
        (indexCartwrightStegerClassGenerator P r level u) =
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) := by
  exact residueProjectiveDetClass_indexCartwrightStegerGenerator
    P r level (constantClassRepresentative P r u)
noncomputable def IndexCartwrightStegerImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  Subgroup.closure
    (Set.range (indexCartwrightStegerClassGenerator P r level))
noncomputable def IndexCartwrightStegerUnitImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  Subgroup.closure
    (Set.range (indexCartwrightStegerGenerator P r level))
theorem indexCartwrightStegerUnitGenerator_mem_unitImage
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    indexCartwrightStegerGenerator P r level u ∈
      IndexCartwrightStegerUnitImage P r level :=
  Subgroup.subset_closure ⟨u, rfl⟩
theorem IndexCartwrightStegerImage_le_unitImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerImage P r level ≤
      IndexCartwrightStegerUnitImage P r level := by
  rw [IndexCartwrightStegerImage]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨u, rfl⟩
  exact indexCartwrightStegerUnitGenerator_mem_unitImage P r level
    (constantClassRepresentative P r u)
theorem indexCartwrightStegerUnitGenerator_eq_classGenerator
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : (ConstantExtension P r)ˣ) :
    indexCartwrightStegerGenerator P r level u =
      indexCartwrightStegerClassGenerator P r level
        (QuotientGroup.mk u) := by
  apply indexCartwrightStegerGenerator_eq_of_quotientMk_eq
  exact (QuotientGroup.out_eq'
    (QuotientGroup.mk u : ConstantProjectiveClass P r)).symm
theorem IndexCartwrightStegerUnitImage_le_image
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerUnitImage P r level ≤
      IndexCartwrightStegerImage P r level := by
  rw [IndexCartwrightStegerUnitImage]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨u, rfl⟩
  rw [indexCartwrightStegerUnitGenerator_eq_classGenerator]
  exact Subgroup.subset_closure ⟨QuotientGroup.mk u, rfl⟩
theorem IndexCartwrightStegerUnitImage_eq_image
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerUnitImage P r level =
      IndexCartwrightStegerImage P r level :=
  le_antisymm
    (IndexCartwrightStegerUnitImage_le_image P r level)
    (IndexCartwrightStegerImage_le_unitImage P r level)
theorem indexConstantPGL_mem_normalizer_unitImage
    (P : BasePrime) (r : Rank) (level : Nat)
    (a : (ConstantExtension P r)ˣ) :
    indexConstantPGLHom P r level a ∈
      Subgroup.normalizer
        (IndexCartwrightStegerUnitImage P r level : Set _) := by
  apply Subgroup.normalizer_le_normalizer_closure
    (Set.range (indexCartwrightStegerGenerator P r level))
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨u, rfl⟩ := hg
  exact ⟨a * u,
    indexConstantPGL_conj_indexCartwrightStegerGenerator
      P r level a u |>.symm⟩
theorem indexCyclicGeneratorPGL_mem_normalizer_unitImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.ProjGenLinGroup.mk (indexCyclicGeneratorGL P r level) ∈
      Subgroup.normalizer
        (IndexCartwrightStegerUnitImage P r level : Set _) := by
  apply Subgroup.normalizer_le_normalizer_closure
    (Set.range (indexCartwrightStegerGenerator P r level))
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨u, rfl⟩ := hg
  exact ⟨indexConstantFrobeniusUnit P r u,
    indexCyclicGeneratorPGL_conj_indexCartwrightStegerGenerator
      P r level u |>.symm⟩
noncomputable def IndexCartwrightStegerStabilizer
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  Subgroup.closure
    (Set.range (indexConstantPGLHom P r level) ∪
      {Matrix.ProjGenLinGroup.mk (indexCyclicGeneratorGL P r level)})
theorem IndexCartwrightStegerStabilizer_le_normalizer_unitImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerStabilizer P r level ≤
      Subgroup.normalizer
        (IndexCartwrightStegerUnitImage P r level : Set _) := by
  rw [IndexCartwrightStegerStabilizer]
  apply (Subgroup.closure_le _).mpr
  rintro g (hg | hg)
  · obtain ⟨a, rfl⟩ := hg
    exact indexConstantPGL_mem_normalizer_unitImage P r level a
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact indexCyclicGeneratorPGL_mem_normalizer_unitImage P r level
noncomputable def IndexCartwrightStegerAmbient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (PGL P r level) :=
  IndexCartwrightStegerStabilizer P r level ⊔
    IndexCartwrightStegerUnitImage P r level
instance indexCartwrightStegerUnitImage_normal_in_ambient
    (P : BasePrime) (r : Rank) (level : Nat) :
    ((IndexCartwrightStegerUnitImage P r level).subgroupOf
      (IndexCartwrightStegerAmbient P r level)).Normal := by
  rw [IndexCartwrightStegerAmbient]
  exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
    (IndexCartwrightStegerStabilizer_le_normalizer_unitImage P r level)
instance indexCartwrightStegerImage_normal_in_ambient
    (P : BasePrime) (r : Rank) (level : Nat) :
    ((IndexCartwrightStegerImage P r level).subgroupOf
      (IndexCartwrightStegerAmbient P r level)).Normal := by
  rw [← IndexCartwrightStegerUnitImage_eq_image]
  infer_instance
theorem indexCartwrightStegerGenerator_mem_image
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    indexCartwrightStegerClassGenerator P r level u ∈
      IndexCartwrightStegerImage P r level :=
  Subgroup.subset_closure ⟨u, rfl⟩
theorem map_IndexCartwrightStegerImage_residueProjectiveDetClass
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexCartwrightStegerImage P r level).map
        (residueProjectiveDetClass P r level) =
      Subgroup.zpowers
        (QuotientGroup.mk (indexRatioUnit P r level) :
          ResiduePowerClass P r level) := by
  apply le_antisymm
  · rw [IndexCartwrightStegerImage,
      MonoidHom.map_closure]
    apply (Subgroup.closure_le _).2
    rintro q ⟨g, ⟨u, rfl⟩, rfl⟩
    rw [residueProjectiveDetClass_indexCartwrightStegerClassGenerator]
    exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_eq_closure]
    apply (Subgroup.closure_le _).2
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    exact ⟨indexCartwrightStegerClassGenerator P r level 1,
      indexCartwrightStegerGenerator_mem_image P r level 1,
      residueProjectiveDetClass_indexCartwrightStegerClassGenerator
        P r level 1⟩
theorem map_IndexCartwrightStegerImage_residueProjectiveDetClass_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexCartwrightStegerImage P r level).map
        (residueProjectiveDetClass P r level) = ⊤ := by
  rw [map_IndexCartwrightStegerImage_residueProjectiveDetClass]
  apply (Subgroup.card_eq_iff_eq_top
    (Subgroup.zpowers
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level))).mp
  rw [Nat.card_zpowers, indexRatioUnit_orderOf,
    IndexSelection.natCard_powerClass]
  simp only [Fintype.card_fin]
noncomputable def indexImageDetClassHom
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerImage P r level →*
      ResiduePowerClass P r level :=
  (residueProjectiveDetClass P r level).comp
    (IndexCartwrightStegerImage P r level).subtype
theorem indexImageDetClassHom_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexImageDetClassHom P r level) := by
  intro q
  have hq : q ∈ (IndexCartwrightStegerImage P r level).map
      (residueProjectiveDetClass P r level) := by
    rw [map_IndexCartwrightStegerImage_residueProjectiveDetClass_eq_top]
    exact Subgroup.mem_top q
  obtain ⟨g, hg, hqg⟩ := hq
  exact ⟨⟨g, hg⟩, hqg⟩
noncomputable def IndexCartwrightStegerColorZero
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup (IndexCartwrightStegerImage P r level) :=
  (indexImageDetClassHom P r level).ker
noncomputable instance indexCartwrightStegerColorZeroNormal
    (P : BasePrime) (r : Rank) (level : Nat) :
    (IndexCartwrightStegerColorZero P r level).Normal := by
  dsimp [IndexCartwrightStegerColorZero]
  infer_instance
noncomputable def indexColorQuotientEquiv
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerImage P r level ⧸
        IndexCartwrightStegerColorZero P r level ≃*
      ResiduePowerClass P r level :=
  QuotientGroup.quotientKerEquivOfSurjective
    (indexImageDetClassHom P r level)
    (indexImageDetClassHom_surjective P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


