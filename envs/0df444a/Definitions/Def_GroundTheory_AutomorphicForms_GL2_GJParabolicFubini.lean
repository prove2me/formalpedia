-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJParabolicFubini
-- name    : GroundTheory_AutomorphicForms_GL2_GJParabolicFubini
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:25.423719+00:00
-- url     : https://prove2.me/theorems/35e9c410-6a2a-5b9c-b92a-239272fab445
-- title:
--   GJParabolic Fubini
-- statement:
--   Definitions and structural lemmas for GJParabolic Fubini, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClosed_levi
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Measure Topology Set
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α]
variable (n) in

abbrev LeviIndex (β : Fin n → α) : Type := {ij : Fin n × Fin n // β ij.1 = β ij.2}
variable (F) in

def unipMatrix {β : Fin n → α} (u : UnipotentIndex n β → F) : Matrix (Fin n) (Fin n) F :=
  fun i j => if h : β i < β j then u ⟨(i, j), h⟩ else 0
theorem unipMatrix_apply_of_lt {β : Fin n → α} (u : UnipotentIndex n β → F) {i j : Fin n}
    (h : β i < β j) : unipMatrix F u i j = u ⟨(i, j), h⟩ := by
  simp [unipMatrix, h]
theorem unipMatrix_apply_of_not_lt {β : Fin n → α} (u : UnipotentIndex n β → F) {i j : Fin n}
    (h : ¬ β i < β j) : unipMatrix F u i j = 0 := by
  simp [unipMatrix, h]
section Chart
variable (F n) (β : Fin n → α)
def lieLevi : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {A | ∀ i j, β i ≠ β j → A i j = 0}
  add_mem' {A B} hA hB i j h := by simp [hA i j h, hB i j h]
  zero_mem' i j _ := rfl
  smul_mem' c A hA i j h := by simp [hA i j h]
variable {F n β} in

theorem mul_mem_lieLevi {A B : Matrix (Fin n) (Fin n) F} (hA : A ∈ lieLevi F n β)
    (hB : B ∈ lieLevi F n β) : A * B ∈ lieLevi F n β := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : β i = β k
  · rw [hB k j (fun e => h (hik.trans e)), mul_zero]
  · rw [hA i k hik, zero_mul]
def leviCoord : lieLevi F n β ≃ₗ[F] (LeviIndex n β → F) where
  toFun A s := (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
  invFun x := ⟨Matrix.of fun i j => if h : β i = β j then x ⟨(i, j), h⟩ else 0,
    fun i j hij => by simp [hij]⟩
  map_add' A B := rfl
  map_smul' c A := rfl
  left_inv A := by
    ext i j
    by_cases h : β i = β j
    · simp [h]
    · simp [h, A.2 i j h]
  right_inv x := by
    funext s
    simp [s.2]
@[simp] theorem leviCoord_apply (A : lieLevi F n β) (s : LeviIndex n β) :
    leviCoord F n β A s = (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 :=
  rfl
def leviCoordHomeomorph : lieLevi F n β ≃ₜ (LeviIndex n β → F) where
  toEquiv := (leviCoord F n β).toEquiv
  continuous_toFun := continuous_pi fun s =>
    (continuous_subtype_val.matrix_elem s.1.1 s.1.2 :
      Continuous fun A : lieLevi F n β => (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2)
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    by_cases h : β i = β j
    · simp only [Matrix.of_apply, h, dite_true]
      exact continuous_apply _
    · simp only [Matrix.of_apply, h, dite_false]
      exact continuous_const
def toLieLevi (m : levi F n β) : lieLevi F n β :=
  ⟨((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), fun i j h => mem_levi.1 m.2 i j h⟩
theorem isOpenEmbedding_toLieLevi : IsOpenEmbedding (toLieLevi F n β) := by
  have hemb : IsEmbedding (toLieLevi F n β) :=
    ((isOpenEmbedding_val F n).isEmbedding.comp IsEmbedding.subtypeVal).codRestrict
      (lieLevi F n β : Set (Matrix (Fin n) (Fin n) F)) fun m : levi F n β =>
        fun i j h => mem_levi.1 m.2 i j h
  refine ⟨hemb, ?_⟩
  have : Set.range (toLieLevi F n β) = Subtype.val ⁻¹' Set.range
      (Units.val : GL (Fin n) F → Matrix (Fin n) (Fin n) F) := by
    ext A
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, rfl⟩
    · rintro ⟨u, hu⟩
      refine ⟨⟨u, mem_levi.2 fun i j h => ?_⟩, Subtype.ext hu⟩
      rw [hu]
      exact A.2 i j h
  rw [this]
  exact (isOpenEmbedding_val F n).isOpen_range.preimage continuous_subtype_val
def mulLeftLieLevi (m : levi F n β) : lieLevi F n β ≃ₗ[F] lieLevi F n β :=
  (Units.mulLeftLinearEquiv F _ (m : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact mul_mem_lieLevi (fun i j h => mem_levi.1 m.2 i j h) hA
    · refine ⟨((m⁻¹ : levi F n β) : GL (Fin n) F) * A,
        mul_mem_lieLevi (fun i j h => mem_levi.1 (m⁻¹).2 i j h) hA, ?_⟩
      simp [← mul_assoc])
def mulRightLieLevi (m : levi F n β) : lieLevi F n β ≃ₗ[F] lieLevi F n β :=
  (Units.mulRightLinearEquiv F (m : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact mul_mem_lieLevi hA (fun i j h => mem_levi.1 m.2 i j h)
    · refine ⟨A * ((m⁻¹ : levi F n β) : GL (Fin n) F),
        mul_mem_lieLevi hA (fun i j h => mem_levi.1 (m⁻¹).2 i j h), ?_⟩
      simp [mul_assoc])
variable {F n}
def leviChart : LinearChart F (LeviIndex n β) (levi F n β) where
  toFun m := leviCoord F n β (toLieLevi F n β m)
  isOpenEmbedding :=
    (leviCoordHomeomorph F n β).isOpenEmbedding.comp (isOpenEmbedding_toLieLevi F n β)
  left m := (leviCoord F n β).symm.trans ((mulLeftLieLevi F n β m).trans (leviCoord F n β))
  right m := (leviCoord F n β).symm.trans ((mulRightLieLevi F n β m).trans (leviCoord F n β))
  toFun_mul_left g x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  toFun_mul_right h x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
variable {β}
@[simp] theorem leviChart_apply (m : levi F n β) (s : LeviIndex n β) :
    (leviChart β).toFun m s = ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 :=
  rfl
@[simp] theorem parabolicChart_apply (p : blockUpper F n β) (s : ParabolicIndex n β) :
    (parabolicChart F n β).toFun p s = ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 :=
  rfl
end Chart
section ParabolicMk
variable {β : Fin n → α}
theorem blockTriangular_add_unipMatrix (m : levi F n β) (u : UnipotentIndex n β → F) :
    (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u).BlockTriangular β := by
  intro i j hji
  rw [Matrix.add_apply, mem_levi.1 m.2 i j (ne_of_gt hji),
    unipMatrix_apply_of_not_lt u (not_lt.2 hji.le), add_zero]
theorem det_add_unipMatrix (m : levi F n β) (u : UnipotentIndex n β → F) :
    (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u).det =
      ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det := by
  classical
  have hm : ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular β :=
    fun i j h => mem_levi.1 m.2 i j (ne_of_gt h)
  rw [(blockTriangular_add_unipMatrix m u).det, hm.det]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  ext i j
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.add_apply]
  rw [unipMatrix_apply_of_not_lt u (by rw [i.2, j.2]; exact lt_irrefl _), add_zero]
theorem isUnit_add_unipMatrix (m : levi F n β) (u : UnipotentIndex n β → F) :
    IsUnit (((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_add_unipMatrix, ← Matrix.isUnit_iff_isUnit_det]
  exact (m : GL (Fin n) F).isUnit
variable (β) in

def parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) : blockUpper F n β :=
  ⟨(isUnit_add_unipMatrix m u).unit, by
    rw [mem_blockUpper, IsUnit.unit_spec]
    exact blockTriangular_add_unipMatrix m u⟩
theorem coe_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    (((parabolicMk β m u : blockUpper F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) + unipMatrix F u :=
  IsUnit.unit_spec _
theorem leviProj_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    leviProj F n β (parabolicMk β m u) = m := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [leviProj_apply, coe_parabolicMk]
  split_ifs with h
  · rw [Matrix.add_apply, unipMatrix_apply_of_not_lt u (by rw [h]; exact lt_irrefl _), add_zero]
  · exact (mem_levi.1 m.2 i j h).symm
def unipCoord (p : blockUpper F n β) : UnipotentIndex n β → F :=
  fun s => ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
theorem unipCoord_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    unipCoord (parabolicMk β m u) = u := by
  funext s
  rw [unipCoord, coe_parabolicMk, Matrix.add_apply, mem_levi.1 m.2 _ _ (ne_of_lt s.2),
    unipMatrix_apply_of_lt u s.2, zero_add]
theorem parabolicMk_leviProj_unipCoord (p : blockUpper F n β) :
    parabolicMk β (leviProj F n β p) (unipCoord p) = p := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [coe_parabolicMk, Matrix.add_apply, leviProj_apply]
  rcases lt_trichotomy (β i) (β j) with h | h | h
  · rw [if_neg (ne_of_lt h), unipMatrix_apply_of_lt _ h, zero_add]
    rfl
  · rw [if_pos h, unipMatrix_apply_of_not_lt _ (by rw [h]; exact lt_irrefl _), add_zero]
  · rw [if_neg (ne_of_gt h), unipMatrix_apply_of_not_lt _ (not_lt.2 h.le), add_zero]
    exact ((mem_blockUpper F n).1 p.2 h).symm
end ParabolicMk
section Ratio
instance locallyCompactSpace_levi_chart (β : Fin n → α) : LocallyCompactSpace (levi F n β) :=
  isClosed_levi.isClosedEmbedding_subtypeVal.locallyCompactSpace
variable (β : Fin n → α)
def leviRatio : levi F n β →* ℝ≥0 where
  toFun m := (leviChart β).leftModulus m / (parabolicChart F n β).leftModulus (leviIncl m)
  map_one' := by
    borelize F ↥(levi F n β) ↥(blockUpper F n β)
    rw [map_one, ← LinearChart.leftModulusHom_apply, ← LinearChart.leftModulusHom_apply, map_one,
      map_one, div_one]
  map_mul' m m' := by
    borelize F ↥(levi F n β) ↥(blockUpper F n β)
    rw [map_mul, LinearChart.leftModulus_mul, LinearChart.leftModulus_mul, div_mul_div_comm]
variable {β}
end Ratio
section Coordinates
variable (β : Fin n → α)
def coordAddEquiv : ((LeviIndex n β → F) × (UnipotentIndex n β → F)) ≃+ (ParabolicIndex n β → F) where
  toFun x s := if h : β s.1.1 = β s.1.2 then x.1 ⟨s.1, h⟩
    else x.2 ⟨s.1, lt_of_le_of_ne (not_lt.1 s.2) h⟩
  invFun y := (fun s => y ⟨s.1, not_lt.2 s.2.le⟩, fun s => y ⟨s.1, not_lt.2 s.2.le⟩)
  left_inv x := by
    ext s
    · simp [s.2]
    · simp [ne_of_lt s.2]
  right_inv y := by
    funext s
    by_cases h : β s.1.1 = β s.1.2 <;> simp [h]
  map_add' x y := by
    funext s
    by_cases h : β s.1.1 = β s.1.2 <;> simp [h]
theorem coordAddEquiv_apply (x : (LeviIndex n β → F) × (UnipotentIndex n β → F))
    (s : ParabolicIndex n β) :
    coordAddEquiv β x s = if h : β s.1.1 = β s.1.2 then x.1 ⟨s.1, h⟩
      else x.2 ⟨s.1, lt_of_le_of_ne (not_lt.1 s.2) h⟩ :=
  rfl
def coordEquiv : ((LeviIndex n β → F) × (UnipotentIndex n β → F)) ≃ₜ+ (ParabolicIndex n β → F) where
  toAddEquiv := coordAddEquiv β
  continuous_toFun := by
    refine continuous_pi fun s => ?_
    show Continuous fun x : (LeviIndex n β → F) × (UnipotentIndex n β → F) =>
      if h : β s.1.1 = β s.1.2 then x.1 ⟨s.1, h⟩ else x.2 ⟨s.1, lt_of_le_of_ne (not_lt.1 s.2) h⟩
    by_cases h : β s.1.1 = β s.1.2
    · simp only [h, dite_true]
      exact (continuous_apply _).comp continuous_fst
    · simp only [h, dite_false]
      exact (continuous_apply _).comp continuous_snd
  continuous_invFun := by
    refine Continuous.prodMk (continuous_pi fun s => ?_) (continuous_pi fun s => ?_) <;>
    exact continuous_apply _
variable {β}
theorem continuous_leviProj : Continuous (leviProj F n β) := by
  refine (leviChart β).isOpenEmbedding.isInducing.continuous_iff.2 ?_
  have : (leviChart β).toFun ∘ leviProj F n β = fun (p : blockUpper F n β) (s : LeviIndex n β) =>
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 := by
    funext p s
    simp only [Function.comp_apply, leviChart_apply, leviProj_apply, if_pos s.2]
  rw [this]
  exact continuous_pi fun s =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem s.1.1 s.1.2
theorem parabolicChart_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    (parabolicChart F n β).toFun (parabolicMk β m u) = coordAddEquiv β ((leviChart β).toFun m, u) := by
  funext s
  rw [parabolicChart_apply, coe_parabolicMk, Matrix.add_apply, coordAddEquiv_apply]
  by_cases h : β s.1.1 = β s.1.2
  · rw [dif_pos h, unipMatrix_apply_of_not_lt u (by rw [h]; exact lt_irrefl _), add_zero]
    rfl
  · have hlt := lt_of_le_of_ne (not_lt.1 s.2) h
    rw [dif_neg h, mem_levi.1 m.2 _ _ h, unipMatrix_apply_of_lt u hlt, zero_add]
variable (β) in

def parabolicMkHomeomorph : (levi F n β × (UnipotentIndex n β → F)) ≃ₜ blockUpper F n β where
  toFun x := parabolicMk β x.1 x.2
  invFun p := (leviProj F n β p, unipCoord p)
  left_inv x := Prod.ext (leviProj_parabolicMk x.1 x.2) (unipCoord_parabolicMk x.1 x.2)
  right_inv p := parabolicMk_leviProj_unipCoord p
  continuous_toFun := by
    refine (parabolicChart F n β).isOpenEmbedding.isInducing.continuous_iff.2 ?_
    have : (parabolicChart F n β).toFun ∘ (fun x : levi F n β × (UnipotentIndex n β → F) =>
        parabolicMk β x.1 x.2) = fun x => coordEquiv β ((leviChart β).toFun x.1, x.2) := by
      funext x
      rw [Function.comp_apply, parabolicChart_parabolicMk]
      rfl
    rw [this]
    exact (coordEquiv β).continuous.comp
      (((leviChart β).isOpenEmbedding.continuous.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := by
    refine continuous_leviProj.prodMk (continuous_pi fun s => ?_)
    exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem s.1.1 s.1.2
end Coordinates
section Measures
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]
variable {β : Fin n → α}
variable (β) in

def haarLevi (μ𝔪 : Measure (LeviIndex n β → F)) : Measure (levi F n β) :=
  (leviChart β).haar μ𝔪
instance isHaarMeasure_haarLevi (μ𝔪 : Measure (LeviIndex n β → F)) [μ𝔪.IsAddHaarMeasure] :
    (haarLevi β μ𝔪).IsHaarMeasure :=
  LinearChart.isHaarMeasure_haar _ μ𝔪
variable (β) in

def parabolicMeasure (μ𝔪 : Measure (LeviIndex n β → F)) (μ𝔫 : Measure (UnipotentIndex n β → F)) :
    Measure (ParabolicIndex n β → F) :=
  map (coordEquiv β) (μ𝔪.prod μ𝔫)
instance isAddHaarMeasure_parabolicMeasure (μ𝔪 : Measure (LeviIndex n β → F))
    (μ𝔫 : Measure (UnipotentIndex n β → F)) [μ𝔪.IsAddHaarMeasure] [μ𝔫.IsAddHaarMeasure] :
    (parabolicMeasure β μ𝔪 μ𝔫).IsAddHaarMeasure :=
  ContinuousAddEquiv.isAddHaarMeasure_map _ _
end Measures
section Main
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]
variable {β : Fin n → α}
end Main
end GodementJacquet
end GroundTheory.Automorphic


