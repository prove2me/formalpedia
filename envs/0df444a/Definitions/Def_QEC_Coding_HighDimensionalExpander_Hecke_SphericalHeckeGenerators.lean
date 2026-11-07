-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
-- name    : QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:26:31.170516+00:00
-- url     : https://prove2.me/theorems/8027e6bc-45cc-4b58-b6d3-cb0ad8d7a84f
-- title:
--   Spherical Hecke Generators
-- statement:
--   Definitions and structural lemmas for Spherical Hecke Generators, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeGenerators.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_projectiveDominantHeckeFunction_fundamental
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantCoweight_mem_doubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantGeneralLinear_det_localUnitOrder
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantGeneralLinear_orderLowerBound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_scalar_mul_eq_of_projective_mk_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralGeneralLinearToLocal_inv_orderLowerBound
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralGeneralLinearToLocal_orderLowerBound
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_integralGeneralLinear_det_localUnitOrder_eq_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_left_mul_mem_dominantDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_pow
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantDoubleCoset_isCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantDoubleCoset_isOpen
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_inv_first_entry_order
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_inv_orderLowerBound_first
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_last_entry_order
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankFour_eq_of_doubleCoset_inter_nonempty
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankFour_secondCompound_inv_first_entry_order
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankFour_secondCompound_inv_orderLowerBound
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankThree_eq_of_doubleCoset_inter_nonempty
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompound_orderLowerBound
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_right_mul_mem_dominantDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_scalarGeneralLinear_orderLowerBound
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise Valued
universe u
def projectiveDominantCoweightZero (n : ℕ) :
    ProjectiveDominantCoweight n where
  toDominant := {
    exponent := 0
    antitone_exponent := antitone_const }
  last_exponent_eq_zero := rfl
@[simp]
theorem projectiveDominantCoweightZero_exponent (n : ℕ)
    (i : Fin (n + 1)) :
    (projectiveDominantCoweightZero n).toDominant.exponent i = 0 :=
  rfl
def projectiveDominantCoweightAdd {n : ℕ}
    (a b : ProjectiveDominantCoweight n) :
    ProjectiveDominantCoweight n where
  toDominant := {
    exponent := fun i ↦
      a.toDominant.exponent i + b.toDominant.exponent i
    antitone_exponent := fun _ _ hij ↦
      Nat.add_le_add
        (a.toDominant.antitone_exponent hij)
        (b.toDominant.antitone_exponent hij) }
  last_exponent_eq_zero := by
    change a.toDominant.exponent (Fin.last n) +
      b.toDominant.exponent (Fin.last n) = 0
    rw [a.last_exponent_eq_zero, b.last_exponent_eq_zero, zero_add]
@[simp]
theorem projectiveDominantCoweightAdd_exponent {n : ℕ}
    (a b : ProjectiveDominantCoweight n) (i : Fin (n + 1)) :
    (projectiveDominantCoweightAdd a b).toDominant.exponent i =
      a.toDominant.exponent i + b.toDominant.exponent i :=
  rfl
@[simp]
theorem projectiveDominantCoweightAdd_zero {n : ℕ}
    (a : ProjectiveDominantCoweight n) :
    projectiveDominantCoweightAdd a (projectiveDominantCoweightZero n) = a := by
  apply ProjectiveDominantCoweight.ext
  funext i
  simp
@[simp]
theorem projectiveDominantCoweightZero_add {n : ℕ}
    (a : ProjectiveDominantCoweight n) :
    projectiveDominantCoweightAdd (projectiveDominantCoweightZero n) a = a := by
  apply ProjectiveDominantCoweight.ext
  funext i
  simp
theorem dominantGeneralLinear_projectiveDominantCoweightAdd
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n) :
    dominantGeneralLinear k
        (projectiveDominantCoweightAdd a b).toDominant =
      dominantGeneralLinear k a.toDominant *
        dominantGeneralLinear k b.toDominant := by
  change diagonalGeneralLinearHom (LocalFunctionField k) (n + 1)
      (fun i ↦ uniformizerUnit k ^
        (a.toDominant.exponent i + b.toDominant.exponent i)) =
    diagonalGeneralLinearHom (LocalFunctionField k) (n + 1)
        (fun i ↦ uniformizerUnit k ^ a.toDominant.exponent i) *
      diagonalGeneralLinearHom (LocalFunctionField k) (n + 1)
        (fun i ↦ uniformizerUnit k ^ b.toDominant.exponent i)
  rw [← map_mul]
  congr 1
  funext i
  exact pow_add _ _ _
theorem dominantCoweight_projectiveDominantCoweightAdd
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n) :
    dominantCoweight k
        (projectiveDominantCoweightAdd a b).toDominant =
      dominantCoweight k a.toDominant *
        dominantCoweight k b.toDominant := by
  exact congrArg Matrix.ProjGenLinGroup.mk
    (dominantGeneralLinear_projectiveDominantCoweightAdd k a b)
@[simp]
theorem dominantGeneralLinear_projectiveDominantCoweightZero
    (k : Type u) [Field k] (n : ℕ) :
    dominantGeneralLinear k (projectiveDominantCoweightZero n).toDominant = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [dominantGeneralLinear, diagonalGeneralLinear_apply, Matrix.one_apply]
@[simp]
theorem dominantCoweight_projectiveDominantCoweightZero
    (k : Type u) [Field k] (n : ℕ) :
    dominantCoweight k (projectiveDominantCoweightZero n).toDominant = 1 := by
  exact congrArg Matrix.ProjGenLinGroup.mk
    (dominantGeneralLinear_projectiveDominantCoweightZero k n)
theorem projectiveDominantDoubleCoset_zero
    (k : Type u) [Field k] (n : ℕ) :
    projectiveDominantDoubleCoset k (projectiveDominantCoweightZero n) =
      (maximalCompact k (n + 1) : Set (HeckeGroup k (n + 1))) := by
  simp [projectiveDominantDoubleCoset, dominantDoubleCoset]
@[simp]
theorem projectiveDominantHeckeFunction_zero
    (k : Type u) [Field k] [Finite k] (n : ℕ) :
    HeckeFunction.projectiveDominantHeckeFunction k
        (projectiveDominantCoweightZero n) = 1 := by
  ext x
  simp [HeckeFunction.projectiveDominantHeckeFunction_apply,
    projectiveDominantDoubleCoset_zero]
def cartanConvolutionFiber
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (x : HeckeGroup k (n + 1)) : Set (HeckeGroup k (n + 1)) :=
  projectiveDominantDoubleCoset k a ∩
    (fun t ↦ t⁻¹ * x) ⁻¹' projectiveDominantDoubleCoset k b
theorem cartanConvolutionFiber_isOpen
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (x : HeckeGroup k (n + 1)) :
    IsOpen (cartanConvolutionFiber k a b x) := by
  apply (projectiveDominantDoubleCoset_isOpen k a).inter
  exact (projectiveDominantDoubleCoset_isOpen k b).preimage
    (continuous_inv.mul continuous_const)
theorem cartanConvolutionFiber_nonempty_iff_mem_mul
    (k : Type u) [Field k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (x : HeckeGroup k (n + 1)) :
    (cartanConvolutionFiber k a b x).Nonempty ↔
      x ∈ projectiveDominantDoubleCoset k a *
        projectiveDominantDoubleCoset k b := by
  constructor
  · rintro ⟨t, hta, htb⟩
    refine ⟨t, hta, t⁻¹ * x, htb, ?_⟩
    group
  · rintro ⟨ta, hta, tb, htb, hproduct⟩
    refine ⟨ta, hta, ?_⟩
    rw [← hproduct]
    simpa [mul_assoc] using htb
theorem projectiveDominantHeckeFunction_mul_apply
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n)
    (x : HeckeGroup k (n + 1)) :
    (HeckeFunction.projectiveDominantHeckeFunction k a *
        HeckeFunction.projectiveDominantHeckeFunction k b) x =
      ((normalizedLocalHaarMeasure k (n + 1)).real
        (cartanConvolutionFiber k a b x) : ℂ) := by
  rw [HeckeFunction.mul_apply]
  have hfun : (fun t ↦
      HeckeFunction.projectiveDominantHeckeFunction k a t *
        HeckeFunction.projectiveDominantHeckeFunction k b (t⁻¹ * x)) =
      (cartanConvolutionFiber k a b x).indicator (fun _ ↦ (1 : ℂ)) := by
    funext t
    by_cases ha : t ∈ projectiveDominantDoubleCoset k a <;>
      by_cases hb : t⁻¹ * x ∈ projectiveDominantDoubleCoset k b <;>
      simp [HeckeFunction.projectiveDominantHeckeFunction_apply,
        cartanConvolutionFiber, ha, hb]
  rw [hfun]
  rw [MeasureTheory.integral_indicator_const (1 : ℂ)
    (cartanConvolutionFiber_isOpen k a b x).measurableSet]
  simp
theorem mem_cartanDoubleCoset_mul_of_mul_apply_ne_zero
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (c a b : ProjectiveDominantCoweight n)
    (hne : (HeckeFunction.projectiveDominantHeckeFunction k a *
        HeckeFunction.projectiveDominantHeckeFunction k b)
      (dominantCoweight k c.toDominant) ≠ 0) :
    dominantCoweight k c.toDominant ∈
      projectiveDominantDoubleCoset k a *
        projectiveDominantDoubleCoset k b := by
  apply (cartanConvolutionFiber_nonempty_iff_mem_mul k a b _).1
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  apply hne
  rw [projectiveDominantHeckeFunction_mul_apply, hempty]
  simp
def topCartanRightCoset
    (k : Type u) [Field k] {n : ℕ}
    (a : ProjectiveDominantCoweight n) : Set (HeckeGroup k (n + 1)) :=
  (fun t ↦ (dominantCoweight k a.toDominant)⁻¹ * t) ⁻¹'
    (maximalCompact k (n + 1) : Set (HeckeGroup k (n + 1)))
theorem topCartanRightCoset_subset_convolutionFiber
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n) :
    topCartanRightCoset k a ⊆
      cartanConvolutionFiber k a b
        (dominantCoweight k
          (projectiveDominantCoweightAdd a b).toDominant) := by
  intro t ht
  let da := dominantCoweight k a.toDominant
  let db := dominantCoweight k b.toDominant
  have hta : t = da * (da⁻¹ * t) := by group
  have hda : da ∈ projectiveDominantDoubleCoset k a :=
    dominantCoweight_mem_doubleCoset k a.toDominant
  have htmem : t ∈ projectiveDominantDoubleCoset k a := by
    rw [hta]
    exact right_mul_mem_dominantDoubleCoset k a.toDominant ht hda
  have hbinv : (da⁻¹ * t)⁻¹ ∈ maximalCompact k (n + 1) :=
    (maximalCompact k (n + 1)).inv_mem ht
  have hdb : db ∈ projectiveDominantDoubleCoset k b :=
    dominantCoweight_mem_doubleCoset k b.toDominant
  have hsecond : t⁻¹ * (da * db) ∈
      projectiveDominantDoubleCoset k b := by
    have heq : t⁻¹ * (da * db) = (da⁻¹ * t)⁻¹ * db := by
      rw [hta]
      group
    rw [heq]
    exact left_mul_mem_dominantDoubleCoset k b.toDominant hbinv hdb
  refine ⟨htmem, ?_⟩
  rw [dominantCoweight_projectiveDominantCoweightAdd]
  exact hsecond
theorem normalizedLocalHaarMeasure_topCartanRightCoset
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (a : ProjectiveDominantCoweight n) :
    normalizedLocalHaarMeasure k (n + 1) (topCartanRightCoset k a) = 1 := by
  rw [topCartanRightCoset, MeasureTheory.measure_preimage_mul,
    normalizedLocalHaarMeasure_maximalCompact]
theorem one_le_measureReal_top_cartanConvolutionFiber
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n) :
    1 ≤ (normalizedLocalHaarMeasure k (n + 1)).real
      (cartanConvolutionFiber k a b
        (dominantCoweight k
          (projectiveDominantCoweightAdd a b).toDominant)) := by
  let μ := normalizedLocalHaarMeasure k (n + 1)
  let fiber := cartanConvolutionFiber k a b
    (dominantCoweight k
      (projectiveDominantCoweightAdd a b).toDominant)
  have hsubset : topCartanRightCoset k a ⊆ fiber :=
    topCartanRightCoset_subset_convolutionFiber k a b
  have hfiberSubset : fiber ⊆ projectiveDominantDoubleCoset k a :=
    Set.inter_subset_left
  have hfinite : μ fiber ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (MeasureTheory.measure_mono hfiberSubset)
      (projectiveDominantDoubleCoset_isCompact k a).measure_lt_top
  have hmono : μ.real (topCartanRightCoset k a) ≤ μ.real fiber :=
    MeasureTheory.measureReal_mono hsubset hfinite
  have hleft : μ.real (topCartanRightCoset k a) = 1 := by
    rw [MeasureTheory.Measure.real,
      normalizedLocalHaarMeasure_topCartanRightCoset,
      ENNReal.toReal_one]
  rwa [hleft] at hmono
theorem projectiveDominantHeckeFunction_mul_apply_add_ne_zero
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (a b : ProjectiveDominantCoweight n) :
    (HeckeFunction.projectiveDominantHeckeFunction k a *
        HeckeFunction.projectiveDominantHeckeFunction k b)
      (dominantCoweight k
        (projectiveDominantCoweightAdd a b).toDominant) ≠ 0 := by
  rw [projectiveDominantHeckeFunction_mul_apply]
  have hpositive : (0 : ℝ) <
      (normalizedLocalHaarMeasure k (n + 1)).real
        (cartanConvolutionFiber k a b
          (dominantCoweight k
            (projectiveDominantCoweightAdd a b).toDominant)) :=
    lt_of_lt_of_le zero_lt_one
      (one_le_measureReal_top_cartanConvolutionFiber k a b)
  exact_mod_cast hpositive.ne'
theorem exists_compact_factorization_of_mem_cartanDoubleCoset_mul
    (k : Type u) [Field k] {n : ℕ}
    (c a b : ProjectiveDominantCoweight n)
    (hmem : dominantCoweight k c.toDominant ∈
      projectiveDominantDoubleCoset k a *
        projectiveDominantDoubleCoset k b) :
    ∃ left middle right : HeckeGroup k (n + 1),
      left ∈ maximalCompact k (n + 1) ∧
      middle ∈ maximalCompact k (n + 1) ∧
      right ∈ maximalCompact k (n + 1) ∧
      dominantCoweight k c.toDominant =
        left * dominantCoweight k a.toDominant * middle *
          dominantCoweight k b.toDominant * right := by
  rw [projectiveDominantDoubleCoset, projectiveDominantDoubleCoset,
    dominantDoubleCoset, dominantDoubleCoset] at hmem
  rcases hmem with ⟨xa, hxa, xb, hxb, hproduct⟩
  rcases hxa with ⟨ya, hya, rightA, hrightA, hxaProduct⟩
  rcases hya with ⟨leftA, hleftA, diagonalA, hdiagonalA, hyaProduct⟩
  rcases hxb with ⟨yb, hyb, rightB, hrightB, hxbProduct⟩
  rcases hyb with ⟨leftB, hleftB, diagonalB, hdiagonalB, hybProduct⟩
  rw [Set.mem_singleton_iff] at hdiagonalA hdiagonalB
  subst diagonalA
  subst diagonalB
  refine ⟨leftA, rightA * leftB, rightB, hleftA,
    (maximalCompact k (n + 1)).mul_mem hrightA hleftB,
    hrightB, ?_⟩
  rw [← hproduct, ← hxaProduct, ← hyaProduct,
    ← hxbProduct, ← hybProduct]
  group
theorem exists_integral_scalar_factorization_of_mem_cartanDoubleCoset_mul
    (k : Type u) [Field k] {n : ℕ}
    (c a b : ProjectiveDominantCoweight n)
    (hmem : dominantCoweight k c.toDominant ∈
      projectiveDominantDoubleCoset k a *
        projectiveDominantDoubleCoset k b) :
    ∃ (left middle right :
        GL (Fin (n + 1)) (Valued.integer (LocalFunctionField k)))
      (scalar : Units (LocalFunctionField k)),
      localUnitOrder scalar ≤ 0 ∧
        dominantGeneralLinear k c.toDominant =
          Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) scalar *
            (integralGeneralLinearToLocal k (n + 1) left *
              dominantGeneralLinear k a.toDominant *
              integralGeneralLinearToLocal k (n + 1) middle *
              dominantGeneralLinear k b.toDominant *
              integralGeneralLinearToLocal k (n + 1) right) := by
  obtain ⟨leftP, middleP, rightP, hleftP, hmiddleP, hrightP,
      hprojective⟩ :=
    exists_compact_factorization_of_mem_cartanDoubleCoset_mul
      k c a b hmem
  rw [mem_maximalCompact_iff] at hleftP hmiddleP hrightP
  obtain ⟨left, hleft⟩ := hleftP
  obtain ⟨middle, hmiddle⟩ := hmiddleP
  obtain ⟨right, hright⟩ := hrightP
  change Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k (n + 1) left) = leftP at hleft
  change Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k (n + 1) middle) = middleP at hmiddle
  change Matrix.ProjGenLinGroup.mk
      (integralGeneralLinearToLocal k (n + 1) right) = rightP at hright
  have hmk : Matrix.ProjGenLinGroup.mk
      (dominantGeneralLinear k c.toDominant) =
      Matrix.ProjGenLinGroup.mk
        (integralGeneralLinearToLocal k (n + 1) left *
          dominantGeneralLinear k a.toDominant *
          integralGeneralLinearToLocal k (n + 1) middle *
          dominantGeneralLinear k b.toDominant *
          integralGeneralLinearToLocal k (n + 1) right) := by
    change dominantCoweight k c.toDominant = _
    simp only [map_mul]
    rw [hleft, hmiddle, hright]
    exact hprojective
  obtain ⟨scalar, hscalar⟩ :=
    exists_scalar_mul_eq_of_projective_mk_eq hmk
  let leftLocal := integralGeneralLinearToLocal k (n + 1) left
  let middleLocal := integralGeneralLinearToLocal k (n + 1) middle
  let rightLocal := integralGeneralLinearToLocal k (n + 1) right
  let diagonalC := dominantGeneralLinear k c.toDominant
  let diagonalA := dominantGeneralLinear k a.toDominant
  let diagonalB := dominantGeneralLinear k b.toDominant
  let scalarGL := Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) scalar
  have hleftBound : MatrixOrderLowerBound 0
      (leftLocal : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_orderLowerBound left
  have hmiddleBound : MatrixOrderLowerBound 0
      (middleLocal : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_orderLowerBound middle
  have hrightBound : MatrixOrderLowerBound 0
      (rightLocal : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_orderLowerBound right
  have hdiagonalABound : MatrixOrderLowerBound 0
      (diagonalA : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    dominantGeneralLinear_orderLowerBound_zero a.toDominant
  have hdiagonalBBound : MatrixOrderLowerBound 0
      (diagonalB : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    dominantGeneralLinear_orderLowerBound_zero b.toDominant
  have hscalarBound : MatrixOrderLowerBound
      (localUnitOrder scalar : WithTop ℤ)
      (scalarGL : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) :=
    scalarGeneralLinear_orderLowerBound scalar
  have hproductBound : MatrixOrderLowerBound
      (localUnitOrder scalar : WithTop ℤ)
      (scalarGL * (leftLocal * diagonalA * middleLocal * diagonalB * rightLocal) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    simpa only [zero_add, add_zero] using
      hscalarBound.mul
        ((((hleftBound.mul hdiagonalABound).mul hmiddleBound).mul
          hdiagonalBBound).mul hrightBound)
  have hdiagonalCBound : MatrixOrderLowerBound
      (localUnitOrder scalar : WithTop ℤ)
      (diagonalC : Matrix (Fin (n + 1)) (Fin (n + 1))
        (LocalFunctionField k)) := by
    dsimp [diagonalC, diagonalA, diagonalB, leftLocal, middleLocal,
      rightLocal, scalarGL] at hscalar ⊢
    rw [hscalar]
    exact hproductBound
  have hentry := hdiagonalCBound (Fin.last n) (Fin.last n)
  dsimp [diagonalC] at hentry
  rw [projectiveDominant_last_entry_order c] at hentry
  have hnonpos : localUnitOrder scalar ≤ 0 :=
    WithTop.coe_le_coe.mp hentry
  exact ⟨left, middle, right, scalar, hnonpos, hscalar⟩
theorem projectiveDominant_exponent_sum_le_of_mem_cartanDoubleCoset_mul
    (k : Type u) [Field k] {n : ℕ}
    (c a b : ProjectiveDominantCoweight n)
    (hmem : dominantCoweight k c.toDominant ∈
      projectiveDominantDoubleCoset k a *
        projectiveDominantDoubleCoset k b) :
    (∑ i, (c.toDominant.exponent i : ℤ)) ≤
      (∑ i, (a.toDominant.exponent i : ℤ)) +
        ∑ i, (b.toDominant.exponent i : ℤ) := by
  obtain ⟨left, middle, right, scalar, hscalarNonpos, hGL⟩ :=
    exists_integral_scalar_factorization_of_mem_cartanDoubleCoset_mul
      k c a b hmem
  have hdet := congrArg Matrix.GeneralLinearGroup.det hGL
  have horder := congrArg localUnitOrder hdet
  have hsum :
      (∑ i, (c.toDominant.exponent i : ℤ)) =
        (n + 1 : ℤ) * localUnitOrder scalar +
          ((∑ i, (a.toDominant.exponent i : ℤ)) +
            ∑ i, (b.toDominant.exponent i : ℤ)) := by
    simpa [map_mul, Matrix.GeneralLinearGroup.det_scalar,
      localUnitOrder_mul, localUnitOrder_pow,
      integralGeneralLinear_det_localUnitOrder_eq_zero,
      dominantGeneralLinear_det_localUnitOrder,
      add_assoc, add_left_comm, add_comm] using horder
  rw [hsum]
  have hmultiple : (n + 1 : ℤ) * localUnitOrder scalar ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hscalarNonpos
  omega
theorem projectiveDominant_first_exponent_le_of_mem_cartanDoubleCoset_mul
    (k : Type u) [Field k] {n : ℕ}
    (c a b : ProjectiveDominantCoweight n)
    (hmem : dominantCoweight k c.toDominant ∈
      projectiveDominantDoubleCoset k a *
        projectiveDominantDoubleCoset k b) :
    c.toDominant.exponent (0 : Fin (n + 1)) ≤
      a.toDominant.exponent (0 : Fin (n + 1)) +
        b.toDominant.exponent (0 : Fin (n + 1)) := by
  obtain ⟨left, middle, right, scalar, hscalarNonpos, hGL⟩ :=
    exists_integral_scalar_factorization_of_mem_cartanDoubleCoset_mul
      k c a b hmem
  let leftLocal := integralGeneralLinearToLocal k (n + 1) left
  let middleLocal := integralGeneralLinearToLocal k (n + 1) middle
  let rightLocal := integralGeneralLinearToLocal k (n + 1) right
  let diagonalC := dominantGeneralLinear k c.toDominant
  let diagonalA := dominantGeneralLinear k a.toDominant
  let diagonalB := dominantGeneralLinear k b.toDominant
  let scalarGL := Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) scalar
  have hleftInv : MatrixOrderLowerBound 0
      ((leftLocal⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound left
  have hmiddleInv : MatrixOrderLowerBound 0
      ((middleLocal⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound middle
  have hrightInv : MatrixOrderLowerBound 0
      ((rightLocal⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound right
  have hdiagonalAInv :=
    projectiveDominant_inv_orderLowerBound_first (k := k) a
  have hdiagonalBInv :=
    projectiveDominant_inv_orderLowerBound_first (k := k) b
  have hscalarInv : MatrixOrderLowerBound
      ((-localUnitOrder scalar : ℤ) : WithTop ℤ)
      ((scalarGL⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (LocalFunctionField k)) := by
    rw [show scalarGL⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) scalar⁻¹ by
        exact (map_inv _ scalar).symm]
    simpa [scalarGL, localUnitOrder_inv] using
      (scalarGeneralLinear_orderLowerBound (d := n + 1) scalar⁻¹)
  have hinverse :
      diagonalC⁻¹ = rightLocal⁻¹ * diagonalB⁻¹ * middleLocal⁻¹ *
        diagonalA⁻¹ * leftLocal⁻¹ * scalarGL⁻¹ := by
    dsimp [diagonalC, diagonalA, diagonalB, leftLocal, middleLocal,
      rightLocal, scalarGL] at hGL ⊢
    rw [hGL]
    group
  have hproduct : MatrixOrderLowerBound
      (((-(b.toDominant.exponent (0 : Fin (n + 1)) : ℤ) -
        (a.toDominant.exponent (0 : Fin (n + 1)) : ℤ) -
        localUnitOrder scalar : ℤ)) : WithTop ℤ)
      (rightLocal⁻¹ * diagonalB⁻¹ * middleLocal⁻¹ *
          diagonalA⁻¹ * leftLocal⁻¹ * scalarGL⁻¹ :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    simpa only [zero_add, add_zero, ← WithTop.coe_add, sub_eq_add_neg, Int.cast_neg,
      Int.cast_natCast] using
      (((((hrightInv.mul hdiagonalBInv).mul hmiddleInv).mul
        hdiagonalAInv).mul hleftInv).mul hscalarInv)
  have hbound : MatrixOrderLowerBound
      (((-(b.toDominant.exponent (0 : Fin (n + 1)) : ℤ) -
        (a.toDominant.exponent (0 : Fin (n + 1)) : ℤ) -
        localUnitOrder scalar : ℤ)) : WithTop ℤ)
      ((diagonalC⁻¹ : GL (Fin (n + 1)) (LocalFunctionField k)) :
        Matrix (Fin (n + 1)) (Fin (n + 1))
          (LocalFunctionField k)) := by
    rw [hinverse]
    exact hproduct
  have hentry := hbound (0 : Fin (n + 1)) 0
  dsimp [diagonalC] at hentry
  rw [projectiveDominant_inv_first_entry_order c] at hentry
  have hint := WithTop.coe_le_coe.mp hentry
  push_cast at hint
  omega
theorem projectiveDominant_rankFour_firstTwoSum_le_of_mem_cartanDoubleCoset_mul
    (k : Type u) [Field k]
    (c a b : ProjectiveDominantCoweight 3)
    (hmem : dominantCoweight k c.toDominant ∈
      projectiveDominantDoubleCoset k a *
        projectiveDominantDoubleCoset k b) :
    c.toDominant.exponent (0 : Fin 4) +
        c.toDominant.exponent (1 : Fin 4) ≤
      (a.toDominant.exponent (0 : Fin 4) +
        a.toDominant.exponent (1 : Fin 4)) +
      (b.toDominant.exponent (0 : Fin 4) +
        b.toDominant.exponent (1 : Fin 4)) := by
  obtain ⟨left, middle, right, scalar, hscalarNonpos, hGL⟩ :=
    exists_integral_scalar_factorization_of_mem_cartanDoubleCoset_mul
      k c a b hmem
  let leftLocal := integralGeneralLinearToLocal k 4 left
  let middleLocal := integralGeneralLinearToLocal k 4 middle
  let rightLocal := integralGeneralLinearToLocal k 4 right
  let diagonalC := dominantGeneralLinear k c.toDominant
  let diagonalA := dominantGeneralLinear k a.toDominant
  let diagonalB := dominantGeneralLinear k b.toDominant
  let scalarGL := Matrix.GeneralLinearGroup.scalar (Fin 4) scalar
  have hleftInv : MatrixOrderLowerBound 0
      ((leftLocal⁻¹ : GL (Fin 4) (LocalFunctionField k)) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound left
  have hmiddleInv : MatrixOrderLowerBound 0
      ((middleLocal⁻¹ : GL (Fin 4) (LocalFunctionField k)) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound middle
  have hrightInv : MatrixOrderLowerBound 0
      ((rightLocal⁻¹ : GL (Fin 4) (LocalFunctionField k)) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) :=
    integralGeneralLinearToLocal_inv_orderLowerBound right
  have hleftCompoundInv : MatrixOrderLowerBound 0
      (((rankFourSecondCompoundGeneralLinear leftLocal)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [rankFourSecondCompoundGeneralLinear_inv_val]
    simpa using rankFourSecondCompound_orderLowerBound hleftInv
  have hmiddleCompoundInv : MatrixOrderLowerBound 0
      (((rankFourSecondCompoundGeneralLinear middleLocal)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [rankFourSecondCompoundGeneralLinear_inv_val]
    simpa using rankFourSecondCompound_orderLowerBound hmiddleInv
  have hrightCompoundInv : MatrixOrderLowerBound 0
      (((rankFourSecondCompoundGeneralLinear rightLocal)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [rankFourSecondCompoundGeneralLinear_inv_val]
    simpa using rankFourSecondCompound_orderLowerBound hrightInv
  have hdiagonalACompoundInv :=
    projectiveDominant_rankFour_secondCompound_inv_orderLowerBound
      (k := k) a
  have hdiagonalBCompoundInv :=
    projectiveDominant_rankFour_secondCompound_inv_orderLowerBound
      (k := k) b
  have hscalarInv : MatrixOrderLowerBound
      ((-localUnitOrder scalar : ℤ) : WithTop ℤ)
      ((scalarGL⁻¹ : GL (Fin 4) (LocalFunctionField k)) :
        Matrix (Fin 4) (Fin 4) (LocalFunctionField k)) := by
    rw [show scalarGL⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 4) scalar⁻¹ by
        exact (map_inv _ scalar).symm]
    simpa [scalarGL, localUnitOrder_inv] using
      (scalarGeneralLinear_orderLowerBound (d := 4) scalar⁻¹)
  have hscalarCompoundInv : MatrixOrderLowerBound
      (((-localUnitOrder scalar : ℤ) +
        (-localUnitOrder scalar : ℤ) : ℤ) : WithTop ℤ)
      (((rankFourSecondCompoundGeneralLinear scalarGL)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [rankFourSecondCompoundGeneralLinear_inv_val]
    simpa only [WithTop.coe_add] using
      rankFourSecondCompound_orderLowerBound hscalarInv
  have hinverse :
      diagonalC⁻¹ = rightLocal⁻¹ * diagonalB⁻¹ * middleLocal⁻¹ *
        diagonalA⁻¹ * leftLocal⁻¹ * scalarGL⁻¹ := by
    dsimp [diagonalC, diagonalA, diagonalB, leftLocal, middleLocal,
      rightLocal, scalarGL] at hGL ⊢
    rw [hGL]
    group
  have hcompoundInverse :
      (rankFourSecondCompoundGeneralLinear diagonalC)⁻¹ =
        (rankFourSecondCompoundGeneralLinear rightLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear diagonalB)⁻¹ *
          (rankFourSecondCompoundGeneralLinear middleLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear diagonalA)⁻¹ *
          (rankFourSecondCompoundGeneralLinear leftLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear scalarGL)⁻¹ := by
    have h := congrArg rankFourSecondCompoundGeneralLinear hinverse
    rw [rankFourSecondCompoundGeneralLinear_inv] at h
    repeat' rw [rankFourSecondCompoundGeneralLinear_mul] at h
    repeat' rw [rankFourSecondCompoundGeneralLinear_inv] at h
    exact h
  have hproduct : MatrixOrderLowerBound
      (((-((b.toDominant.exponent (0 : Fin 4) +
          b.toDominant.exponent (1 : Fin 4) : ℕ) : ℤ) : ℤ) +
        (-((a.toDominant.exponent (0 : Fin 4) +
          a.toDominant.exponent (1 : Fin 4) : ℕ) : ℤ) : ℤ) +
        (-localUnitOrder scalar : ℤ) +
        (-localUnitOrder scalar : ℤ) : ℤ) : WithTop ℤ)
      ((rankFourSecondCompoundGeneralLinear rightLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear diagonalB)⁻¹ *
          (rankFourSecondCompoundGeneralLinear middleLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear diagonalA)⁻¹ *
          (rankFourSecondCompoundGeneralLinear leftLocal)⁻¹ *
          (rankFourSecondCompoundGeneralLinear scalarGL)⁻¹ :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    simpa only [zero_add, add_zero, WithTop.coe_add, add_assoc] using
      (((((hrightCompoundInv.mul hdiagonalBCompoundInv).mul
        hmiddleCompoundInv).mul hdiagonalACompoundInv).mul
        hleftCompoundInv).mul hscalarCompoundInv)
  have hbound : MatrixOrderLowerBound
      (((-((b.toDominant.exponent (0 : Fin 4) +
          b.toDominant.exponent (1 : Fin 4) : ℕ) : ℤ) : ℤ) +
        (-((a.toDominant.exponent (0 : Fin 4) +
          a.toDominant.exponent (1 : Fin 4) : ℕ) : ℤ) : ℤ) +
        (-localUnitOrder scalar : ℤ) +
        (-localUnitOrder scalar : ℤ) : ℤ) : WithTop ℤ)
      (((rankFourSecondCompoundGeneralLinear diagonalC)⁻¹ :
        GL (Fin 6) (LocalFunctionField k)) :
        Matrix (Fin 6) (Fin 6) (LocalFunctionField k)) := by
    rw [hcompoundInverse]
    exact hproduct
  have hentry := hbound (0 : Fin 6) 0
  dsimp [diagonalC] at hentry
  rw [projectiveDominant_rankFour_secondCompound_inv_first_entry_order c]
    at hentry
  have hint := WithTop.coe_le_coe.mp hentry
  push_cast at hint
  omega
theorem projectiveDominant_mul_support_bounds
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (c a b : ProjectiveDominantCoweight n)
    (hne : (HeckeFunction.projectiveDominantHeckeFunction k a *
        HeckeFunction.projectiveDominantHeckeFunction k b)
      (dominantCoweight k c.toDominant) ≠ 0) :
    c.toDominant.exponent (0 : Fin (n + 1)) ≤
        a.toDominant.exponent (0 : Fin (n + 1)) +
          b.toDominant.exponent (0 : Fin (n + 1)) ∧
      (∑ i, (c.toDominant.exponent i : ℤ)) ≤
        (∑ i, (a.toDominant.exponent i : ℤ)) +
          ∑ i, (b.toDominant.exponent i : ℤ) := by
  have hmem := mem_cartanDoubleCoset_mul_of_mul_apply_ne_zero
    k c a b hne
  exact ⟨
    projectiveDominant_first_exponent_le_of_mem_cartanDoubleCoset_mul
      k c a b hmem,
    projectiveDominant_exponent_sum_le_of_mem_cartanDoubleCoset_mul
      k c a b hmem⟩
theorem projectiveDominant_rankFour_mul_support_firstTwoSum_bound
    (k : Type u) [Field k] [Finite k]
    (c a b : ProjectiveDominantCoweight 3)
    (hne : (HeckeFunction.projectiveDominantHeckeFunction k a *
        HeckeFunction.projectiveDominantHeckeFunction k b)
      (dominantCoweight k c.toDominant) ≠ 0) :
    c.toDominant.exponent (0 : Fin 4) +
        c.toDominant.exponent (1 : Fin 4) ≤
      (a.toDominant.exponent (0 : Fin 4) +
        a.toDominant.exponent (1 : Fin 4)) +
      (b.toDominant.exponent (0 : Fin 4) +
        b.toDominant.exponent (1 : Fin 4)) := by
  exact projectiveDominant_rankFour_firstTwoSum_le_of_mem_cartanDoubleCoset_mul
    k c a b (mem_cartanDoubleCoset_mul_of_mul_apply_ne_zero k c a b hne)
theorem rankThree_eq_of_first_exponent_eq_of_exponent_sum_eq
    (a b : ProjectiveDominantCoweight 2)
    (hfirst : a.toDominant.exponent (0 : Fin 3) =
      b.toDominant.exponent (0 : Fin 3))
    (hsum : (∑ i, (a.toDominant.exponent i : ℤ)) =
      ∑ i, (b.toDominant.exponent i : ℤ)) :
    a = b := by
  have halast : a.toDominant.exponent (2 : Fin 3) = 0 := by
    simpa using a.last_exponent_eq_zero
  have hblast : b.toDominant.exponent (2 : Fin 3) = 0 := by
    simpa using b.last_exponent_eq_zero
  apply ProjectiveDominantCoweight.ext
  funext i
  fin_cases i
  · exact hfirst
  · simp [Fin.sum_univ_succ, halast, hblast] at hsum
    change a.toDominant.exponent (1 : Fin 3) =
      b.toDominant.exponent (1 : Fin 3)
    omega
  · exact halast.trans hblast.symm
theorem rankFour_eq_of_first_exponent_eq_of_firstTwoSum_eq_of_exponent_sum_eq
    (a b : ProjectiveDominantCoweight 3)
    (hfirst : a.toDominant.exponent (0 : Fin 4) =
      b.toDominant.exponent (0 : Fin 4))
    (hfirstTwo : a.toDominant.exponent (0 : Fin 4) +
        a.toDominant.exponent (1 : Fin 4) =
      b.toDominant.exponent (0 : Fin 4) +
        b.toDominant.exponent (1 : Fin 4))
    (hsum : (∑ i, (a.toDominant.exponent i : ℤ)) =
      ∑ i, (b.toDominant.exponent i : ℤ)) :
    a = b := by
  have hsecond : a.toDominant.exponent (1 : Fin 4) =
      b.toDominant.exponent (1 : Fin 4) := by omega
  have halast : a.toDominant.exponent (3 : Fin 4) = 0 := by
    simpa using a.last_exponent_eq_zero
  have hblast : b.toDominant.exponent (3 : Fin 4) = 0 := by
    simpa using b.last_exponent_eq_zero
  have hthird : a.toDominant.exponent (2 : Fin 4) =
      b.toDominant.exponent (2 : Fin 4) := by
    simp [Fin.sum_univ_succ, halast, hblast] at hsum
    omega
  apply ProjectiveDominantCoweight.ext
  funext i
  fin_cases i
  · exact hfirst
  · exact hsecond
  · exact hthird
  · exact halast.trans hblast.symm
def projectiveDominantExponentSum {n : ℕ}
    (weight : ProjectiveDominantCoweight n) : ℕ :=
  ∑ i, weight.toDominant.exponent i
def rankThreeCartanGrade (weight : ProjectiveDominantCoweight 2) : ℕ :=
  weight.toDominant.exponent 0 + projectiveDominantExponentSum weight
def rankFourCartanGrade (weight : ProjectiveDominantCoweight 3) : ℕ :=
  weight.toDominant.exponent 0 +
    (weight.toDominant.exponent 0 + weight.toDominant.exponent 1) +
    projectiveDominantExponentSum weight
theorem projectiveDominantExponentSum_add {n : ℕ}
    (a b : ProjectiveDominantCoweight n) :
    projectiveDominantExponentSum (projectiveDominantCoweightAdd a b) =
      projectiveDominantExponentSum a +
        projectiveDominantExponentSum b := by
  simp [projectiveDominantExponentSum, projectiveDominantCoweightAdd,
    Finset.sum_add_distrib]
theorem rankThreeCartanGrade_add
    (a b : ProjectiveDominantCoweight 2) :
    rankThreeCartanGrade (projectiveDominantCoweightAdd a b) =
      rankThreeCartanGrade a + rankThreeCartanGrade b := by
  simp [rankThreeCartanGrade, projectiveDominantExponentSum_add]
  omega
theorem rankFourCartanGrade_add
    (a b : ProjectiveDominantCoweight 3) :
    rankFourCartanGrade (projectiveDominantCoweightAdd a b) =
      rankFourCartanGrade a + rankFourCartanGrade b := by
  simp [rankFourCartanGrade, projectiveDominantExponentSum_add]
  omega
theorem rankThreeCartanGrade_lt_add_of_mul_apply_ne_zero_of_ne
    (k : Type u) [Field k] [Finite k]
    (c a b : ProjectiveDominantCoweight 2)
    (hne : (HeckeFunction.projectiveDominantHeckeFunction k a *
        HeckeFunction.projectiveDominantHeckeFunction k b)
      (dominantCoweight k c.toDominant) ≠ 0)
    (hc : c ≠ projectiveDominantCoweightAdd a b) :
    rankThreeCartanGrade c <
      rankThreeCartanGrade (projectiveDominantCoweightAdd a b) := by
  obtain ⟨hfirst, hsumInt⟩ :=
    projectiveDominant_mul_support_bounds k c a b hne
  have hsum : projectiveDominantExponentSum c ≤
      projectiveDominantExponentSum a +
        projectiveDominantExponentSum b := by
    exact_mod_cast hsumInt
  have hgrade : rankThreeCartanGrade c ≤
      rankThreeCartanGrade (projectiveDominantCoweightAdd a b) := by
    rw [rankThreeCartanGrade_add]
    simp only [rankThreeCartanGrade]
    omega
  apply lt_of_le_of_ne hgrade
  intro hgradeEq
  rw [rankThreeCartanGrade_add] at hgradeEq
  simp only [rankThreeCartanGrade] at hgradeEq
  have hfirstEq : c.toDominant.exponent (0 : Fin 3) =
      (projectiveDominantCoweightAdd a b).toDominant.exponent 0 := by
    rw [projectiveDominantCoweightAdd_exponent]
    omega
  have hsumEq : projectiveDominantExponentSum c =
      projectiveDominantExponentSum (projectiveDominantCoweightAdd a b) := by
    rw [projectiveDominantExponentSum_add]
    omega
  apply hc
  apply rankThree_eq_of_first_exponent_eq_of_exponent_sum_eq _ _ hfirstEq
  exact_mod_cast hsumEq
theorem rankFourCartanGrade_lt_add_of_mul_apply_ne_zero_of_ne
    (k : Type u) [Field k] [Finite k]
    (c a b : ProjectiveDominantCoweight 3)
    (hne : (HeckeFunction.projectiveDominantHeckeFunction k a *
        HeckeFunction.projectiveDominantHeckeFunction k b)
      (dominantCoweight k c.toDominant) ≠ 0)
    (hc : c ≠ projectiveDominantCoweightAdd a b) :
    rankFourCartanGrade c <
      rankFourCartanGrade (projectiveDominantCoweightAdd a b) := by
  obtain ⟨hfirst, hsumInt⟩ :=
    projectiveDominant_mul_support_bounds k c a b hne
  have hfirstTwo :=
    projectiveDominant_rankFour_mul_support_firstTwoSum_bound
      k c a b hne
  have hsum : projectiveDominantExponentSum c ≤
      projectiveDominantExponentSum a +
        projectiveDominantExponentSum b := by
    exact_mod_cast hsumInt
  have hgrade : rankFourCartanGrade c ≤
      rankFourCartanGrade (projectiveDominantCoweightAdd a b) := by
    rw [rankFourCartanGrade_add]
    simp only [rankFourCartanGrade]
    omega
  apply lt_of_le_of_ne hgrade
  intro hgradeEq
  rw [rankFourCartanGrade_add] at hgradeEq
  simp only [rankFourCartanGrade] at hgradeEq
  have hfirstEq : c.toDominant.exponent (0 : Fin 4) =
      (projectiveDominantCoweightAdd a b).toDominant.exponent 0 := by
    rw [projectiveDominantCoweightAdd_exponent]
    omega
  have hfirstTwoEq : c.toDominant.exponent (0 : Fin 4) +
        c.toDominant.exponent (1 : Fin 4) =
      (projectiveDominantCoweightAdd a b).toDominant.exponent 0 +
        (projectiveDominantCoweightAdd a b).toDominant.exponent 1 := by
    simp only [projectiveDominantCoweightAdd_exponent]
    omega
  have hsumEq : projectiveDominantExponentSum c =
      projectiveDominantExponentSum (projectiveDominantCoweightAdd a b) := by
    rw [projectiveDominantExponentSum_add]
    omega
  apply hc
  apply rankFour_eq_of_first_exponent_eq_of_firstTwoSum_eq_of_exponent_sum_eq
    _ _ hfirstEq hfirstTwoEq
  exact_mod_cast hsumEq
def rankThreeProjectiveMultiplicity
    (weight : ProjectiveDominantCoweight 2) : Fin 2 → ℕ :=
  ![weight.toDominant.exponent 0 - weight.toDominant.exponent 1,
    weight.toDominant.exponent 1]
def rankThreeProjectiveWeight (m : Fin 2 → ℕ) :
    ProjectiveDominantCoweight 2 where
  toDominant := {
    exponent := ![m 0 + m 1, m 1, 0]
    antitone_exponent := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all }
  last_exponent_eq_zero := by simp
def rankThreeProjectiveMultiplicityEquiv :
    ProjectiveDominantCoweight 2 ≃ (Fin 2 → ℕ) where
  toFun := rankThreeProjectiveMultiplicity
  invFun := rankThreeProjectiveWeight
  left_inv weight := by
    apply ProjectiveDominantCoweight.ext
    funext i
    have h01 : weight.toDominant.exponent 1 ≤
        weight.toDominant.exponent 0 :=
      weight.toDominant.antitone_exponent
        (show (0 : Fin 3) ≤ (1 : Fin 3) by decide)
    have hlast : weight.toDominant.exponent 2 = 0 := by
      simpa using weight.last_exponent_eq_zero
    fin_cases i
    · simp [rankThreeProjectiveWeight, rankThreeProjectiveMultiplicity]
      omega
    · simp [rankThreeProjectiveWeight, rankThreeProjectiveMultiplicity]
    · simpa [rankThreeProjectiveWeight] using hlast.symm
  right_inv m := by
    funext i
    fin_cases i <;>
      simp [rankThreeProjectiveWeight, rankThreeProjectiveMultiplicity]
theorem rankThreeProjectiveMultiplicity_add
    (a b : ProjectiveDominantCoweight 2) :
    rankThreeProjectiveMultiplicity
        (projectiveDominantCoweightAdd a b) =
      rankThreeProjectiveMultiplicity a +
        rankThreeProjectiveMultiplicity b := by
  funext i
  have ha := a.toDominant.antitone_exponent
    (show (0 : Fin 3) ≤ (1 : Fin 3) by decide)
  have hb := b.toDominant.antitone_exponent
    (show (0 : Fin 3) ≤ (1 : Fin 3) by decide)
  fin_cases i <;>
    simp [rankThreeProjectiveMultiplicity,
      projectiveDominantCoweightAdd]
  all_goals omega
def rankFourProjectiveMultiplicity
    (weight : ProjectiveDominantCoweight 3) : Fin 3 → ℕ :=
  ![weight.toDominant.exponent 0 - weight.toDominant.exponent 1,
    weight.toDominant.exponent 1 - weight.toDominant.exponent 2,
    weight.toDominant.exponent 2]
def rankFourProjectiveWeight (m : Fin 3 → ℕ) :
    ProjectiveDominantCoweight 3 where
  toDominant := {
    exponent := ![m 0 + m 1 + m 2, m 1 + m 2, m 2, 0]
    antitone_exponent := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all }
  last_exponent_eq_zero := by simp
def rankFourProjectiveMultiplicityEquiv :
    ProjectiveDominantCoweight 3 ≃ (Fin 3 → ℕ) where
  toFun := rankFourProjectiveMultiplicity
  invFun := rankFourProjectiveWeight
  left_inv weight := by
    apply ProjectiveDominantCoweight.ext
    funext i
    have h01 : weight.toDominant.exponent 1 ≤
        weight.toDominant.exponent 0 :=
      weight.toDominant.antitone_exponent
        (show (0 : Fin 4) ≤ (1 : Fin 4) by decide)
    have h12 : weight.toDominant.exponent 2 ≤
        weight.toDominant.exponent 1 :=
      weight.toDominant.antitone_exponent
        (show (1 : Fin 4) ≤ (2 : Fin 4) by decide)
    have hlast : weight.toDominant.exponent 3 = 0 := by
      simpa using weight.last_exponent_eq_zero
    fin_cases i <;>
      simp [rankFourProjectiveWeight, rankFourProjectiveMultiplicity,
        hlast] <;> omega
  right_inv m := by
    funext i
    fin_cases i
    · simp [rankFourProjectiveWeight, rankFourProjectiveMultiplicity]
      omega
    · simp [rankFourProjectiveWeight, rankFourProjectiveMultiplicity]
    · simp [rankFourProjectiveWeight, rankFourProjectiveMultiplicity]
theorem rankFourProjectiveMultiplicity_add
    (a b : ProjectiveDominantCoweight 3) :
    rankFourProjectiveMultiplicity
        (projectiveDominantCoweightAdd a b) =
      rankFourProjectiveMultiplicity a +
        rankFourProjectiveMultiplicity b := by
  funext i
  have ha01 := a.toDominant.antitone_exponent
    (show (0 : Fin 4) ≤ (1 : Fin 4) by decide)
  have hb01 := b.toDominant.antitone_exponent
    (show (0 : Fin 4) ≤ (1 : Fin 4) by decide)
  have ha12 := a.toDominant.antitone_exponent
    (show (1 : Fin 4) ≤ (2 : Fin 4) by decide)
  have hb12 := b.toDominant.antitone_exponent
    (show (1 : Fin 4) ≤ (2 : Fin 4) by decide)
  fin_cases i <;>
    simp [rankFourProjectiveMultiplicity,
      projectiveDominantCoweightAdd] <;> omega
theorem rankThreeProjectiveMultiplicity_fundamental
    (color : Fin 2) :
    rankThreeProjectiveMultiplicity
        (fundamentalProjectiveDominantCoweight 2 (color.val + 1) (by omega)) =
      Pi.single color 1 := by
  funext i
  fin_cases color <;> fin_cases i <;>
    simp [rankThreeProjectiveMultiplicity,
      fundamentalProjectiveDominantCoweight, fundamentalDominantCoweight]
theorem rankFourProjectiveMultiplicity_fundamental
    (color : Fin 3) :
    rankFourProjectiveMultiplicity
        (fundamentalProjectiveDominantCoweight 3 (color.val + 1) (by omega)) =
      Pi.single color 1 := by
  funext i
  fin_cases color <;> fin_cases i <;>
    simp [rankFourProjectiveMultiplicity,
      fundamentalProjectiveDominantCoweight, fundamentalDominantCoweight]
theorem exists_rankThree_projective_predecessor
    (weight : ProjectiveDominantCoweight 2)
    (hne : weight ≠ projectiveDominantCoweightZero 2) :
    ∃ (previous : ProjectiveDominantCoweight 2) (color : Fin 2),
      weight = projectiveDominantCoweightAdd previous
        (fundamentalProjectiveDominantCoweight 2 (color.val + 1) (by omega)) := by
  let m := rankThreeProjectiveMultiplicity weight
  have hm : m ≠ 0 := by
    intro hmzero
    apply hne
    apply ProjectiveDominantCoweight.ext
    have hrecover := rankThreeProjectiveMultiplicityEquiv.left_inv weight
    have hzeroRecover : rankThreeProjectiveWeight (0 : Fin 2 → ℕ) =
        projectiveDominantCoweightZero 2 := by
      apply ProjectiveDominantCoweight.ext
      funext i
      fin_cases i <;> simp [rankThreeProjectiveWeight]
    rw [← hzeroRecover, ← hrecover]
    simp [rankThreeProjectiveMultiplicityEquiv, m, hmzero]
  have hexists : ∃ color : Fin 2, m color ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hm (funext hall)
  obtain ⟨color, hcolor⟩ := hexists
  have hcolorPos : 0 < m color := Nat.pos_of_ne_zero hcolor
  let previousMultiplicity : Fin 2 → ℕ :=
    Function.update m color (m color - 1)
  have hdecomp : m = previousMultiplicity + Pi.single color 1 := by
    funext i
    by_cases hi : i = color
    · subst i
      simp [previousMultiplicity]
      omega
    · simp [previousMultiplicity, hi]
  refine ⟨rankThreeProjectiveWeight previousMultiplicity, color, ?_⟩
  apply rankThreeProjectiveMultiplicityEquiv.injective
  change rankThreeProjectiveMultiplicity weight =
    rankThreeProjectiveMultiplicity
      (projectiveDominantCoweightAdd
        (rankThreeProjectiveWeight previousMultiplicity)
        (fundamentalProjectiveDominantCoweight 2 (color.val + 1) (by omega)))
  rw [rankThreeProjectiveMultiplicity_add,
    rankThreeProjectiveMultiplicity_fundamental]
  have hprevious :=
    rankThreeProjectiveMultiplicityEquiv.right_inv previousMultiplicity
  change rankThreeProjectiveMultiplicity
      (rankThreeProjectiveWeight previousMultiplicity) =
    previousMultiplicity at hprevious
  rw [hprevious]
  simpa [m] using hdecomp
theorem exists_rankFour_projective_predecessor
    (weight : ProjectiveDominantCoweight 3)
    (hne : weight ≠ projectiveDominantCoweightZero 3) :
    ∃ (previous : ProjectiveDominantCoweight 3) (color : Fin 3),
      weight = projectiveDominantCoweightAdd previous
        (fundamentalProjectiveDominantCoweight 3 (color.val + 1) (by omega)) := by
  let m := rankFourProjectiveMultiplicity weight
  have hm : m ≠ 0 := by
    intro hmzero
    apply hne
    apply ProjectiveDominantCoweight.ext
    have hrecover := rankFourProjectiveMultiplicityEquiv.left_inv weight
    have hzeroRecover : rankFourProjectiveWeight (0 : Fin 3 → ℕ) =
        projectiveDominantCoweightZero 3 := by
      apply ProjectiveDominantCoweight.ext
      funext i
      fin_cases i <;> simp [rankFourProjectiveWeight]
    rw [← hzeroRecover, ← hrecover]
    simp [rankFourProjectiveMultiplicityEquiv, m, hmzero]
  have hexists : ∃ color : Fin 3, m color ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hm (funext hall)
  obtain ⟨color, hcolor⟩ := hexists
  have hcolorPos : 0 < m color := Nat.pos_of_ne_zero hcolor
  let previousMultiplicity : Fin 3 → ℕ :=
    Function.update m color (m color - 1)
  have hdecomp : m = previousMultiplicity + Pi.single color 1 := by
    funext i
    by_cases hi : i = color
    · subst i
      simp [previousMultiplicity]
      omega
    · simp [previousMultiplicity, hi]
  refine ⟨rankFourProjectiveWeight previousMultiplicity, color, ?_⟩
  apply rankFourProjectiveMultiplicityEquiv.injective
  change rankFourProjectiveMultiplicity weight =
    rankFourProjectiveMultiplicity
      (projectiveDominantCoweightAdd
        (rankFourProjectiveWeight previousMultiplicity)
        (fundamentalProjectiveDominantCoweight 3 (color.val + 1) (by omega)))
  rw [rankFourProjectiveMultiplicity_add,
    rankFourProjectiveMultiplicity_fundamental]
  have hprevious :=
    rankFourProjectiveMultiplicityEquiv.right_inv previousMultiplicity
  change rankFourProjectiveMultiplicity
      (rankFourProjectiveWeight previousMultiplicity) =
    previousMultiplicity at hprevious
  rw [hprevious]
  simpa [m] using hdecomp
@[simp]
theorem projectiveDominantHeckeFunction_apply_dominant_self
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) :
    HeckeFunction.projectiveDominantHeckeFunction k weight
        (dominantCoweight k weight.toDominant) = 1 := by
  have hmem : dominantCoweight k weight.toDominant ∈
      projectiveDominantDoubleCoset k weight :=
    dominantCoweight_mem_doubleCoset k weight.toDominant
  rw [HeckeFunction.projectiveDominantHeckeFunction_apply,
    Set.indicator_of_mem hmem]
theorem projectiveDominantHeckeFunction_apply_dominant_rankThree_of_ne
    (k : Type u) [Field k] [Finite k]
    (a b : ProjectiveDominantCoweight 2) (hab : a ≠ b) :
    HeckeFunction.projectiveDominantHeckeFunction k a
        (dominantCoweight k b.toDominant) = 0 := by
  have hnot : dominantCoweight k b.toDominant ∉
      projectiveDominantDoubleCoset k a := by
    intro hmem
    have hself : dominantCoweight k b.toDominant ∈
        projectiveDominantDoubleCoset k b :=
      dominantCoweight_mem_doubleCoset k b.toDominant
    have heq :=
      projectiveDominant_rankThree_eq_of_doubleCoset_inter_nonempty
        k b a ⟨_, hself, hmem⟩
    exact hab heq.symm
  rw [HeckeFunction.projectiveDominantHeckeFunction_apply,
    Set.indicator_of_notMem hnot]
theorem projectiveDominantHeckeFunction_apply_dominant_rankFour_of_ne
    (k : Type u) [Field k] [Finite k]
    (a b : ProjectiveDominantCoweight 3) (hab : a ≠ b) :
    HeckeFunction.projectiveDominantHeckeFunction k a
        (dominantCoweight k b.toDominant) = 0 := by
  have hnot : dominantCoweight k b.toDominant ∉
      projectiveDominantDoubleCoset k a := by
    intro hmem
    have hself : dominantCoweight k b.toDominant ∈
        projectiveDominantDoubleCoset k b :=
      dominantCoweight_mem_doubleCoset k b.toDominant
    have heq :=
      projectiveDominant_rankFour_eq_of_doubleCoset_inter_nonempty
        k b a ⟨_, hself, hmem⟩
    exact hab heq.symm
  rw [HeckeFunction.projectiveDominantHeckeFunction_apply,
    Set.indicator_of_notMem hnot]
noncomputable def rankThreeFundamentalHeckeEval
    (k : Type u) [Field k] [Finite k] :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] HeckeFunction k 3 :=
  MvPolynomial.aeval fun color ↦
    HeckeFunction.fundamentalHeckeFunction k 3 (color.val + 1)
@[simp]
theorem rankThreeFundamentalHeckeEval_X
    (k : Type u) [Field k] [Finite k] (color : Fin 2) :
    rankThreeFundamentalHeckeEval k (MvPolynomial.X color) =
      HeckeFunction.fundamentalHeckeFunction k 3 (color.val + 1) := by
  simp [rankThreeFundamentalHeckeEval]
noncomputable def rankFourFundamentalHeckeEval
    (k : Type u) [Field k] [Finite k] :
    MvPolynomial (Fin 3) ℂ →ₐ[ℂ] HeckeFunction k 4 :=
  MvPolynomial.aeval fun color ↦
    HeckeFunction.fundamentalHeckeFunction k 4 (color.val + 1)
@[simp]
theorem rankFourFundamentalHeckeEval_X
    (k : Type u) [Field k] [Finite k] (color : Fin 3) :
    rankFourFundamentalHeckeEval k (MvPolynomial.X color) =
      HeckeFunction.fundamentalHeckeFunction k 4 (color.val + 1) := by
  simp [rankFourFundamentalHeckeEval]
theorem rankThree_projectiveDominantHeckeFunction_mem_evalRange_of_grade_lt
    (k : Type u) [Field k] [Finite k] (grade : ℕ) :
    ∀ weight : ProjectiveDominantCoweight 2,
      rankThreeCartanGrade weight < grade →
      HeckeFunction.projectiveDominantHeckeFunction k weight ∈
        (rankThreeFundamentalHeckeEval k).range := by
  classical
  induction grade with
  | zero =>
      intro weight hgrade
      omega
  | succ grade ih =>
      intro weight hgrade
      by_cases hzero : weight = projectiveDominantCoweightZero 2
      · subst weight
        rw [projectiveDominantHeckeFunction_zero]
        exact Subalgebra.one_mem _
      · obtain ⟨previous, color, hweight⟩ :=
          exists_rankThree_projective_predecessor weight hzero
        let fundamental :=
          fundamentalProjectiveDominantCoweight 2 (color.val + 1) (by omega)
        have hfundamentalGrade : 0 < rankThreeCartanGrade fundamental := by
          fin_cases color <;>
            norm_num [fundamental, rankThreeCartanGrade,
              projectiveDominantExponentSum,
              fundamentalProjectiveDominantCoweight,
              fundamentalDominantCoweight, Fin.sum_univ_succ]
        have hpreviousGrade : rankThreeCartanGrade previous < grade := by
          have hadd := rankThreeCartanGrade_add previous fundamental
          rw [← hweight] at hadd
          omega
        have hpreviousMem :
            HeckeFunction.projectiveDominantHeckeFunction k previous ∈
              (rankThreeFundamentalHeckeEval k).range :=
          ih previous hpreviousGrade
        have hfundamentalMem :
            HeckeFunction.projectiveDominantHeckeFunction k fundamental ∈
              (rankThreeFundamentalHeckeEval k).range := by
          refine ⟨MvPolynomial.X color, ?_⟩
          change rankThreeFundamentalHeckeEval k (MvPolynomial.X color) =
            HeckeFunction.projectiveDominantHeckeFunction k fundamental
          rw [rankThreeFundamentalHeckeEval_X,
            ← HeckeFunction.projectiveDominantHeckeFunction_fundamental]
        let product :=
          HeckeFunction.projectiveDominantHeckeFunction k previous *
            HeckeFunction.projectiveDominantHeckeFunction k fundamental
        have hproductMem : product ∈
            (rankThreeFundamentalHeckeEval k).range :=
          Subalgebra.mul_mem _ hpreviousMem hfundamentalMem
        obtain ⟨weights, hexpansion⟩ :=
          HeckeFunction.exists_projectiveDominantHeckeFunction_expansion_rankThree
            product
        have htopCoefficient :
            product (dominantCoweight k weight.toDominant) ≠ 0 := by
          dsimp [product]
          rw [hweight]
          exact projectiveDominantHeckeFunction_mul_apply_add_ne_zero
            k previous fundamental
        let coefficient : ℂ :=
          product (dominantCoweight k weight.toDominant)
        have hcoefficient : coefficient ≠ 0 := htopCoefficient
        have hweightMem : weight ∈ weights := by
          by_contra hnotMem
          have heval := congrArg
            (fun f : HeckeFunction k 3 ↦
              f (dominantCoweight k weight.toDominant)) hexpansion
          change product (dominantCoweight k weight.toDominant) =
            (∑ other ∈ weights,
              product (dominantCoweight k other.toDominant) •
                HeckeFunction.projectiveDominantHeckeFunction k other)
              (dominantCoweight k weight.toDominant) at heval
          rw [HeckeFunction.finset_sum_apply] at heval
          have hsumZero :
              (∑ other ∈ weights,
                (product (dominantCoweight k other.toDominant) •
                  HeckeFunction.projectiveDominantHeckeFunction k other)
                    (dominantCoweight k weight.toDominant)) = 0 := by
            apply Finset.sum_eq_zero
            intro other hother
            have hne : other ≠ weight := fun heq ↦ hnotMem (heq ▸ hother)
            simp [projectiveDominantHeckeFunction_apply_dominant_rankThree_of_ne
              k other weight hne]
          exact htopCoefficient (heval.trans hsumZero)
        let lowerSum := ∑ other ∈ weights.erase weight,
          product (dominantCoweight k other.toDominant) •
            HeckeFunction.projectiveDominantHeckeFunction k other
        have hlowerMem : lowerSum ∈
            (rankThreeFundamentalHeckeEval k).range := by
          dsimp [lowerSum]
          apply Submodule.sum_mem
            ((rankThreeFundamentalHeckeEval k).range).toSubmodule
          intro other hother
          rw [Finset.mem_erase] at hother
          by_cases hcoefficient :
              product (dominantCoweight k other.toDominant) = 0
          · rw [hcoefficient, zero_smul]
            exact Subalgebra.zero_mem _
          · have hstrict : rankThreeCartanGrade other <
                rankThreeCartanGrade weight := by
              rw [hweight]
              exact rankThreeCartanGrade_lt_add_of_mul_apply_ne_zero_of_ne
                k other previous fundamental hcoefficient
                  (fun heq ↦ hother.1 (heq.trans hweight.symm))
            have hotherGrade : rankThreeCartanGrade other < grade := by
              omega
            exact ((rankThreeFundamentalHeckeEval k).range).smul_mem
              (ih other hotherGrade) _
        have hsplit : product =
            coefficient •
                HeckeFunction.projectiveDominantHeckeFunction k weight +
              lowerSum := by
          calc
            product = ∑ other ∈ weights,
                product (dominantCoweight k other.toDominant) •
                  HeckeFunction.projectiveDominantHeckeFunction k other :=
              hexpansion
            _ = coefficient •
                  HeckeFunction.projectiveDominantHeckeFunction k weight +
                lowerSum := by
              dsimp [coefficient, lowerSum]
              exact (Finset.add_sum_erase weights
                (fun other ↦
                  product (dominantCoweight k other.toDominant) •
                    HeckeFunction.projectiveDominantHeckeFunction k other)
                hweightMem).symm
        have hsolve :
            HeckeFunction.projectiveDominantHeckeFunction k weight =
              coefficient⁻¹ •
                (product - lowerSum) := by
          have hisolate : product - lowerSum =
              coefficient •
                HeckeFunction.projectiveDominantHeckeFunction k weight := by
            rw [hsplit]
            abel_nf
          calc
            HeckeFunction.projectiveDominantHeckeFunction k weight =
                (1 : ℂ) •
                  HeckeFunction.projectiveDominantHeckeFunction k weight := by
                    simp
            _ = (coefficient⁻¹ * coefficient) •
                    HeckeFunction.projectiveDominantHeckeFunction k weight := by
                      rw [inv_mul_cancel₀ hcoefficient]
            _ = coefficient⁻¹ •
                  (coefficient •
                    HeckeFunction.projectiveDominantHeckeFunction k weight) := by
                      rw [mul_smul]
            _ = coefficient⁻¹ •
                  (product - lowerSum) := by rw [hisolate]
        rw [hsolve]
        exact ((rankThreeFundamentalHeckeEval k).range).smul_mem
          (((rankThreeFundamentalHeckeEval k).range).sub_mem
            hproductMem hlowerMem) _
theorem rankThree_projectiveDominantHeckeFunction_mem_evalRange
    (k : Type u) [Field k] [Finite k]
    (weight : ProjectiveDominantCoweight 2) :
    HeckeFunction.projectiveDominantHeckeFunction k weight ∈
      (rankThreeFundamentalHeckeEval k).range := by
  exact rankThree_projectiveDominantHeckeFunction_mem_evalRange_of_grade_lt
    k (rankThreeCartanGrade weight + 1) weight (by omega)
theorem rankThreeFundamentalHeckeEval_surjective
    (k : Type u) [Field k] [Finite k] :
    Function.Surjective (rankThreeFundamentalHeckeEval k) := by
  classical
  intro f
  change f ∈ (rankThreeFundamentalHeckeEval k).range
  obtain ⟨weights, hf⟩ :=
    HeckeFunction.exists_projectiveDominantHeckeFunction_expansion_rankThree f
  rw [hf]
  apply Submodule.sum_mem
    ((rankThreeFundamentalHeckeEval k).range).toSubmodule
  intro weight hweight
  exact ((rankThreeFundamentalHeckeEval k).range).smul_mem
    (rankThree_projectiveDominantHeckeFunction_mem_evalRange k weight) _
theorem rankFour_projectiveDominantHeckeFunction_mem_evalRange_of_grade_lt
    (k : Type u) [Field k] [Finite k] (grade : ℕ) :
    ∀ weight : ProjectiveDominantCoweight 3,
      rankFourCartanGrade weight < grade →
      HeckeFunction.projectiveDominantHeckeFunction k weight ∈
        (rankFourFundamentalHeckeEval k).range := by
  classical
  induction grade with
  | zero =>
      intro weight hgrade
      omega
  | succ grade ih =>
      intro weight hgrade
      by_cases hzero : weight = projectiveDominantCoweightZero 3
      · subst weight
        rw [projectiveDominantHeckeFunction_zero]
        exact Subalgebra.one_mem _
      · obtain ⟨previous, color, hweight⟩ :=
          exists_rankFour_projective_predecessor weight hzero
        let fundamental :=
          fundamentalProjectiveDominantCoweight 3 (color.val + 1) (by omega)
        have hfundamentalGrade : 0 < rankFourCartanGrade fundamental := by
          fin_cases color <;>
            norm_num [fundamental, rankFourCartanGrade,
              projectiveDominantExponentSum,
              fundamentalProjectiveDominantCoweight,
              fundamentalDominantCoweight, Fin.sum_univ_succ]
        have hpreviousGrade : rankFourCartanGrade previous < grade := by
          have hadd := rankFourCartanGrade_add previous fundamental
          rw [← hweight] at hadd
          omega
        have hpreviousMem :
            HeckeFunction.projectiveDominantHeckeFunction k previous ∈
              (rankFourFundamentalHeckeEval k).range :=
          ih previous hpreviousGrade
        have hfundamentalMem :
            HeckeFunction.projectiveDominantHeckeFunction k fundamental ∈
              (rankFourFundamentalHeckeEval k).range := by
          refine ⟨MvPolynomial.X color, ?_⟩
          change rankFourFundamentalHeckeEval k (MvPolynomial.X color) =
            HeckeFunction.projectiveDominantHeckeFunction k fundamental
          rw [rankFourFundamentalHeckeEval_X,
            ← HeckeFunction.projectiveDominantHeckeFunction_fundamental]
        let product :=
          HeckeFunction.projectiveDominantHeckeFunction k previous *
            HeckeFunction.projectiveDominantHeckeFunction k fundamental
        have hproductMem : product ∈
            (rankFourFundamentalHeckeEval k).range :=
          Subalgebra.mul_mem _ hpreviousMem hfundamentalMem
        obtain ⟨weights, hexpansion⟩ :=
          HeckeFunction.exists_projectiveDominantHeckeFunction_expansion_rankFour
            product
        have htopCoefficient :
            product (dominantCoweight k weight.toDominant) ≠ 0 := by
          dsimp [product]
          rw [hweight]
          exact projectiveDominantHeckeFunction_mul_apply_add_ne_zero
            k previous fundamental
        let coefficient : ℂ :=
          product (dominantCoweight k weight.toDominant)
        have hcoefficient : coefficient ≠ 0 := htopCoefficient
        have hweightMem : weight ∈ weights := by
          by_contra hnotMem
          have heval := congrArg
            (fun f : HeckeFunction k 4 ↦
              f (dominantCoweight k weight.toDominant)) hexpansion
          change product (dominantCoweight k weight.toDominant) =
            (∑ other ∈ weights,
              product (dominantCoweight k other.toDominant) •
                HeckeFunction.projectiveDominantHeckeFunction k other)
              (dominantCoweight k weight.toDominant) at heval
          rw [HeckeFunction.finset_sum_apply] at heval
          have hsumZero :
              (∑ other ∈ weights,
                (product (dominantCoweight k other.toDominant) •
                  HeckeFunction.projectiveDominantHeckeFunction k other)
                    (dominantCoweight k weight.toDominant)) = 0 := by
            apply Finset.sum_eq_zero
            intro other hother
            have hne : other ≠ weight := fun heq ↦ hnotMem (heq ▸ hother)
            simp [projectiveDominantHeckeFunction_apply_dominant_rankFour_of_ne
              k other weight hne]
          exact htopCoefficient (heval.trans hsumZero)
        let lowerSum := ∑ other ∈ weights.erase weight,
          product (dominantCoweight k other.toDominant) •
            HeckeFunction.projectiveDominantHeckeFunction k other
        have hlowerMem : lowerSum ∈
            (rankFourFundamentalHeckeEval k).range := by
          dsimp [lowerSum]
          apply Submodule.sum_mem
            ((rankFourFundamentalHeckeEval k).range).toSubmodule
          intro other hother
          rw [Finset.mem_erase] at hother
          by_cases hcoefficientOther :
              product (dominantCoweight k other.toDominant) = 0
          · rw [hcoefficientOther, zero_smul]
            exact Subalgebra.zero_mem _
          · have hstrict : rankFourCartanGrade other <
                rankFourCartanGrade weight := by
              rw [hweight]
              exact rankFourCartanGrade_lt_add_of_mul_apply_ne_zero_of_ne
                k other previous fundamental hcoefficientOther
                  (fun heq ↦ hother.1 (heq.trans hweight.symm))
            have hotherGrade : rankFourCartanGrade other < grade := by
              omega
            exact ((rankFourFundamentalHeckeEval k).range).smul_mem
              (ih other hotherGrade) _
        have hsplit : product =
            coefficient •
                HeckeFunction.projectiveDominantHeckeFunction k weight +
              lowerSum := by
          calc
            product = ∑ other ∈ weights,
                product (dominantCoweight k other.toDominant) •
                  HeckeFunction.projectiveDominantHeckeFunction k other :=
              hexpansion
            _ = coefficient •
                  HeckeFunction.projectiveDominantHeckeFunction k weight +
                lowerSum := by
              dsimp [coefficient, lowerSum]
              exact (Finset.add_sum_erase weights
                (fun other ↦
                  product (dominantCoweight k other.toDominant) •
                    HeckeFunction.projectiveDominantHeckeFunction k other)
                hweightMem).symm
        have hsolve :
            HeckeFunction.projectiveDominantHeckeFunction k weight =
              coefficient⁻¹ • (product - lowerSum) := by
          have hisolate : product - lowerSum =
              coefficient •
                HeckeFunction.projectiveDominantHeckeFunction k weight := by
            rw [hsplit]
            abel_nf
          calc
            HeckeFunction.projectiveDominantHeckeFunction k weight =
                (1 : ℂ) •
                  HeckeFunction.projectiveDominantHeckeFunction k weight := by
                    simp
            _ = (coefficient⁻¹ * coefficient) •
                    HeckeFunction.projectiveDominantHeckeFunction k weight := by
                      rw [inv_mul_cancel₀ hcoefficient]
            _ = coefficient⁻¹ •
                  (coefficient •
                    HeckeFunction.projectiveDominantHeckeFunction k weight) := by
                      rw [mul_smul]
            _ = coefficient⁻¹ • (product - lowerSum) := by rw [hisolate]
        rw [hsolve]
        exact ((rankFourFundamentalHeckeEval k).range).smul_mem
          (((rankFourFundamentalHeckeEval k).range).sub_mem
            hproductMem hlowerMem) _
theorem rankFour_projectiveDominantHeckeFunction_mem_evalRange
    (k : Type u) [Field k] [Finite k]
    (weight : ProjectiveDominantCoweight 3) :
    HeckeFunction.projectiveDominantHeckeFunction k weight ∈
      (rankFourFundamentalHeckeEval k).range := by
  exact rankFour_projectiveDominantHeckeFunction_mem_evalRange_of_grade_lt
    k (rankFourCartanGrade weight + 1) weight (by omega)
theorem rankFourFundamentalHeckeEval_surjective
    (k : Type u) [Field k] [Finite k] :
    Function.Surjective (rankFourFundamentalHeckeEval k) := by
  classical
  intro f
  change f ∈ (rankFourFundamentalHeckeEval k).range
  obtain ⟨weights, hf⟩ :=
    HeckeFunction.exists_projectiveDominantHeckeFunction_expansion_rankFour f
  rw [hf]
  apply Submodule.sum_mem
    ((rankFourFundamentalHeckeEval k).range).toSubmodule
  intro weight hweight
  exact ((rankFourFundamentalHeckeEval k).range).smul_mem
    (rankFour_projectiveDominantHeckeFunction_mem_evalRange k weight) _
def HasRankThreeLeadingCartanTerm
    (k : Type u) [Field k] [Finite k]
    (f : HeckeFunction k 3) (weight : ProjectiveDominantCoweight 2) : Prop :=
  f (dominantCoweight k weight.toDominant) ≠ 0 ∧
    ∀ other : ProjectiveDominantCoweight 2,
      f (dominantCoweight k other.toDominant) ≠ 0 →
      other ≠ weight →
      rankThreeCartanGrade other < rankThreeCartanGrade weight
theorem hasRankThreeLeadingCartanTerm_zero
    (k : Type u) [Field k] [Finite k] :
    HasRankThreeLeadingCartanTerm k
      (HeckeFunction.projectiveDominantHeckeFunction k
        (projectiveDominantCoweightZero 2))
      (projectiveDominantCoweightZero 2) := by
  constructor
  · simp
  · intro other hother hne
    exfalso
    apply hother
    exact projectiveDominantHeckeFunction_apply_dominant_rankThree_of_ne
      k (projectiveDominantCoweightZero 2) other (Ne.symm hne)
theorem HasRankThreeLeadingCartanTerm.mul_projectiveDominantHeckeFunction
    (k : Type u) [Field k] [Finite k]
    {f : HeckeFunction k 3} {a : ProjectiveDominantCoweight 2}
    (hf : HasRankThreeLeadingCartanTerm k f a)
    (b : ProjectiveDominantCoweight 2) :
    HasRankThreeLeadingCartanTerm k
      (f * HeckeFunction.projectiveDominantHeckeFunction k b)
      (projectiveDominantCoweightAdd a b) := by
  classical
  obtain ⟨weights, hexpansion⟩ :=
    HeckeFunction.exists_projectiveDominantHeckeFunction_expansion_rankThree f
  have haMem : a ∈ weights := by
    by_contra hnotMem
    have heval := congrArg
      (fun g : HeckeFunction k 3 ↦ g (dominantCoweight k a.toDominant))
      hexpansion
    change f (dominantCoweight k a.toDominant) =
      (∑ other ∈ weights,
        f (dominantCoweight k other.toDominant) •
          HeckeFunction.projectiveDominantHeckeFunction k other)
        (dominantCoweight k a.toDominant) at heval
    rw [HeckeFunction.finset_sum_apply] at heval
    have hsumZero :
        (∑ other ∈ weights,
          (f (dominantCoweight k other.toDominant) •
            HeckeFunction.projectiveDominantHeckeFunction k other)
              (dominantCoweight k a.toDominant)) = 0 := by
      apply Finset.sum_eq_zero
      intro other hother
      have hne : other ≠ a := fun heq ↦ hnotMem (heq ▸ hother)
      simp [projectiveDominantHeckeFunction_apply_dominant_rankThree_of_ne
        k other a hne]
    exact hf.1 (heval.trans hsumZero)
  have hproductExpansion :
      f * HeckeFunction.projectiveDominantHeckeFunction k b =
        ∑ other ∈ weights,
          f (dominantCoweight k other.toDominant) •
            (HeckeFunction.projectiveDominantHeckeFunction k other *
              HeckeFunction.projectiveDominantHeckeFunction k b) := by
    calc
      f * HeckeFunction.projectiveDominantHeckeFunction k b =
          (∑ other ∈ weights,
            f (dominantCoweight k other.toDominant) •
              HeckeFunction.projectiveDominantHeckeFunction k other) *
            HeckeFunction.projectiveDominantHeckeFunction k b := by
              rw [← hexpansion]
      _ = ∑ other ∈ weights,
          f (dominantCoweight k other.toDominant) •
            (HeckeFunction.projectiveDominantHeckeFunction k other *
              HeckeFunction.projectiveDominantHeckeFunction k b) := by
            simp only [Finset.sum_mul, smul_mul_assoc]
  constructor
  · have htopEval :
        (f * HeckeFunction.projectiveDominantHeckeFunction k b)
            (dominantCoweight k
              (projectiveDominantCoweightAdd a b).toDominant) =
          f (dominantCoweight k a.toDominant) *
            (HeckeFunction.projectiveDominantHeckeFunction k a *
              HeckeFunction.projectiveDominantHeckeFunction k b)
              (dominantCoweight k
                (projectiveDominantCoweightAdd a b).toDominant) := by
      rw [hproductExpansion, HeckeFunction.finset_sum_apply,
        Finset.sum_eq_single a]
      · simp
      · intro other hother hne
        by_cases hcoefficient :
            f (dominantCoweight k other.toDominant) = 0
        · simp [hcoefficient]
        · have hotherGrade := hf.2 other hcoefficient hne
          have htargetGrade :
              rankThreeCartanGrade
                  (projectiveDominantCoweightAdd other b) <
                rankThreeCartanGrade
                  (projectiveDominantCoweightAdd a b) := by
            rw [rankThreeCartanGrade_add, rankThreeCartanGrade_add]
            omega
          have hconvolution :
              (HeckeFunction.projectiveDominantHeckeFunction k other *
                HeckeFunction.projectiveDominantHeckeFunction k b)
                (dominantCoweight k
                  (projectiveDominantCoweightAdd a b).toDominant) = 0 := by
            by_contra hnonzero
            by_cases heq : projectiveDominantCoweightAdd a b =
                projectiveDominantCoweightAdd other b
            · rw [heq] at htargetGrade
              omega
            · have hstrict :=
                rankThreeCartanGrade_lt_add_of_mul_apply_ne_zero_of_ne
                  k (projectiveDominantCoweightAdd a b) other b hnonzero heq
              omega
          simp [hconvolution]
      · exact fun hnot ↦ (hnot haMem).elim
    rw [htopEval]
    exact mul_ne_zero hf.1
      (projectiveDominantHeckeFunction_mul_apply_add_ne_zero k a b)
  · intro output houtput houtputNe
    have hsumNe :
        (∑ other ∈ weights,
          (f (dominantCoweight k other.toDominant) •
            (HeckeFunction.projectiveDominantHeckeFunction k other *
              HeckeFunction.projectiveDominantHeckeFunction k b))
            (dominantCoweight k output.toDominant)) ≠ 0 := by
      rw [← HeckeFunction.finset_sum_apply, ← hproductExpansion]
      exact houtput
    obtain ⟨source, hsourceMem, hsourceTerm⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero hsumNe
    change f (dominantCoweight k source.toDominant) *
        (HeckeFunction.projectiveDominantHeckeFunction k source *
          HeckeFunction.projectiveDominantHeckeFunction k b)
          (dominantCoweight k output.toDominant) ≠ 0 at hsourceTerm
    have hsourceCoefficient := (mul_ne_zero_iff.mp hsourceTerm).1
    have hsourceConvolution := (mul_ne_zero_iff.mp hsourceTerm).2
    by_cases hsourceEq : source = a
    · subst source
      exact rankThreeCartanGrade_lt_add_of_mul_apply_ne_zero_of_ne
        k output a b hsourceConvolution houtputNe
    · have hsourceGrade := hf.2 source hsourceCoefficient hsourceEq
      have houtputLe : rankThreeCartanGrade output ≤
          rankThreeCartanGrade (projectiveDominantCoweightAdd source b) := by
        by_cases heq : output = projectiveDominantCoweightAdd source b
        · rw [heq]
        · exact (rankThreeCartanGrade_lt_add_of_mul_apply_ne_zero_of_ne
            k output source b hsourceConvolution heq).le
      rw [rankThreeCartanGrade_add] at houtputLe
      rw [rankThreeCartanGrade_add]
      omega
def rankThreeMonomialWeight (m : Fin 2 →₀ ℕ) :
    ProjectiveDominantCoweight 2 :=
  rankThreeProjectiveWeight (Finsupp.equivFunOnFinite m)
def rankThreeHeckeMonomial
    (k : Type u) [Field k] [Finite k] (m : Fin 2 →₀ ℕ) :
    HeckeFunction k 3 :=
  rankThreeFundamentalHeckeEval k (MvPolynomial.monomial m 1)
@[simp]
theorem rankThreeMonomialWeight_zero :
    rankThreeMonomialWeight 0 = projectiveDominantCoweightZero 2 := by
  apply ProjectiveDominantCoweight.ext
  funext i
  fin_cases i <;> simp [rankThreeMonomialWeight, rankThreeProjectiveWeight]
@[simp]
theorem rankThreeHeckeMonomial_zero
    (k : Type u) [Field k] [Finite k] :
    rankThreeHeckeMonomial k 0 = 1 := by
  simp [rankThreeHeckeMonomial]
theorem rankThreeMonomialWeight_add (m n : Fin 2 →₀ ℕ) :
    rankThreeMonomialWeight (m + n) =
      projectiveDominantCoweightAdd
        (rankThreeMonomialWeight m) (rankThreeMonomialWeight n) := by
  apply ProjectiveDominantCoweight.ext
  funext i
  fin_cases i <;>
    simp [rankThreeMonomialWeight, rankThreeProjectiveWeight,
      projectiveDominantCoweightAdd] <;> omega
theorem rankThreeHeckeMonomial_add
    (k : Type u) [Field k] [Finite k] (m n : Fin 2 →₀ ℕ) :
    rankThreeHeckeMonomial k (m + n) =
      rankThreeHeckeMonomial k m * rankThreeHeckeMonomial k n := by
  rw [rankThreeHeckeMonomial, rankThreeHeckeMonomial,
    rankThreeHeckeMonomial, ← map_mul, MvPolynomial.monomial_mul]
  simp
theorem rankThreeMonomialWeight_single_one (color : Fin 2) :
    rankThreeMonomialWeight (Finsupp.single color 1) =
      fundamentalProjectiveDominantCoweight 2 (color.val + 1) (by omega) := by
  apply ProjectiveDominantCoweight.ext
  funext i
  fin_cases color <;> fin_cases i <;>
    simp [rankThreeMonomialWeight, rankThreeProjectiveWeight,
      fundamentalProjectiveDominantCoweight, fundamentalDominantCoweight,
      Finsupp.equivFunOnFinite]
theorem rankThreeHeckeMonomial_single_one
    (k : Type u) [Field k] [Finite k] (color : Fin 2) :
    rankThreeHeckeMonomial k (Finsupp.single color 1) =
      HeckeFunction.projectiveDominantHeckeFunction k
        (fundamentalProjectiveDominantCoweight 2 (color.val + 1) (by omega)) := by
  rw [rankThreeHeckeMonomial]
  have hmonomial : (MvPolynomial.monomial (Finsupp.single color 1) 1 :
      MvPolynomial (Fin 2) ℂ) = MvPolynomial.X color := by
    rw [← MvPolynomial.X_pow_eq_monomial]
    simp
  rw [hmonomial, rankThreeFundamentalHeckeEval_X,
    ← HeckeFunction.projectiveDominantHeckeFunction_fundamental]
theorem hasRankThreeLeadingCartanTerm_monomial_of_degree_lt
    (k : Type u) [Field k] [Finite k] (degree : ℕ) :
    ∀ m : Fin 2 →₀ ℕ,
      (m.sum fun _ exponent ↦ exponent) < degree →
      HasRankThreeLeadingCartanTerm k
        (rankThreeHeckeMonomial k m) (rankThreeMonomialWeight m) := by
  classical
  induction degree with
  | zero =>
      intro m hdegree
      omega
  | succ degree ih =>
      intro m hdegree
      by_cases hm : m = 0
      · subst m
        simpa using hasRankThreeLeadingCartanTerm_zero k
      · have hsupport : m.support.Nonempty :=
          Finsupp.support_nonempty_iff.mpr hm
        obtain ⟨color, hcolorSupport⟩ := hsupport
        have hcolor : m color ≠ 0 := Finsupp.mem_support_iff.mp hcolorSupport
        let previous := m - Finsupp.single color 1
        have hdecomp : m = previous + Finsupp.single color 1 := by
          ext i
          by_cases hi : i = color
          · subst i
            simp [previous]
            omega
          · simp [previous, hi]
        have hdegreeDecomp :
            (m.sum fun _ exponent ↦ exponent) =
              (previous.sum fun _ exponent ↦ exponent) + 1 := by
          rw [hdecomp, Finsupp.sum_add_index'
            (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
          simp
        have hpreviousDegree :
            (previous.sum fun _ exponent ↦ exponent) < degree := by
          omega
        have hprevious := ih previous hpreviousDegree
        have hstep := hprevious.mul_projectiveDominantHeckeFunction k
          (fundamentalProjectiveDominantCoweight 2 (color.val + 1) (by omega))
        rw [hdecomp, rankThreeHeckeMonomial_add,
          rankThreeMonomialWeight_add,
          rankThreeHeckeMonomial_single_one,
          rankThreeMonomialWeight_single_one]
        exact hstep
theorem hasRankThreeLeadingCartanTerm_monomial
    (k : Type u) [Field k] [Finite k] (m : Fin 2 →₀ ℕ) :
    HasRankThreeLeadingCartanTerm k
      (rankThreeHeckeMonomial k m) (rankThreeMonomialWeight m) := by
  exact hasRankThreeLeadingCartanTerm_monomial_of_degree_lt k
    ((m.sum fun _ exponent ↦ exponent) + 1) m (by omega)
theorem rankThreeMonomialWeight_injective :
    Function.Injective rankThreeMonomialWeight := by
  intro m n hweight
  have hm := congrArg rankThreeProjectiveMultiplicity hweight
  have hmRecover := rankThreeProjectiveMultiplicityEquiv.right_inv
    (Finsupp.equivFunOnFinite m)
  have hnRecover := rankThreeProjectiveMultiplicityEquiv.right_inv
    (Finsupp.equivFunOnFinite n)
  change rankThreeProjectiveMultiplicity (rankThreeProjectiveWeight
      (Finsupp.equivFunOnFinite m)) = Finsupp.equivFunOnFinite m at hmRecover
  change rankThreeProjectiveMultiplicity (rankThreeProjectiveWeight
      (Finsupp.equivFunOnFinite n)) = Finsupp.equivFunOnFinite n at hnRecover
  rw [rankThreeMonomialWeight, hmRecover,
    rankThreeMonomialWeight, hnRecover] at hm
  exact Finsupp.equivFunOnFinite.injective hm
theorem rankThreeFundamentalHeckeEval_monomial
    (k : Type u) [Field k] [Finite k]
    (m : Fin 2 →₀ ℕ) (coefficient : ℂ) :
    rankThreeFundamentalHeckeEval k
        (MvPolynomial.monomial m coefficient) =
      coefficient • rankThreeHeckeMonomial k m := by
  rw [rankThreeHeckeMonomial, rankThreeFundamentalHeckeEval,
    MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  rw [Algebra.smul_def]
  simp
theorem rankThreeFundamentalHeckeEval_eq_zero_iff
    (k : Type u) [Field k] [Finite k]
    (p : MvPolynomial (Fin 2) ℂ) :
    rankThreeFundamentalHeckeEval k p = 0 ↔ p = 0 := by
  classical
  constructor
  · intro hp
    by_contra hpne
    have hsupport : p.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply hpne
      apply MvPolynomial.support_eq_empty.mp hempty
    obtain ⟨leading, hleadingMem, hmax⟩ :=
      Finset.exists_max_image p.support
        (fun m ↦ rankThreeCartanGrade (rankThreeMonomialWeight m)) hsupport
    have hexpansion : rankThreeFundamentalHeckeEval k p =
        ∑ m ∈ p.support,
          p.coeff m • rankThreeHeckeMonomial k m := by
      calc
        rankThreeFundamentalHeckeEval k p =
            rankThreeFundamentalHeckeEval k
              (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m)) := by
                congr 1
                exact MvPolynomial.as_sum p
        _ = ∑ m ∈ p.support,
              p.coeff m • rankThreeHeckeMonomial k m := by
                rw [map_sum]
                apply Finset.sum_congr rfl
                intro m hm
                exact rankThreeFundamentalHeckeEval_monomial k m (p.coeff m)
    have heval := congrArg
      (fun f : HeckeFunction k 3 ↦
        f (dominantCoweight k (rankThreeMonomialWeight leading).toDominant))
      hexpansion
    rw [hp] at heval
    change (0 : HeckeFunction k 3)
        (dominantCoweight k (rankThreeMonomialWeight leading).toDominant) =
      (∑ m ∈ p.support,
        p.coeff m • rankThreeHeckeMonomial k m)
          (dominantCoweight k
            (rankThreeMonomialWeight leading).toDominant) at heval
    rw [HeckeFunction.zero_apply,
      HeckeFunction.finset_sum_apply] at heval
    rw [Finset.sum_eq_single leading] at heval
    · have hleadingCoefficient : p.coeff leading ≠ 0 :=
        MvPolynomial.mem_support_iff.mp hleadingMem
      have hleadingValue :=
        (hasRankThreeLeadingCartanTerm_monomial k leading).1
      simp only [HeckeFunction.smul_apply, smul_eq_mul] at heval
      exact (mul_ne_zero hleadingCoefficient hleadingValue) heval.symm
    · intro other hother hne
      have hotherValue : rankThreeHeckeMonomial k other
          (dominantCoweight k
            (rankThreeMonomialWeight leading).toDominant) = 0 := by
        by_contra hnonzero
        have hweightNe : rankThreeMonomialWeight leading ≠
            rankThreeMonomialWeight other := by
          intro heq
          exact hne (rankThreeMonomialWeight_injective heq.symm)
        have hstrict :=
          (hasRankThreeLeadingCartanTerm_monomial k other).2
            (rankThreeMonomialWeight leading) hnonzero hweightNe
        have hle := hmax other hother
        omega
      simp [hotherValue]
    · exact fun hnot ↦ (hnot hleadingMem).elim
  · intro hp
    rw [hp, map_zero]
theorem rankThreeFundamentalHeckeEval_injective
    (k : Type u) [Field k] [Finite k] :
    Function.Injective (rankThreeFundamentalHeckeEval k) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply (rankThreeFundamentalHeckeEval_eq_zero_iff k (p - q)).1
  rw [map_sub, hpq, sub_self]
def HasRankFourLeadingCartanTerm
    (k : Type u) [Field k] [Finite k]
    (f : HeckeFunction k 4) (weight : ProjectiveDominantCoweight 3) : Prop :=
  f (dominantCoweight k weight.toDominant) ≠ 0 ∧
    ∀ other : ProjectiveDominantCoweight 3,
      f (dominantCoweight k other.toDominant) ≠ 0 →
      other ≠ weight →
      rankFourCartanGrade other < rankFourCartanGrade weight
theorem hasRankFourLeadingCartanTerm_zero
    (k : Type u) [Field k] [Finite k] :
    HasRankFourLeadingCartanTerm k
      (HeckeFunction.projectiveDominantHeckeFunction k
        (projectiveDominantCoweightZero 3))
      (projectiveDominantCoweightZero 3) := by
  constructor
  · simp
  · intro other hother hne
    exfalso
    apply hother
    exact projectiveDominantHeckeFunction_apply_dominant_rankFour_of_ne
      k (projectiveDominantCoweightZero 3) other (Ne.symm hne)
theorem HasRankFourLeadingCartanTerm.mul_projectiveDominantHeckeFunction
    (k : Type u) [Field k] [Finite k]
    {f : HeckeFunction k 4} {a : ProjectiveDominantCoweight 3}
    (hf : HasRankFourLeadingCartanTerm k f a)
    (b : ProjectiveDominantCoweight 3) :
    HasRankFourLeadingCartanTerm k
      (f * HeckeFunction.projectiveDominantHeckeFunction k b)
      (projectiveDominantCoweightAdd a b) := by
  classical
  obtain ⟨weights, hexpansion⟩ :=
    HeckeFunction.exists_projectiveDominantHeckeFunction_expansion_rankFour f
  have haMem : a ∈ weights := by
    by_contra hnotMem
    have heval := congrArg
      (fun g : HeckeFunction k 4 ↦ g (dominantCoweight k a.toDominant))
      hexpansion
    change f (dominantCoweight k a.toDominant) =
      (∑ other ∈ weights,
        f (dominantCoweight k other.toDominant) •
          HeckeFunction.projectiveDominantHeckeFunction k other)
        (dominantCoweight k a.toDominant) at heval
    rw [HeckeFunction.finset_sum_apply] at heval
    have hsumZero :
        (∑ other ∈ weights,
          (f (dominantCoweight k other.toDominant) •
            HeckeFunction.projectiveDominantHeckeFunction k other)
              (dominantCoweight k a.toDominant)) = 0 := by
      apply Finset.sum_eq_zero
      intro other hother
      have hne : other ≠ a := fun heq ↦ hnotMem (heq ▸ hother)
      simp [projectiveDominantHeckeFunction_apply_dominant_rankFour_of_ne
        k other a hne]
    exact hf.1 (heval.trans hsumZero)
  have hproductExpansion :
      f * HeckeFunction.projectiveDominantHeckeFunction k b =
        ∑ other ∈ weights,
          f (dominantCoweight k other.toDominant) •
            (HeckeFunction.projectiveDominantHeckeFunction k other *
              HeckeFunction.projectiveDominantHeckeFunction k b) := by
    calc
      f * HeckeFunction.projectiveDominantHeckeFunction k b =
          (∑ other ∈ weights,
            f (dominantCoweight k other.toDominant) •
              HeckeFunction.projectiveDominantHeckeFunction k other) *
            HeckeFunction.projectiveDominantHeckeFunction k b := by
              rw [← hexpansion]
      _ = ∑ other ∈ weights,
          f (dominantCoweight k other.toDominant) •
            (HeckeFunction.projectiveDominantHeckeFunction k other *
              HeckeFunction.projectiveDominantHeckeFunction k b) := by
            simp only [Finset.sum_mul, smul_mul_assoc]
  constructor
  · have htopEval :
        (f * HeckeFunction.projectiveDominantHeckeFunction k b)
            (dominantCoweight k
              (projectiveDominantCoweightAdd a b).toDominant) =
          f (dominantCoweight k a.toDominant) *
            (HeckeFunction.projectiveDominantHeckeFunction k a *
              HeckeFunction.projectiveDominantHeckeFunction k b)
              (dominantCoweight k
                (projectiveDominantCoweightAdd a b).toDominant) := by
      rw [hproductExpansion, HeckeFunction.finset_sum_apply,
        Finset.sum_eq_single a]
      · simp
      · intro other hother hne
        by_cases hcoefficient :
            f (dominantCoweight k other.toDominant) = 0
        · simp [hcoefficient]
        · have hotherGrade := hf.2 other hcoefficient hne
          have htargetGrade :
              rankFourCartanGrade
                  (projectiveDominantCoweightAdd other b) <
                rankFourCartanGrade
                  (projectiveDominantCoweightAdd a b) := by
            rw [rankFourCartanGrade_add, rankFourCartanGrade_add]
            omega
          have hconvolution :
              (HeckeFunction.projectiveDominantHeckeFunction k other *
                HeckeFunction.projectiveDominantHeckeFunction k b)
                (dominantCoweight k
                  (projectiveDominantCoweightAdd a b).toDominant) = 0 := by
            by_contra hnonzero
            by_cases heq : projectiveDominantCoweightAdd a b =
                projectiveDominantCoweightAdd other b
            · rw [heq] at htargetGrade
              omega
            · have hstrict :=
                rankFourCartanGrade_lt_add_of_mul_apply_ne_zero_of_ne
                  k (projectiveDominantCoweightAdd a b) other b hnonzero heq
              omega
          simp [hconvolution]
      · exact fun hnot ↦ (hnot haMem).elim
    rw [htopEval]
    exact mul_ne_zero hf.1
      (projectiveDominantHeckeFunction_mul_apply_add_ne_zero k a b)
  · intro output houtput houtputNe
    have hsumNe :
        (∑ other ∈ weights,
          (f (dominantCoweight k other.toDominant) •
            (HeckeFunction.projectiveDominantHeckeFunction k other *
              HeckeFunction.projectiveDominantHeckeFunction k b))
            (dominantCoweight k output.toDominant)) ≠ 0 := by
      rw [← HeckeFunction.finset_sum_apply, ← hproductExpansion]
      exact houtput
    obtain ⟨source, hsourceMem, hsourceTerm⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero hsumNe
    change f (dominantCoweight k source.toDominant) *
        (HeckeFunction.projectiveDominantHeckeFunction k source *
          HeckeFunction.projectiveDominantHeckeFunction k b)
          (dominantCoweight k output.toDominant) ≠ 0 at hsourceTerm
    have hsourceCoefficient := (mul_ne_zero_iff.mp hsourceTerm).1
    have hsourceConvolution := (mul_ne_zero_iff.mp hsourceTerm).2
    by_cases hsourceEq : source = a
    · subst source
      exact rankFourCartanGrade_lt_add_of_mul_apply_ne_zero_of_ne
        k output a b hsourceConvolution houtputNe
    · have hsourceGrade := hf.2 source hsourceCoefficient hsourceEq
      have houtputLe : rankFourCartanGrade output ≤
          rankFourCartanGrade (projectiveDominantCoweightAdd source b) := by
        by_cases heq : output = projectiveDominantCoweightAdd source b
        · rw [heq]
        · exact (rankFourCartanGrade_lt_add_of_mul_apply_ne_zero_of_ne
            k output source b hsourceConvolution heq).le
      rw [rankFourCartanGrade_add] at houtputLe
      rw [rankFourCartanGrade_add]
      omega
def rankFourMonomialWeight (m : Fin 3 →₀ ℕ) :
    ProjectiveDominantCoweight 3 :=
  rankFourProjectiveWeight (Finsupp.equivFunOnFinite m)
def rankFourHeckeMonomial
    (k : Type u) [Field k] [Finite k] (m : Fin 3 →₀ ℕ) :
    HeckeFunction k 4 :=
  rankFourFundamentalHeckeEval k (MvPolynomial.monomial m 1)
@[simp]
theorem rankFourMonomialWeight_zero :
    rankFourMonomialWeight 0 = projectiveDominantCoweightZero 3 := by
  apply ProjectiveDominantCoweight.ext
  funext i
  fin_cases i <;> simp [rankFourMonomialWeight, rankFourProjectiveWeight]
@[simp]
theorem rankFourHeckeMonomial_zero
    (k : Type u) [Field k] [Finite k] :
    rankFourHeckeMonomial k 0 = 1 := by
  simp [rankFourHeckeMonomial]
theorem rankFourMonomialWeight_add (m n : Fin 3 →₀ ℕ) :
    rankFourMonomialWeight (m + n) =
      projectiveDominantCoweightAdd
        (rankFourMonomialWeight m) (rankFourMonomialWeight n) := by
  apply ProjectiveDominantCoweight.ext
  funext i
  fin_cases i <;>
    simp [rankFourMonomialWeight, rankFourProjectiveWeight,
      projectiveDominantCoweightAdd] <;> omega
theorem rankFourHeckeMonomial_add
    (k : Type u) [Field k] [Finite k] (m n : Fin 3 →₀ ℕ) :
    rankFourHeckeMonomial k (m + n) =
      rankFourHeckeMonomial k m * rankFourHeckeMonomial k n := by
  rw [rankFourHeckeMonomial, rankFourHeckeMonomial,
    rankFourHeckeMonomial, ← map_mul, MvPolynomial.monomial_mul]
  simp
theorem rankFourMonomialWeight_single_one (color : Fin 3) :
    rankFourMonomialWeight (Finsupp.single color 1) =
      fundamentalProjectiveDominantCoweight 3 (color.val + 1) (by omega) := by
  apply ProjectiveDominantCoweight.ext
  funext i
  fin_cases color <;> fin_cases i <;>
    simp [rankFourMonomialWeight, rankFourProjectiveWeight,
      fundamentalProjectiveDominantCoweight, fundamentalDominantCoweight,
      Finsupp.equivFunOnFinite]
theorem rankFourHeckeMonomial_single_one
    (k : Type u) [Field k] [Finite k] (color : Fin 3) :
    rankFourHeckeMonomial k (Finsupp.single color 1) =
      HeckeFunction.projectiveDominantHeckeFunction k
        (fundamentalProjectiveDominantCoweight 3 (color.val + 1) (by omega)) := by
  rw [rankFourHeckeMonomial]
  have hmonomial : (MvPolynomial.monomial (Finsupp.single color 1) 1 :
      MvPolynomial (Fin 3) ℂ) = MvPolynomial.X color := by
    rw [← MvPolynomial.X_pow_eq_monomial]
    simp
  rw [hmonomial, rankFourFundamentalHeckeEval_X,
    ← HeckeFunction.projectiveDominantHeckeFunction_fundamental]
theorem hasRankFourLeadingCartanTerm_monomial_of_degree_lt
    (k : Type u) [Field k] [Finite k] (degree : ℕ) :
    ∀ m : Fin 3 →₀ ℕ,
      (m.sum fun _ exponent ↦ exponent) < degree →
      HasRankFourLeadingCartanTerm k
        (rankFourHeckeMonomial k m) (rankFourMonomialWeight m) := by
  classical
  induction degree with
  | zero =>
      intro m hdegree
      omega
  | succ degree ih =>
      intro m hdegree
      by_cases hm : m = 0
      · subst m
        simpa using hasRankFourLeadingCartanTerm_zero k
      · have hsupport : m.support.Nonempty :=
          Finsupp.support_nonempty_iff.mpr hm
        obtain ⟨color, hcolorSupport⟩ := hsupport
        have hcolor : m color ≠ 0 := Finsupp.mem_support_iff.mp hcolorSupport
        let previous := m - Finsupp.single color 1
        have hdecomp : m = previous + Finsupp.single color 1 := by
          ext i
          by_cases hi : i = color
          · subst i
            simp [previous]
            omega
          · simp [previous, hi]
        have hdegreeDecomp :
            (m.sum fun _ exponent ↦ exponent) =
              (previous.sum fun _ exponent ↦ exponent) + 1 := by
          rw [hdecomp, Finsupp.sum_add_index'
            (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
          simp
        have hpreviousDegree :
            (previous.sum fun _ exponent ↦ exponent) < degree := by
          omega
        have hprevious := ih previous hpreviousDegree
        have hstep := hprevious.mul_projectiveDominantHeckeFunction k
          (fundamentalProjectiveDominantCoweight 3 (color.val + 1) (by omega))
        rw [hdecomp, rankFourHeckeMonomial_add,
          rankFourMonomialWeight_add,
          rankFourHeckeMonomial_single_one,
          rankFourMonomialWeight_single_one]
        exact hstep
theorem hasRankFourLeadingCartanTerm_monomial
    (k : Type u) [Field k] [Finite k] (m : Fin 3 →₀ ℕ) :
    HasRankFourLeadingCartanTerm k
      (rankFourHeckeMonomial k m) (rankFourMonomialWeight m) := by
  exact hasRankFourLeadingCartanTerm_monomial_of_degree_lt k
    ((m.sum fun _ exponent ↦ exponent) + 1) m (by omega)
theorem rankFourMonomialWeight_injective :
    Function.Injective rankFourMonomialWeight := by
  intro m n hweight
  have hm := congrArg rankFourProjectiveMultiplicity hweight
  have hmRecover := rankFourProjectiveMultiplicityEquiv.right_inv
    (Finsupp.equivFunOnFinite m)
  have hnRecover := rankFourProjectiveMultiplicityEquiv.right_inv
    (Finsupp.equivFunOnFinite n)
  change rankFourProjectiveMultiplicity (rankFourProjectiveWeight
      (Finsupp.equivFunOnFinite m)) = Finsupp.equivFunOnFinite m at hmRecover
  change rankFourProjectiveMultiplicity (rankFourProjectiveWeight
      (Finsupp.equivFunOnFinite n)) = Finsupp.equivFunOnFinite n at hnRecover
  rw [rankFourMonomialWeight, hmRecover,
    rankFourMonomialWeight, hnRecover] at hm
  exact Finsupp.equivFunOnFinite.injective hm
theorem rankFourFundamentalHeckeEval_monomial
    (k : Type u) [Field k] [Finite k]
    (m : Fin 3 →₀ ℕ) (coefficient : ℂ) :
    rankFourFundamentalHeckeEval k
        (MvPolynomial.monomial m coefficient) =
      coefficient • rankFourHeckeMonomial k m := by
  rw [rankFourHeckeMonomial, rankFourFundamentalHeckeEval,
    MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  rw [Algebra.smul_def]
  simp
theorem rankFourFundamentalHeckeEval_eq_zero_iff
    (k : Type u) [Field k] [Finite k]
    (p : MvPolynomial (Fin 3) ℂ) :
    rankFourFundamentalHeckeEval k p = 0 ↔ p = 0 := by
  classical
  constructor
  · intro hp
    by_contra hpne
    have hsupport : p.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply hpne
      apply MvPolynomial.support_eq_empty.mp hempty
    obtain ⟨leading, hleadingMem, hmax⟩ :=
      Finset.exists_max_image p.support
        (fun m ↦ rankFourCartanGrade (rankFourMonomialWeight m)) hsupport
    have hexpansion : rankFourFundamentalHeckeEval k p =
        ∑ m ∈ p.support,
          p.coeff m • rankFourHeckeMonomial k m := by
      calc
        rankFourFundamentalHeckeEval k p =
            rankFourFundamentalHeckeEval k
              (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m)) := by
                congr 1
                exact MvPolynomial.as_sum p
        _ = ∑ m ∈ p.support,
              p.coeff m • rankFourHeckeMonomial k m := by
                rw [map_sum]
                apply Finset.sum_congr rfl
                intro m hm
                exact rankFourFundamentalHeckeEval_monomial k m (p.coeff m)
    have heval := congrArg
      (fun f : HeckeFunction k 4 ↦
        f (dominantCoweight k (rankFourMonomialWeight leading).toDominant))
      hexpansion
    rw [hp] at heval
    change (0 : HeckeFunction k 4)
        (dominantCoweight k (rankFourMonomialWeight leading).toDominant) =
      (∑ m ∈ p.support,
        p.coeff m • rankFourHeckeMonomial k m)
          (dominantCoweight k
            (rankFourMonomialWeight leading).toDominant) at heval
    rw [HeckeFunction.zero_apply,
      HeckeFunction.finset_sum_apply] at heval
    rw [Finset.sum_eq_single leading] at heval
    · have hleadingCoefficient : p.coeff leading ≠ 0 :=
        MvPolynomial.mem_support_iff.mp hleadingMem
      have hleadingValue :=
        (hasRankFourLeadingCartanTerm_monomial k leading).1
      simp only [HeckeFunction.smul_apply, smul_eq_mul] at heval
      exact (mul_ne_zero hleadingCoefficient hleadingValue) heval.symm
    · intro other hother hne
      have hotherValue : rankFourHeckeMonomial k other
          (dominantCoweight k
            (rankFourMonomialWeight leading).toDominant) = 0 := by
        by_contra hnonzero
        have hweightNe : rankFourMonomialWeight leading ≠
            rankFourMonomialWeight other := by
          intro heq
          exact hne (rankFourMonomialWeight_injective heq.symm)
        have hstrict :=
          (hasRankFourLeadingCartanTerm_monomial k other).2
            (rankFourMonomialWeight leading) hnonzero hweightNe
        have hle := hmax other hother
        omega
      simp [hotherValue]
    · exact fun hnot ↦ (hnot hleadingMem).elim
  · intro hp
    rw [hp, map_zero]
theorem rankFourFundamentalHeckeEval_injective
    (k : Type u) [Field k] [Finite k] :
    Function.Injective (rankFourFundamentalHeckeEval k) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply (rankFourFundamentalHeckeEval_eq_zero_iff k (p - q)).1
  rw [map_sub, hpq, sub_self]
noncomputable def rankThreeFundamentalHeckeAlgEquiv
    (k : Type u) [Field k] [Finite k] :
    MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] HeckeFunction k 3 :=
  AlgEquiv.ofBijective (rankThreeFundamentalHeckeEval k)
    ⟨rankThreeFundamentalHeckeEval_injective k,
      rankThreeFundamentalHeckeEval_surjective k⟩
noncomputable def rankFourFundamentalHeckeAlgEquiv
    (k : Type u) [Field k] [Finite k] :
    MvPolynomial (Fin 3) ℂ ≃ₐ[ℂ] HeckeFunction k 4 :=
  AlgEquiv.ofBijective (rankFourFundamentalHeckeEval k)
    ⟨rankFourFundamentalHeckeEval_injective k,
      rankFourFundamentalHeckeEval_surjective k⟩
end QEC.Coding.HighDimensionalExpander.SphericalHecke


