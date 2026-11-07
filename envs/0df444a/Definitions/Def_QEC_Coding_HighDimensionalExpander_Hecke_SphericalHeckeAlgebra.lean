-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
-- name    : QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:14:41.466988+00:00
-- url     : https://prove2.me/theorems/9844918e-0caa-4cb9-abe9-68b9bddb6bff
-- title:
--   Spherical Hecke Algebra
-- statement:
--   Definitions and structural lemmas for Spherical Hecke Algebra, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHeckeAlgebra.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Mathlib.Analysis.Convolution
import Mathlib.LinearAlgebra.Basis.Basic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_add
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_MatrixOrderLowerBound_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantCoweight_mem_doubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_mem_projectiveDominantDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_isCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_isOpen
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_iUnion_projectiveDominantDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_left_mul_mem_dominantDoubleCoset_iff
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_left_mul_mem_fundamentalDoubleCoset_iff
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_normalizedLocalHaarMeasure_isInvInvariant
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantDoubleCoset_isCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominantDoubleCoset_isOpen
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankFour_eq_of_doubleCoset_inter_nonempty
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveDominant_rankThree_eq_of_doubleCoset_inter_nonempty
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveTranspose_measurePreserving
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveTranspose_mem_dominantDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projectiveTranspose_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_right_mul_mem_dominantDoubleCoset_iff
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_right_mul_mem_fundamentalDoubleCoset_iff
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
open MeasureTheory Set Function
open scoped LocalTopology MatrixGroups Pointwise Convolution ComplexConjugate
universe u
abbrev HeckeGroup (k : Type u) [Field k] (d : ℕ) :=
  PGL(Fin d, LocalFunctionField k)
structure HeckeFunction (k : Type u) [Field k] [Finite k] (d : ℕ) where
  toFun : HeckeGroup k d → ℂ
  continuous_toFun : Continuous toFun
  hasCompactSupport_toFun : HasCompactSupport toFun
  left_invariant : ∀ h ∈ maximalCompact k d, ∀ x, toFun (h * x) = toFun x
  right_invariant : ∀ h ∈ maximalCompact k d, ∀ x, toFun (x * h) = toFun x
namespace HeckeFunction
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    FunLike (HeckeFunction k d) (HeckeGroup k d) ℂ where
  coe := toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl
def involution {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) : HeckeFunction k d where
  toFun x := conj (f x⁻¹)
  continuous_toFun :=
    continuous_star.comp (f.continuous_toFun.comp continuous_inv)
  hasCompactSupport_toFun := by
    have h := f.hasCompactSupport_toFun.comp_homeomorph
      (Homeomorph.inv (HeckeGroup k d))
    exact h.comp_left (map_zero (starRingEnd ℂ))
  left_invariant := by
    intro h hh x
    have hhinv : h⁻¹ ∈ maximalCompact k d :=
      (maximalCompact k d).inv_mem hh
    simp only [mul_inv_rev]
    exact congrArg conj (f.right_invariant h⁻¹ hhinv x⁻¹)
  right_invariant := by
    intro h hh x
    have hhinv : h⁻¹ ∈ maximalCompact k d :=
      (maximalCompact k d).inv_mem hh
    simp only [mul_inv_rev]
    exact congrArg conj (f.left_invariant h⁻¹ hhinv x⁻¹)
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Star (HeckeFunction k d) where
  star := involution
@[simp]
theorem star_apply {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) (x : HeckeGroup k d) :
    star f x = conj (f x⁻¹) :=
  rfl
@[ext]
theorem ext {k : Type u} [Field k] [Finite k] {d : ℕ}
    {f g : HeckeFunction k d} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr
  funext x
  exact h x
theorem continuous {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) : Continuous f :=
  f.continuous_toFun
theorem hasCompactSupport {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) : HasCompactSupport f :=
  f.hasCompactSupport_toFun
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Zero (HeckeFunction k d) where
  zero :=
    { toFun := 0
      continuous_toFun := continuous_zero
      hasCompactSupport_toFun := by simp [HasCompactSupport, tsupport]
      left_invariant := by simp
      right_invariant := by simp }
@[simp]
theorem zero_apply {k : Type u} [Field k] [Finite k] {d : ℕ}
    (x : HeckeGroup k d) : (0 : HeckeFunction k d) x = 0 :=
  rfl
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Add (HeckeFunction k d) where
  add f g :=
    { toFun := fun x ↦ f x + g x
      continuous_toFun := f.continuous.add g.continuous
      hasCompactSupport_toFun := f.hasCompactSupport.add g.hasCompactSupport
      left_invariant := by
        intro h hh x
        change f.toFun (h * x) + g.toFun (h * x) =
          f.toFun x + g.toFun x
        rw [f.left_invariant h hh x, g.left_invariant h hh x]
      right_invariant := by
        intro h hh x
        change f.toFun (x * h) + g.toFun (x * h) =
          f.toFun x + g.toFun x
        rw [f.right_invariant h hh x, g.right_invariant h hh x] }
@[simp]
theorem add_apply {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) (x : HeckeGroup k d) :
    (f + g) x = f x + g x :=
  rfl
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Neg (HeckeFunction k d) where
  neg f :=
    { toFun := fun x ↦ -f x
      continuous_toFun := f.continuous.neg
      hasCompactSupport_toFun := by
        simpa [HasCompactSupport, tsupport] using f.hasCompactSupport
      left_invariant := by
        intro h hh x
        change -f.toFun (h * x) = -f.toFun x
        rw [f.left_invariant h hh x]
      right_invariant := by
        intro h hh x
        change -f.toFun (x * h) = -f.toFun x
        rw [f.right_invariant h hh x] }
@[simp]
theorem neg_apply {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) (x : HeckeGroup k d) :
    (-f) x = -f x :=
  rfl
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Sub (HeckeFunction k d) where
  sub f g := f + -g
@[simp]
theorem sub_apply {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) (x : HeckeGroup k d) :
    (f - g) x = f x - g x :=
  rfl
theorem coe_zero {k : Type u} [Field k] [Finite k] {d : ℕ} :
    ⇑(0 : HeckeFunction k d) = (0 : HeckeGroup k d → ℂ) :=
  rfl
theorem coe_add {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) : ⇑(f + g) = ⇑f + ⇑g :=
  rfl
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    AddCommGroup (HeckeFunction k d) where
  add := (· + ·)
  add_assoc f g h := by ext x; simp [add_assoc]
  zero := 0
  zero_add f := by ext x; simp
  add_zero f := by ext x; simp
  nsmul := nsmulRec
  neg := Neg.neg
  sub := Sub.sub
  sub_eq_add_neg _ _ := rfl
  zsmul := zsmulRec
  neg_add_cancel f := by ext x; simp
  add_comm f g := by ext x; simp [add_comm]
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    SMul ℂ (HeckeFunction k d) where
  smul c f :=
    { toFun := fun x ↦ c • f x
      continuous_toFun := f.continuous.const_smul c
      hasCompactSupport_toFun := by
        have hsubset : support (fun x ↦ c • f x) ⊆ tsupport f := by
          intro x hx
          apply subset_closure
          apply mem_support.2
          intro hfx
          apply hx
          simp [hfx]
        exact f.hasCompactSupport.of_isClosed_subset isClosed_closure
          (closure_minimal hsubset f.hasCompactSupport.isClosed)
      left_invariant := by
        intro h hh x
        change c • f.toFun (h * x) = c • f.toFun x
        rw [f.left_invariant h hh x]
      right_invariant := by
        intro h hh x
        change c • f.toFun (x * h) = c • f.toFun x
        rw [f.right_invariant h hh x] }
@[simp]
theorem smul_apply {k : Type u} [Field k] [Finite k] {d : ℕ}
    (c : ℂ) (f : HeckeFunction k d) (x : HeckeGroup k d) :
    (c • f) x = c • f x :=
  rfl
theorem coe_smul {k : Type u} [Field k] [Finite k] {d : ℕ}
    (c : ℂ) (f : HeckeFunction k d) : ⇑(c • f) = c • ⇑f :=
  rfl
@[simp]
theorem finset_sum_apply {k : Type u} [Field k] [Finite k] {d : ℕ}
    {ι : Type*} (s : Finset ι) (g : ι → HeckeFunction k d)
    (x : HeckeGroup k d) :
    (∑ i ∈ s, g i) x = ∑ i ∈ s, g i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Module ℂ (HeckeFunction k d) := fast_instance%
  Function.Injective.module ℂ
    ⟨⟨fun f ↦ (f : HeckeGroup k d → ℂ), coe_zero⟩, coe_add⟩
    DFunLike.coe_injective coe_smul
theorem integrable {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) :
    Integrable f (normalizedLocalHaarMeasure k d) :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
def rawConvolution {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) :
    HeckeGroup k d → ℂ :=
  fun x ↦ ∫ t, f t * g (t⁻¹ * x) ∂(normalizedLocalHaarMeasure k d)
theorem rawConvolution_apply {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) (x : HeckeGroup k d) :
    rawConvolution f g x =
      ∫ t, f t * g (t⁻¹ * x) ∂(normalizedLocalHaarMeasure k d) :=
  rfl
theorem integrable_convolutionIntegrand
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) (x : HeckeGroup k d) :
    Integrable (fun t ↦ f t * g (t⁻¹ * x))
      (normalizedLocalHaarMeasure k d) := by
  have hg : Continuous (fun t ↦ g (t⁻¹ * x)) :=
    g.continuous.comp (continuous_inv.mul continuous_const)
  have hfg : Continuous (fun t ↦ f t * g (t⁻¹ * x)) :=
    f.continuous.mul hg
  have hsupport : HasCompactSupport (fun t ↦ f t * g (t⁻¹ * x)) :=
    f.hasCompactSupport.mul_right
  exact hfg.integrable_of_hasCompactSupport hsupport
theorem rawConvolution_right_invariant
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) (h : HeckeGroup k d)
    (hh : h ∈ maximalCompact k d) (x : HeckeGroup k d) :
    rawConvolution f g (x * h) = rawConvolution f g x := by
  apply integral_congr_ae
  filter_upwards with t
  rw [← mul_assoc]
  exact congrArg (fun z ↦ f t * z) (g.right_invariant h hh (t⁻¹ * x))
theorem rawConvolution_left_invariant
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) (h : HeckeGroup k d)
    (hh : h ∈ maximalCompact k d) (x : HeckeGroup k d) :
    rawConvolution f g (h * x) = rawConvolution f g x := by
  let F : HeckeGroup k d → ℂ :=
    fun t ↦ f t * g (t⁻¹ * (h * x))
  calc
    rawConvolution f g (h * x) = ∫ t, F t ∂(normalizedLocalHaarMeasure k d) := rfl
    _ = ∫ t, F (h * t) ∂(normalizedLocalHaarMeasure k d) :=
      (integral_mul_left_eq_self F h).symm
    _ = rawConvolution f g x := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [F, mul_inv_rev]
      change f.toFun (h * t) * g.toFun (t⁻¹ * h⁻¹ * (h * x)) =
        f.toFun t * g.toFun (t⁻¹ * x)
      rw [f.left_invariant h hh t]
      simp [mul_assoc]
theorem continuous_rawConvolution
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) : Continuous (rawConvolution f g) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hUcompact, hUx⟩ := exists_compact_mem_nhds x
  let C : Set (HeckeGroup k d) := U * (tsupport g)⁻¹
  have hCcompact : IsCompact C := hUcompact.mul g.hasCompactSupport.inv
  let p : HeckeGroup k d → HeckeGroup k d → ℂ :=
    fun x t ↦ g (t⁻¹ * x)
  have hpcontinuous : Continuous p.uncurry := by
    unfold p Function.uncurry
    exact g.continuous.comp
      ((continuous_inv.comp continuous_snd).mul continuous_fst)
  have hpzero : ∀ a, ∀ t, a ∈ U → t ∉ C → p a t = 0 := by
    intro a t ha ht
    change g (t⁻¹ * a) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply ht
    change t ∈ U * (tsupport g)⁻¹
    rw [Set.mem_mul]
    refine ⟨a, ha, (t⁻¹ * a)⁻¹, ?_, ?_⟩
    · exact Set.mem_inv.2 (by simpa using hmem)
    · simp
  have hcontinuousOn : ContinuousOn (rawConvolution f g) U := by
    exact continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
      (ContinuousLinearMap.mul ℂ ℂ) hCcompact hpcontinuous.continuousOn
        hpzero f.integrable.integrableOn
  exact hcontinuousOn.continuousAt hUx
theorem support_rawConvolution_subset
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) :
    support (rawConvolution f g) ⊆ tsupport f * tsupport g := by
  intro x hx
  by_contra hxprod
  apply hx
  rw [rawConvolution_apply]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  by_cases hft : f t = 0
  · simp [hft]
  by_cases hgt : g (t⁻¹ * x) = 0
  · simp [hgt]
  exfalso
  apply hxprod
  rw [Set.mem_mul]
  refine ⟨t, subset_closure (mem_support.2 hft), t⁻¹ * x,
    subset_closure (mem_support.2 hgt), ?_⟩
  simp
theorem hasCompactSupport_rawConvolution
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) : HasCompactSupport (rawConvolution f g) := by
  have hcompact : IsCompact (tsupport f * tsupport g) :=
    f.hasCompactSupport.mul g.hasCompactSupport
  exact hcompact.of_isClosed_subset isClosed_closure
    (closure_minimal (support_rawConvolution_subset f g) hcompact.isClosed)
def convolution {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) : HeckeFunction k d where
  toFun := rawConvolution f g
  continuous_toFun := continuous_rawConvolution f g
  hasCompactSupport_toFun := hasCompactSupport_rawConvolution f g
  left_invariant := rawConvolution_left_invariant f g
  right_invariant := rawConvolution_right_invariant f g
@[simp]
theorem convolution_apply {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) (x : HeckeGroup k d) :
    convolution f g x =
      ∫ t, f t * g (t⁻¹ * x) ∂(normalizedLocalHaarMeasure k d) :=
  rfl
theorem convolution_add_left {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g h : HeckeFunction k d) :
    convolution (f + g) h = convolution f h + convolution g h := by
  ext x
  simp only [convolution_apply, add_apply]
  rw [← integral_add
    (integrable_convolutionIntegrand f h x)
    (integrable_convolutionIntegrand g h x)]
  apply integral_congr_ae
  filter_upwards with t
  ring
theorem convolution_add_right {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g h : HeckeFunction k d) :
    convolution f (g + h) = convolution f g + convolution f h := by
  ext x
  simp only [convolution_apply, add_apply]
  rw [← integral_add
    (integrable_convolutionIntegrand f g x)
    (integrable_convolutionIntegrand f h x)]
  apply integral_congr_ae
  filter_upwards with t
  ring
theorem convolution_smul_left {k : Type u} [Field k] [Finite k] {d : ℕ}
    (c : ℂ) (f g : HeckeFunction k d) :
    convolution (c • f) g = c • convolution f g := by
  ext x
  simp only [convolution_apply, smul_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul]
  ring
theorem convolution_smul_right {k : Type u} [Field k] [Finite k] {d : ℕ}
    (c : ℂ) (f g : HeckeFunction k d) :
    convolution f (c • g) = c • convolution f g := by
  ext x
  simp only [convolution_apply, smul_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul]
  ring
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Mul (HeckeFunction k d) where
  mul := convolution
@[simp]
theorem mul_apply {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) (x : HeckeGroup k d) :
    (f * g) x = ∫ t, f t * g (t⁻¹ * x)
      ∂(normalizedLocalHaarMeasure k d) :=
  rfl
theorem mul_add {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g h : HeckeFunction k d) : f * (g + h) = f * g + f * h :=
  convolution_add_right f g h
theorem add_mul {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g h : HeckeFunction k d) : (f + g) * h = f * h + g * h :=
  convolution_add_left f g h
theorem smul_mul_assoc {k : Type u} [Field k] [Finite k] {d : ℕ}
    (c : ℂ) (f g : HeckeFunction k d) : (c • f) * g = c • (f * g) :=
  convolution_smul_left c f g
theorem mul_smul_comm {k : Type u} [Field k] [Finite k] {d : ℕ}
    (c : ℂ) (f g : HeckeFunction k d) : f * (c • g) = c • (f * g) :=
  convolution_smul_right c f g
theorem zero_mul {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) : (0 : HeckeFunction k d) * f = 0 := by
  ext x
  simp [mul_apply]
theorem mul_zero {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) : f * (0 : HeckeFunction k d) = 0 := by
  ext x
  simp [mul_apply]
theorem star_mul_convolution
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g : HeckeFunction k d) : star (f * g) = star g * star f := by
  ext x
  let F : HeckeGroup k d → ℂ := fun t =>
    conj (g t⁻¹) * conj (f ((t⁻¹ * x)⁻¹))
  calc
    star (f * g) x =
        conj (∫ t, f t * g (t⁻¹ * x⁻¹)
          ∂normalizedLocalHaarMeasure k d) := by
      simp only [star_apply, mul_apply]
    _ = ∫ t, conj (f t * g (t⁻¹ * x⁻¹))
          ∂normalizedLocalHaarMeasure k d := by
      rw [integral_conj]
    _ = ∫ t, F (x * t) ∂normalizedLocalHaarMeasure k d := by
      apply integral_congr_ae
      filter_upwards with t
      simp [F, mul_comm]
    _ = ∫ t, F t ∂normalizedLocalHaarMeasure k d :=
      integral_mul_left_eq_self F x
    _ = (star g * star f) x := by
      apply integral_congr_ae
      filter_upwards with t
      simp [F]
theorem convolution_assoc
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f g h : HeckeFunction k d) : (f * g) * h = f * (g * h) := by
  ext x
  let mu := normalizedLocalHaarMeasure k d
  let J : HeckeGroup k d × HeckeGroup k d → ℂ :=
    fun p ↦ f p.2 * g (p.2⁻¹ * p.1) * h (p.1⁻¹ * x)
  have hJcontinuous : Continuous J := by
    exact ((f.continuous.comp continuous_snd).mul
      (g.continuous.comp
        ((continuous_inv.comp continuous_snd).mul continuous_fst))).mul
      (h.continuous.comp ((continuous_inv.comp continuous_fst).mul continuous_const))
  have hJsupport : support J ⊆
      (tsupport f * tsupport g) ×ˢ tsupport f := by
    intro p hp
    have hprod : f p.2 * g (p.2⁻¹ * p.1) ≠ 0 ∧
        h (p.1⁻¹ * x) ≠ 0 := mul_ne_zero_iff.mp hp
    have hfg : f p.2 ≠ 0 ∧ g (p.2⁻¹ * p.1) ≠ 0 :=
      mul_ne_zero_iff.mp hprod.1
    have hft : p.2 ∈ tsupport f :=
      subset_closure (mem_support.2 hfg.1)
    have hgu : p.2⁻¹ * p.1 ∈ tsupport g :=
      subset_closure (mem_support.2 hfg.2)
    constructor
    · rw [Set.mem_mul]
      exact ⟨p.2, hft, p.2⁻¹ * p.1, hgu, by simp⟩
    · exact hft
  have hJcompact : HasCompactSupport J := by
    have hcompact : IsCompact ((tsupport f * tsupport g) ×ˢ tsupport f) :=
      (f.hasCompactSupport.mul g.hasCompactSupport).prod f.hasCompactSupport
    exact hcompact.of_isClosed_subset isClosed_closure
      (closure_minimal hJsupport hcompact.isClosed)
  have hJintegrable : Integrable J (mu.prod mu) :=
    hJcontinuous.integrable_of_hasCompactSupport hJcompact
  change (∫ s, (∫ t, f t * g (t⁻¹ * s) ∂mu) * h (s⁻¹ * x) ∂mu) =
    ∫ t, f t * (∫ u, g u * h (u⁻¹ * (t⁻¹ * x)) ∂mu) ∂mu
  calc
    (∫ s, (∫ t, f t * g (t⁻¹ * s) ∂mu) * h (s⁻¹ * x) ∂mu) =
        ∫ s, ∫ t, J (s, t) ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards with s
      exact (integral_mul_const (h (s⁻¹ * x))
        (fun t ↦ f t * g (t⁻¹ * s))).symm
    _ = ∫ t, ∫ s, J (s, t) ∂mu ∂mu :=
      integral_integral_swap hJintegrable
    _ = ∫ t, f t * (∫ u, g u * h (u⁻¹ * (t⁻¹ * x)) ∂mu) ∂mu := by
      apply integral_congr_ae
      filter_upwards with t
      calc
        (∫ s, J (s, t) ∂mu) = ∫ u, J (t * u, t) ∂mu :=
          (integral_mul_left_eq_self (fun s ↦ J (s, t)) t).symm
        _ = f t * (∫ u, g u * h (u⁻¹ * (t⁻¹ * x)) ∂mu) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with u
          simp [J, mul_assoc]
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    NonUnitalRing (HeckeFunction k d) where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := convolution_assoc
def compactUnitHeckeFunction
    (k : Type u) [Field k] [Finite k] (d : ℕ) : HeckeFunction k d where
  toFun := (maximalCompact k d : Set (HeckeGroup k d)).indicator (fun _ ↦ 1)
  continuous_toFun := by
    have hclopen : IsClopen (maximalCompact k d : Set (HeckeGroup k d)) :=
      ⟨(maximalCompact_isCompact k d).isClosed, maximalCompact_isOpen k d⟩
    exact hclopen.continuous_indicator continuous_const
  hasCompactSupport_toFun := by
    have hcompact := maximalCompact_isCompact k d
    exact hcompact.of_isClosed_subset isClosed_closure
      (closure_minimal (by
        intro x hx
        by_contra hnot
        exact hx (Set.indicator_of_notMem hnot _)) hcompact.isClosed)
  left_invariant := by
    intro h hh x
    have hiff : h * x ∈ maximalCompact k d ↔ x ∈ maximalCompact k d :=
      (maximalCompact k d).mul_mem_cancel_left hh
    by_cases hx : x ∈ maximalCompact k d
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]
    · have hhx : h * x ∉ maximalCompact k d := fun hmem ↦ hx (hiff.1 hmem)
      simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hhx]
  right_invariant := by
    intro h hh x
    have hiff : x * h ∈ maximalCompact k d ↔ x ∈ maximalCompact k d :=
      (maximalCompact k d).mul_mem_cancel_right hh
    by_cases hx : x ∈ maximalCompact k d
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]
    · have hxh : x * h ∉ maximalCompact k d := fun hmem ↦ hx (hiff.1 hmem)
      simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxh]
@[simp]
theorem compactUnitHeckeFunction_apply
    (k : Type u) [Field k] [Finite k] (d : ℕ) (x : HeckeGroup k d) :
    compactUnitHeckeFunction k d x =
      (maximalCompact k d : Set (HeckeGroup k d)).indicator (fun _ ↦ 1) x :=
  rfl
theorem compactUnitHeckeFunction_mul
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) : compactUnitHeckeFunction k d * f = f := by
  ext x
  rw [mul_apply]
  let K : Set (HeckeGroup k d) := maximalCompact k d
  have hfun : (fun t ↦ compactUnitHeckeFunction k d t * f (t⁻¹ * x)) =
      K.indicator (fun _ ↦ f x) := by
    funext t
    by_cases ht : t ∈ maximalCompact k d
    · have htinv : t⁻¹ ∈ maximalCompact k d := (maximalCompact k d).inv_mem ht
      change compactUnitHeckeFunction k d t * f.toFun (t⁻¹ * x) = _
      rw [f.left_invariant t⁻¹ htinv x]
      simp [K, compactUnitHeckeFunction_apply, ht]
      rfl
    · simp [K, compactUnitHeckeFunction_apply, ht]
  rw [hfun, integral_indicator_const _ (maximalCompact_isOpen k d).measurableSet]
  have hreal : (normalizedLocalHaarMeasure k d).real K = 1 := by
    rw [Measure.real, normalizedLocalHaarMeasure_maximalCompact,
      ENNReal.toReal_one]
  rw [hreal]
  simp
theorem mul_compactUnitHeckeFunction
    {k : Type u} [Field k] [Finite k] {d : ℕ}
    (f : HeckeFunction k d) : f * compactUnitHeckeFunction k d = f := by
  ext x
  rw [mul_apply]
  let K : Set (HeckeGroup k d) := maximalCompact k d
  let F : HeckeGroup k d → ℂ := fun t ↦
    f t * compactUnitHeckeFunction k d (t⁻¹ * x)
  calc
    (∫ t, f t * compactUnitHeckeFunction k d (t⁻¹ * x)
        ∂normalizedLocalHaarMeasure k d) =
        ∫ u, F (x * u) ∂normalizedLocalHaarMeasure k d := by
          exact (integral_mul_left_eq_self F x).symm
    _ = ∫ u, K.indicator (fun _ ↦ f x) u
        ∂normalizedLocalHaarMeasure k d := by
          congr 1
          funext u
          by_cases hu : u ∈ maximalCompact k d
          · have huinv : u⁻¹ ∈ maximalCompact k d :=
              (maximalCompact k d).inv_mem hu
            change f.toFun (x * u) *
              compactUnitHeckeFunction k d ((x * u)⁻¹ * x) = _
            rw [f.right_invariant u hu x]
            simp [K, compactUnitHeckeFunction_apply, hu, huinv]
            rfl
          · have huinv : u⁻¹ ∉ maximalCompact k d := by
              intro h
              exact hu (by simpa using (maximalCompact k d).inv_mem h)
            simp [F, K, compactUnitHeckeFunction_apply, hu, huinv]
    _ = f x := by
      rw [integral_indicator_const _ (maximalCompact_isOpen k d).measurableSet]
      have hreal : (normalizedLocalHaarMeasure k d).real K = 1 := by
        rw [Measure.real, normalizedLocalHaarMeasure_maximalCompact,
          ENNReal.toReal_one]
      rw [hreal]
      simp
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    One (HeckeFunction k d) where
  one := compactUnitHeckeFunction k d
@[simp]
theorem one_apply
    {k : Type u} [Field k] [Finite k] {d : ℕ} (x : HeckeGroup k d) :
    (1 : HeckeFunction k d) x =
      (maximalCompact k d : Set (HeckeGroup k d)).indicator (fun _ ↦ 1) x :=
  rfl
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Monoid (HeckeFunction k d) where
  mul := Mul.mul
  one := compactUnitHeckeFunction k d
  mul_assoc := convolution_assoc
  one_mul := compactUnitHeckeFunction_mul
  mul_one := mul_compactUnitHeckeFunction
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Semiring (HeckeFunction k d) where
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := mul_add
  right_distrib := add_mul
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Ring (HeckeFunction k d) where
  sub_eq_add_neg _ _ := rfl
  zsmul := zsmulRec
  neg_add_cancel f := by ext x; simp
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    StarRing (HeckeFunction k d) where
  star_involutive f := by
    ext x
    simp
  star_mul := star_mul_convolution
  star_add f g := by
    ext x
    simp
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Algebra ℂ (HeckeFunction k d) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm
instance (k : Type u) [Field k] [Finite k] (d : ℕ) :
    StarModule ℂ (HeckeFunction k d) where
  star_smul c f := by
    ext x
    simp
def fundamentalHeckeFunction
    (k : Type u) [Field k] [Finite k] (d r : ℕ) : HeckeFunction k d where
  toFun := (fundamentalDoubleCoset k d r).indicator (fun _ ↦ 1)
  continuous_toFun := by
    have hclopen : IsClopen (fundamentalDoubleCoset k d r) :=
      ⟨(fundamentalDoubleCoset_isCompact k d r).isClosed,
        fundamentalDoubleCoset_isOpen k d r⟩
    exact hclopen.continuous_indicator continuous_const
  hasCompactSupport_toFun := by
    have hcompact := fundamentalDoubleCoset_isCompact k d r
    exact hcompact.of_isClosed_subset isClosed_closure
      (closure_minimal (by
        intro x hx
        by_contra hnot
        exact hx (Set.indicator_of_notMem hnot _)) hcompact.isClosed)
  left_invariant := by
    intro h hh x
    have hiff := left_mul_mem_fundamentalDoubleCoset_iff k d r (x := x) hh
    by_cases hx : x ∈ fundamentalDoubleCoset k d r
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]
    · have hhx : h * x ∉ fundamentalDoubleCoset k d r :=
        fun hmem ↦ hx (hiff.1 hmem)
      simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hhx]
  right_invariant := by
    intro h hh x
    have hiff := right_mul_mem_fundamentalDoubleCoset_iff k d r (x := x) hh
    by_cases hx : x ∈ fundamentalDoubleCoset k d r
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]
    · have hhx : x * h ∉ fundamentalDoubleCoset k d r :=
        fun hmem ↦ hx (hiff.1 hmem)
      simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hhx]
@[simp]
theorem fundamentalHeckeFunction_apply
    (k : Type u) [Field k] [Finite k] (d r : ℕ) (x : HeckeGroup k d) :
    fundamentalHeckeFunction k d r x =
      (fundamentalDoubleCoset k d r).indicator (fun _ ↦ 1) x :=
  rfl
def projectiveDominantHeckeFunction
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) : HeckeFunction k (n + 1) where
  toFun := (projectiveDominantDoubleCoset k weight).indicator (fun _ ↦ 1)
  continuous_toFun := by
    have hclopen : IsClopen (projectiveDominantDoubleCoset k weight) :=
      ⟨(projectiveDominantDoubleCoset_isCompact k weight).isClosed,
        projectiveDominantDoubleCoset_isOpen k weight⟩
    exact hclopen.continuous_indicator continuous_const
  hasCompactSupport_toFun := by
    have hcompact := projectiveDominantDoubleCoset_isCompact k weight
    exact hcompact.of_isClosed_subset isClosed_closure
      (closure_minimal (by
        intro x hx
        by_contra hnot
        exact hx (Set.indicator_of_notMem hnot _)) hcompact.isClosed)
  left_invariant := by
    intro h hh x
    have hiff := left_mul_mem_dominantDoubleCoset_iff
      k weight.toDominant (x := x) hh
    change (dominantDoubleCoset k weight.toDominant).indicator
      (fun _ ↦ 1) (h * x) =
        (dominantDoubleCoset k weight.toDominant).indicator (fun _ ↦ 1) x
    by_cases hx : x ∈ dominantDoubleCoset k weight.toDominant
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]
    · have hhx : h * x ∉ dominantDoubleCoset k weight.toDominant :=
        fun hmem ↦ hx (hiff.1 hmem)
      simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hhx]
  right_invariant := by
    intro h hh x
    have hiff := right_mul_mem_dominantDoubleCoset_iff
      k weight.toDominant (x := x) hh
    change (dominantDoubleCoset k weight.toDominant).indicator
      (fun _ ↦ 1) (x * h) =
        (dominantDoubleCoset k weight.toDominant).indicator (fun _ ↦ 1) x
    by_cases hx : x ∈ dominantDoubleCoset k weight.toDominant
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]
    · have hhx : x * h ∉ dominantDoubleCoset k weight.toDominant :=
        fun hmem ↦ hx (hiff.1 hmem)
      simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hhx]
@[simp]
theorem projectiveDominantHeckeFunction_apply
    (k : Type u) [Field k] [Finite k] {n : ℕ}
    (weight : ProjectiveDominantCoweight n) (x : HeckeGroup k (n + 1)) :
    projectiveDominantHeckeFunction k weight x =
      (projectiveDominantDoubleCoset k weight).indicator (fun _ ↦ 1) x :=
  rfl
theorem eq_dominantCoweight_of_mem_projectiveDominantDoubleCoset
    {k : Type u} [Field k] [Finite k] {n : ℕ}
    (f : HeckeFunction k (n + 1)) (weight : ProjectiveDominantCoweight n)
    {x : HeckeGroup k (n + 1)}
    (hx : x ∈ projectiveDominantDoubleCoset k weight) :
    f x = f (dominantCoweight k weight.toDominant) := by
  rw [projectiveDominantDoubleCoset, dominantDoubleCoset] at hx
  rcases hx with ⟨y, hy, right, hright, rfl⟩
  rcases hy with ⟨left, hleft, diagonal, hdiagonal, rfl⟩
  have hdiag : diagonal = dominantCoweight k weight.toDominant :=
    Set.mem_singleton_iff.mp hdiagonal
  subst diagonal
  change f.toFun ((left * dominantCoweight k weight.toDominant) * right) =
    f.toFun (dominantCoweight k weight.toDominant)
  calc
    _ = f.toFun (left * dominantCoweight k weight.toDominant) :=
      f.right_invariant right hright _
    _ = f.toFun (dominantCoweight k weight.toDominant) :=
      f.left_invariant left hleft _
theorem exists_finset_projectiveDominantDoubleCoset_cover_tsupport
    {k : Type u} [Field k] [Finite k] {n : ℕ}
    (f : HeckeFunction k (n + 1)) :
    ∃ weights : Finset (ProjectiveDominantCoweight n),
      tsupport f ⊆ ⋃ weight ∈ weights,
        projectiveDominantDoubleCoset k weight := by
  apply f.hasCompactSupport.elim_finite_subcover
    (fun weight ↦ projectiveDominantDoubleCoset k weight)
  · exact fun weight ↦ projectiveDominantDoubleCoset_isOpen k weight
  · rw [iUnion_projectiveDominantDoubleCoset]
    exact Set.subset_univ _
theorem exists_projectiveDominantHeckeFunction_expansion_of_unique
    {k : Type u} [Field k] [Finite k] {n : ℕ}
    (f : HeckeFunction k (n + 1))
    (hunique : ∀ (a b : ProjectiveDominantCoweight n),
      (projectiveDominantDoubleCoset k a ∩
        projectiveDominantDoubleCoset k b).Nonempty → a = b) :
    ∃ weights : Finset (ProjectiveDominantCoweight n),
      f = ∑ weight ∈ weights,
        f (dominantCoweight k weight.toDominant) •
          projectiveDominantHeckeFunction k weight := by
  obtain ⟨weights, hcover⟩ :=
    exists_finset_projectiveDominantDoubleCoset_cover_tsupport f
  refine ⟨weights, ?_⟩
  ext x
  by_cases hfx : f x = 0
  · rw [hfx]
    rw [finset_sum_apply]
    symm
    apply Finset.sum_eq_zero
    intro weight hweight
    by_cases hx : x ∈ projectiveDominantDoubleCoset k weight
    · have hconstant :=
        eq_dominantCoweight_of_mem_projectiveDominantDoubleCoset
          f weight hx
      simp [← hconstant, hfx]
    · simp [projectiveDominantHeckeFunction_apply, hx]
  · have hsupport : x ∈ support f := mem_support.2 hfx
    have htsupport : x ∈ tsupport f := subset_closure hsupport
    have hxcover := hcover htsupport
    rw [Set.mem_iUnion] at hxcover
    obtain ⟨weight, hxcover⟩ := hxcover
    rw [Set.mem_iUnion] at hxcover
    obtain ⟨hweight, hx⟩ := hxcover
    rw [finset_sum_apply]
    rw [Finset.sum_eq_single weight]
    · rw [smul_apply, projectiveDominantHeckeFunction_apply,
        Set.indicator_of_mem hx, smul_eq_mul, mul_one]
      exact eq_dominantCoweight_of_mem_projectiveDominantDoubleCoset
        f weight hx
    · intro other hother hne
      have hxother : x ∉ projectiveDominantDoubleCoset k other := by
        intro hxother
        have heq := hunique weight other ⟨x, hx, hxother⟩
        exact hne heq.symm
      rw [smul_apply, projectiveDominantHeckeFunction_apply,
        Set.indicator_of_notMem hxother, smul_zero]
    · exact fun hnot ↦ (hnot hweight).elim
theorem exists_projectiveDominantHeckeFunction_expansion_rankThree
    {k : Type u} [Field k] [Finite k] (f : HeckeFunction k 3) :
    ∃ weights : Finset (ProjectiveDominantCoweight 2),
      f = ∑ weight ∈ weights,
        f (dominantCoweight k weight.toDominant) •
          projectiveDominantHeckeFunction k weight := by
  exact exists_projectiveDominantHeckeFunction_expansion_of_unique f
    (projectiveDominant_rankThree_eq_of_doubleCoset_inter_nonempty k)
theorem exists_projectiveDominantHeckeFunction_expansion_rankFour
    {k : Type u} [Field k] [Finite k] (f : HeckeFunction k 4) :
    ∃ weights : Finset (ProjectiveDominantCoweight 3),
      f = ∑ weight ∈ weights,
        f (dominantCoweight k weight.toDominant) •
          projectiveDominantHeckeFunction k weight := by
  exact exists_projectiveDominantHeckeFunction_expansion_of_unique f
    (projectiveDominant_rankFour_eq_of_doubleCoset_inter_nonempty k)
theorem span_projectiveDominantHeckeFunction_rankThree
    (k : Type u) [Field k] [Finite k] :
    Submodule.span ℂ
      (Set.range (projectiveDominantHeckeFunction k :
        ProjectiveDominantCoweight 2 → HeckeFunction k 3)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro f
  obtain ⟨weights, hf⟩ :=
    exists_projectiveDominantHeckeFunction_expansion_rankThree f
  rw [hf]
  exact Submodule.sum_mem _ fun weight _ ↦
    Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self weight))
theorem span_projectiveDominantHeckeFunction_rankFour
    (k : Type u) [Field k] [Finite k] :
    Submodule.span ℂ
      (Set.range (projectiveDominantHeckeFunction k :
        ProjectiveDominantCoweight 3 → HeckeFunction k 4)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro f
  obtain ⟨weights, hf⟩ :=
    exists_projectiveDominantHeckeFunction_expansion_rankFour f
  rw [hf]
  exact Submodule.sum_mem _ fun weight _ ↦
    Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self weight))
theorem linearIndependent_projectiveDominantHeckeFunction_of_unique
    {k : Type u} [Field k] [Finite k] {n : ℕ}
    (hunique : ∀ (a b : ProjectiveDominantCoweight n),
      (projectiveDominantDoubleCoset k a ∩
        projectiveDominantDoubleCoset k b).Nonempty → a = b) :
    LinearIndependent ℂ
      (projectiveDominantHeckeFunction k :
        ProjectiveDominantCoweight n → HeckeFunction k (n + 1)) := by
  rw [linearIndependent_iff']
  intro weights coefficient hsum weight hweight
  have heval := congrArg
    (fun f : HeckeFunction k (n + 1) ↦
      f (dominantCoweight k weight.toDominant)) hsum
  change (∑ i ∈ weights,
      coefficient i • projectiveDominantHeckeFunction k i)
        (dominantCoweight k weight.toDominant) =
      (0 : HeckeFunction k (n + 1))
        (dominantCoweight k weight.toDominant) at heval
  rw [finset_sum_apply, Finset.sum_eq_single weight] at heval
  · have hmem : dominantCoweight k weight.toDominant ∈
        projectiveDominantDoubleCoset k weight := by
      exact dominantCoweight_mem_doubleCoset k weight.toDominant
    simpa [projectiveDominantHeckeFunction_apply, hmem] using heval
  · intro other hother hne
    have hnot : dominantCoweight k weight.toDominant ∉
        projectiveDominantDoubleCoset k other := by
      intro hothermem
      have hself : dominantCoweight k weight.toDominant ∈
          projectiveDominantDoubleCoset k weight :=
        dominantCoweight_mem_doubleCoset k weight.toDominant
      have heq := hunique weight other
        ⟨dominantCoweight k weight.toDominant, hself, hothermem⟩
      exact hne heq.symm
    simp [projectiveDominantHeckeFunction_apply, hnot]
  · exact fun hnot ↦ (hnot hweight).elim
theorem linearIndependent_projectiveDominantHeckeFunction_rankThree
    (k : Type u) [Field k] [Finite k] :
    LinearIndependent ℂ
      (projectiveDominantHeckeFunction k :
        ProjectiveDominantCoweight 2 → HeckeFunction k 3) :=
  linearIndependent_projectiveDominantHeckeFunction_of_unique
    (projectiveDominant_rankThree_eq_of_doubleCoset_inter_nonempty k)
theorem linearIndependent_projectiveDominantHeckeFunction_rankFour
    (k : Type u) [Field k] [Finite k] :
    LinearIndependent ℂ
      (projectiveDominantHeckeFunction k :
        ProjectiveDominantCoweight 3 → HeckeFunction k 4) :=
  linearIndependent_projectiveDominantHeckeFunction_of_unique
    (projectiveDominant_rankFour_eq_of_doubleCoset_inter_nonempty k)
noncomputable def projectiveDominantHeckeBasisRankThree
    (k : Type u) [Field k] [Finite k] :
    Module.Basis (ProjectiveDominantCoweight 2) ℂ (HeckeFunction k 3) :=
  Module.Basis.mk
    (linearIndependent_projectiveDominantHeckeFunction_rankThree k)
    (by rw [span_projectiveDominantHeckeFunction_rankThree])
@[simp]
theorem projectiveDominantHeckeBasisRankThree_apply
    (k : Type u) [Field k] [Finite k]
    (weight : ProjectiveDominantCoweight 2) :
    projectiveDominantHeckeBasisRankThree k weight =
      projectiveDominantHeckeFunction k weight :=
  Module.Basis.mk_apply _ _ _
noncomputable def projectiveDominantHeckeBasisRankFour
    (k : Type u) [Field k] [Finite k] :
    Module.Basis (ProjectiveDominantCoweight 3) ℂ (HeckeFunction k 4) :=
  Module.Basis.mk
    (linearIndependent_projectiveDominantHeckeFunction_rankFour k)
    (by rw [span_projectiveDominantHeckeFunction_rankFour])
@[simp]
theorem projectiveDominantHeckeBasisRankFour_apply
    (k : Type u) [Field k] [Finite k]
    (weight : ProjectiveDominantCoweight 3) :
    projectiveDominantHeckeBasisRankFour k weight =
      projectiveDominantHeckeFunction k weight :=
  Module.Basis.mk_apply _ _ _
theorem apply_projectiveTranspose
    {k : Type u} [Field k] [Finite k] {n : ℕ}
    (f : HeckeFunction k (n + 1)) (x : HeckeGroup k (n + 1)) :
    f (projectiveTranspose x) = f x := by
  obtain ⟨weight, hx⟩ :=
    exists_mem_projectiveDominantDoubleCoset k x
  have htx : projectiveTranspose x ∈
      projectiveDominantDoubleCoset k weight :=
    projectiveTranspose_mem_dominantDoubleCoset k weight.toDominant hx
  calc
    f (projectiveTranspose x) =
        f (dominantCoweight k weight.toDominant) :=
      eq_dominantCoweight_of_mem_projectiveDominantDoubleCoset
        f weight htx
    _ = f x :=
      (eq_dominantCoweight_of_mem_projectiveDominantDoubleCoset
        f weight hx).symm
theorem projectiveTranspose_inv_mul
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (x t : PGL(n, R)) :
    (projectiveTranspose t)⁻¹ * projectiveTranspose x =
      projectiveTranspose (x * t⁻¹) := by
  rw [projectiveTranspose_mul]
  simp [projectiveTranspose]
theorem convolution_apply_rightForm
    {k : Type u} [Field k] [Finite k] {n : ℕ}
    (f g : HeckeFunction k (n + 1)) (x : HeckeGroup k (n + 1)) :
    (f * g) x = ∫ t, f (x * t⁻¹) * g t
      ∂normalizedLocalHaarMeasure k (n + 1) := by
  rw [mul_apply]
  let μ := normalizedLocalHaarMeasure k (n + 1)
  let F : HeckeGroup k (n + 1) → ℂ := fun t ↦ f t * g (t⁻¹ * x)
  letI : Measure.IsInvInvariant μ :=
    normalizedLocalHaarMeasure_isInvInvariant k (Nat.succ_pos n)
  calc
    (∫ t, f t * g (t⁻¹ * x) ∂μ) = ∫ t, F t ∂μ := rfl
    _ = ∫ t, F (x * t) ∂μ :=
      (integral_mul_left_eq_self F x).symm
    _ = ∫ t, F (x * t⁻¹) ∂μ :=
      (integral_inv_eq_self (fun t ↦ F (x * t)) μ).symm
    _ = ∫ t, f (x * t⁻¹) * g t ∂μ := by
      apply integral_congr_ae
      filter_upwards with t
      simp [F, mul_assoc]
theorem convolution_apply_projectiveTranspose
    {k : Type u} [Field k] [Finite k] {n : ℕ}
    (f g : HeckeFunction k (n + 1)) (x : HeckeGroup k (n + 1)) :
    (f * g) (projectiveTranspose x) = (g * f) x := by
  rw [mul_apply]
  let μ := normalizedLocalHaarMeasure k (n + 1)
  let F : HeckeGroup k (n + 1) → ℂ := fun t ↦
    f t * g (t⁻¹ * projectiveTranspose x)
  have hmp : MeasurePreserving
      (projectiveTransposeMeasurableEquiv (k := k) (d := n + 1)) μ μ :=
    projectiveTranspose_measurePreserving (k := k) (Nat.succ_pos n)
  calc
    (∫ t, f t * g (t⁻¹ * projectiveTranspose x) ∂μ) =
        ∫ t, F t ∂μ := rfl
    _ = ∫ t, F (projectiveTranspose t) ∂μ :=
      (hmp.integral_comp' F).symm
    _ = ∫ t, f t * g (x * t⁻¹) ∂μ := by
      apply integral_congr_ae
      filter_upwards with t
      change f (projectiveTranspose t) *
        g ((projectiveTranspose t)⁻¹ * projectiveTranspose x) = _
      rw [show (projectiveTranspose t)⁻¹ * projectiveTranspose x =
          projectiveTranspose (x * t⁻¹) by
        exact projectiveTranspose_inv_mul x t]
      rw [apply_projectiveTranspose f t,
        apply_projectiveTranspose g (x * t⁻¹)]
    _ = ∫ t, g (x * t⁻¹) * f t ∂μ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [mul_comm]
    _ = (g * f) x := (convolution_apply_rightForm g f x).symm
theorem convolution_comm
    {k : Type u} [Field k] [Finite k] {n : ℕ}
    (f g : HeckeFunction k (n + 1)) : f * g = g * f := by
  ext x
  calc
    (f * g) x = (f * g) (projectiveTranspose x) :=
      (apply_projectiveTranspose (f * g) x).symm
    _ = (g * f) x := convolution_apply_projectiveTranspose f g x
instance (k : Type u) [Field k] [Finite k] (n : ℕ) :
    CommRing (HeckeFunction k (n + 1)) where
  mul_comm := convolution_comm
def coloredAdjacency
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (f : HeckeFunction k d) : HeckeFunction k d :=
  convolution (fundamentalHeckeFunction k d r) f
end HeckeFunction
end QEC.Coding.HighDimensionalExpander.SphericalHecke


