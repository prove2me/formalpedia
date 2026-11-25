-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
-- name    : GroundTheory_AutomorphicForms_TraceClass
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:29:20.73882+00:00
-- url     : https://prove2.me/theorems/2c0c4d94-549d-427b-9892-fa5b9509a1ce
-- title:
--   Trace Class
-- statement:
--   Definitions and structural lemmas for Trace Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_add
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_adjoint
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_smul
import Theorems.Thm_GroundTheory_Automorphic_enorm_inner_le
import Theorems.Thm_GroundTheory_Automorphic_hsNormSq_comp_right_le
import Theorems.Thm_GroundTheory_Automorphic_hsNormSq_eq_tsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
theorem ennreal_two_mul_le_sq_add_sq (a b : ℝ≥0∞) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a ∞ with rfl | ha
  · simp
  rcases eq_or_ne b ∞ with rfl | hb
  · simp
  lift a to NNReal using ha
  lift b to NNReal using hb
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - b)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
section Abs
theorem isSelfAdjoint_of_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) : IsSelfAdjoint A :=
  ((nonneg_iff_isPositive A).1 hA).isSelfAdjoint
theorem adjoint_eq_of_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) : A† = A :=
  (isSelfAdjoint_of_nonneg hA).adjoint_eq
theorem inner_apply_eq_norm_sqrt_sq {A : H →L[ℂ] H} (hA : 0 ≤ A) (x : H) :
    ⟪x, A x⟫_ℂ = ((‖CFC.sqrt A x‖ ^ 2 : ℝ) : ℂ) := by
  have hs : (CFC.sqrt A)† = CFC.sqrt A := adjoint_eq_of_nonneg (CFC.sqrt_nonneg A)
  have hA' : A = CFC.sqrt A * CFC.sqrt A := (CFC.sqrt_mul_sqrt_self A hA).symm
  conv_lhs => rw [hA', mul_def, comp_apply, ← hs, adjoint_inner_right, hs]
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
theorem norm_abs_apply (T : H →L[ℂ] H) (x : H) : ‖CFC.abs T x‖ = ‖T x‖ := by
  have hR : (CFC.abs T)† = CFC.abs T := adjoint_eq_of_nonneg (CFC.abs_nonneg T)
  have h : ‖CFC.abs T x‖ ^ 2 = ‖T x‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
    congr 1
    conv_lhs => rw [← adjoint_inner_right (CFC.abs T), hR, ← comp_apply, ← mul_def,
      CFC.abs_mul_abs, star_eq_adjoint, mul_def, comp_apply, adjoint_inner_right]
  have := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
theorem exists_polar (T : H →L[ℂ] H) :
    ∃ V : H →L[ℂ] H, ‖V‖ ≤ 1 ∧ V.comp (CFC.abs T) = T ∧ (V†).comp T = CFC.abs T := by
  set R := CFC.abs T with hRdef
  set M : Submodule ℂ H := (LinearMap.range R.toLinearMap).topologicalClosure with hM
  have : CompleteSpace M := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let e : H →ₗ[ℂ] M := R.toLinearMap.codRestrict M
    (fun x => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x))
  have he : ∀ x, (e x : H) = R x := fun x => rfl
  have hdense : DenseRange e := by
    rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
    intro y hy
    change y ∈ ((LinearMap.range R.toLinearMap).topologicalClosure : Set H) at hy
    rw [Submodule.topologicalClosure_coe, LinearMap.coe_range] at hy
    exact hy
  have hnorm : ∀ x, ‖T.toLinearMap x‖ ≤ 1 * ‖e x‖ := by
    intro x
    rw [one_mul, Submodule.coe_norm, he, norm_abs_apply]
    rfl
  let W : M →L[ℂ] H := T.toLinearMap.extendOfNorm e
  have hW : ∀ x, W (e x) = T x := fun x => LinearMap.extendOfNorm_eq hdense ⟨1, hnorm⟩ x
  have hWiso : ∀ m, ‖W m‖ = ‖m‖ := by
    intro m
    refine hdense.induction_on m (isClosed_eq W.continuous.norm continuous_norm) fun x => ?_
    rw [hW, Submodule.coe_norm, he, norm_abs_apply]
  let Wi : M →ₗᵢ[ℂ] H := { W.toLinearMap with norm_map' := hWiso }
  have hWinner : ∀ m m' : M, ⟪W m, W m'⟫_ℂ = ⟪m, m'⟫_ℂ := fun m m' => Wi.inner_map_map m m'
  refine ⟨W.comp M.orthogonalProjectionOnto, ?_, ?_, ?_⟩
  · refine (opNorm_comp_le _ _).trans ?_
    have h1 : ‖W‖ ≤ 1 := opNorm_le_bound _ zero_le_one fun m => by rw [hWiso, one_mul]
    calc ‖W‖ * ‖M.orthogonalProjectionOnto‖ ≤ 1 * 1 := by
          gcongr
          exact Submodule.orthogonalProjectionOnto_norm_le M
      _ = 1 := one_mul 1
  · ext x
    show W (M.orthogonalProjectionOnto ((e x : M) : H)) = T x
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, hW]
  · ext x
    refine ext_inner_right ℂ fun y => ?_
    rw [comp_apply, adjoint_inner_left, comp_apply, ← hW x, hWinner,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, he]
end Abs
section TraceNorm
def traceNorm (T : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (RCLike.re
    ⟪stdHilbertBasis ℂ H i, CFC.abs T (stdHilbertBasis ℂ H i)⟫_ℂ)
theorem ofReal_re_inner_abs (T : H →L[ℂ] H) (x : H) :
    ENNReal.ofReal (RCLike.re ⟪x, CFC.abs T x⟫_ℂ) = ‖CFC.sqrt (CFC.abs T) x‖ₑ ^ 2 := by
  rw [inner_apply_eq_norm_sqrt_sq (CFC.abs_nonneg T), RCLike.re_to_complex, Complex.ofReal_re,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
theorem traceNorm_eq_hsNormSq (T : H →L[ℂ] H) :
    traceNorm T = hsNormSq (CFC.sqrt (CFC.abs T)) := by
  simp only [traceNorm, ofReal_re_inner_abs]
  rfl
theorem traceNorm_eq_tsum {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    traceNorm T = ∑' i, ENNReal.ofReal (RCLike.re ⟪b i, CFC.abs T (b i)⟫_ℂ) := by
  simp only [traceNorm_eq_hsNormSq, ofReal_re_inner_abs, hsNormSq_eq_tsum b]
def IsTraceClass (T : H →L[ℂ] H) : Prop := traceNorm T < ∞
theorem traceNorm_le_of_adjoint_comp {ι : Type*} (b : HilbertBasis ι ℂ H) {T V : H →L[ℂ] H}
    (hV : (V†).comp T = CFC.abs T) : traceNorm T ≤ ∑' i, ‖⟪V (b i), T (b i)⟫_ℂ‖ₑ := by
  rw [traceNorm_eq_tsum b]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← hV, comp_apply, adjoint_inner_right, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (RCLike.re_le_norm _)
theorem enorm_le_one_of_norm_le_one {A : H →L[ℂ] H} (hA : ‖A‖ ≤ 1) : ‖A‖ₑ ≤ 1 := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.2 hA
theorem tsum_enorm_inner_le_traceNorm {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    {U W : H →L[ℂ] H} (hU : ‖U‖ ≤ 1) (hW : ‖W‖ ≤ 1) :
    ∑' i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ ≤ traceNorm T := by
  obtain ⟨V, hV1, hVT, -⟩ := exists_polar T
  set s := CFC.sqrt (CFC.abs T) with hsdef
  have hs : s† = s := adjoint_eq_of_nonneg (CFC.sqrt_nonneg _)
  have hss : s.comp s = CFC.abs T := CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg T)
  have hpt : ∀ x y, ⟪U x, T (W y)⟫_ℂ = ⟪s ((V†) (U x)), s (W y)⟫_ℂ := by
    intro x y
    conv_lhs => rw [← hVT, ← hss, comp_apply, comp_apply, ← adjoint_inner_left V,
      ← hs, adjoint_inner_right, hs]
  have hVU : ‖(V†).comp U‖ ≤ 1 := by
    refine (opNorm_comp_le _ _).trans ?_
    rw [adjoint.norm_map]
    calc ‖V‖ * ‖U‖ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  have key : 2 * ∑' i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ ≤ 2 * traceNorm T := by
    calc 2 * ∑' i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ
        ≤ ∑' i, (‖s ((V†) (U (b i)))‖ₑ ^ 2 + ‖s (W (b i))‖ₑ ^ 2) := by
          rw [← ENNReal.tsum_mul_left]
          refine ENNReal.tsum_le_tsum fun i => ?_
          rw [hpt]
          calc 2 * ‖⟪s ((V†) (U (b i))), s (W (b i))⟫_ℂ‖ₑ
              ≤ 2 * (‖s ((V†) (U (b i)))‖ₑ * ‖s (W (b i))‖ₑ) := by
                gcongr; exact enorm_inner_le _ _
            _ ≤ _ := ennreal_two_mul_le_sq_add_sq _ _
      _ = hsNormSq (s.comp ((V†).comp U)) + hsNormSq (s.comp W) := by
          rw [ENNReal.tsum_add, hsNormSq_eq_tsum b, hsNormSq_eq_tsum b]
          rfl
      _ ≤ ‖(V†).comp U‖ₑ ^ 2 * hsNormSq s + ‖W‖ₑ ^ 2 * hsNormSq s :=
          add_le_add (hsNormSq_comp_right_le _ _) (hsNormSq_comp_right_le _ _)
      _ ≤ 1 ^ 2 * hsNormSq s + 1 ^ 2 * hsNormSq s := by
          gcongr
          · exact enorm_le_one_of_norm_le_one hVU
          · exact enorm_le_one_of_norm_le_one hW
      _ = 2 * traceNorm T := by rw [traceNorm_eq_hsNormSq, one_pow, one_mul, two_mul]
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 key
end TraceNorm
section Ideal
theorem norm_id_le_one : ‖ContinuousLinearMap.id ℂ H‖ ≤ 1 := norm_id_le
theorem tsum_enorm_inner_le {ι : Type*} (b : HilbertBasis ι ℂ H) (T U W : H →L[ℂ] H) :
    ∑' i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ ≤ ‖U‖ₑ * ‖W‖ₑ * traceNorm T := by
  rcases eq_or_ne U 0 with rfl | hU
  · simp
  rcases eq_or_ne W 0 with rfl | hW
  · simp
  have hu : 0 < ‖U‖ := norm_pos_iff.2 hU
  have hw : 0 < ‖W‖ := norm_pos_iff.2 hW
  set U₀ : H →L[ℂ] H := ((‖U‖⁻¹ : ℝ) : ℂ) • U with hU₀def
  set W₀ : H →L[ℂ] H := ((‖W‖⁻¹ : ℝ) : ℂ) • W with hW₀def
  have hU₀ : ‖U₀‖ ≤ 1 := by
    rw [hU₀def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hu.ne']
  have hW₀ : ‖W₀‖ ≤ 1 := by
    rw [hW₀def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hw.ne']
  have hUx : ∀ x, U x = ((‖U‖ : ℝ) : ℂ) • U₀ x := fun x => by
    rw [hU₀def, smul_apply, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hu.ne',
      Complex.ofReal_one, one_smul]
  have hWx : ∀ x, W x = ((‖W‖ : ℝ) : ℂ) • W₀ x := fun x => by
    rw [hW₀def, smul_apply, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hw.ne',
      Complex.ofReal_one, one_smul]
  have hpt : ∀ i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ =
      ‖U‖ₑ * ‖W‖ₑ * ‖⟪U₀ (b i), T (W₀ (b i))⟫_ℂ‖ₑ := by
    intro i
    have h : ⟪U (b i), T (W (b i))⟫_ℂ =
        ((‖U‖ * ‖W‖ : ℝ) : ℂ) * ⟪U₀ (b i), T (W₀ (b i))⟫_ℂ := by
      rw [hUx, hWx, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
        Complex.ofReal_mul, mul_assoc]
    rw [h, enorm_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
  simp_rw [hpt, ENNReal.tsum_mul_left]
  gcongr
  exact tsum_enorm_inner_le_traceNorm b T hU₀ hW₀
theorem traceNorm_zero : traceNorm (0 : H →L[ℂ] H) = 0 := by
  simp [traceNorm]
theorem traceNorm_add_le (S T : H →L[ℂ] H) : traceNorm (S + T) ≤ traceNorm S + traceNorm T := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (S + T)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  have hI : ‖ContinuousLinearMap.id ℂ H‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one norm_id_le_one
  calc traceNorm (S + T) ≤ ∑' i, ‖⟪V (b i), (S + T) (b i)⟫_ℂ‖ₑ :=
        traceNorm_le_of_adjoint_comp b hV
    _ ≤ ∑' i, (‖⟪V (b i), S (ContinuousLinearMap.id ℂ H (b i))⟫_ℂ‖ₑ +
          ‖⟪V (b i), T (ContinuousLinearMap.id ℂ H (b i))⟫_ℂ‖ₑ) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [add_apply, inner_add_right, id_apply]
        exact enorm_add_le _ _
    _ = _ := ENNReal.tsum_add
    _ ≤ ‖V‖ₑ * ‖ContinuousLinearMap.id ℂ H‖ₑ * traceNorm S +
          ‖V‖ₑ * ‖ContinuousLinearMap.id ℂ H‖ₑ * traceNorm T :=
        add_le_add (tsum_enorm_inner_le b S _ _) (tsum_enorm_inner_le b T _ _)
    _ ≤ 1 * 1 * traceNorm S + 1 * 1 * traceNorm T := by gcongr
    _ = traceNorm S + traceNorm T := by simp only [one_mul]
theorem traceNorm_comp_left_le (C T : H →L[ℂ] H) : traceNorm (C.comp T) ≤ ‖C‖ₑ * traceNorm T := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (C.comp T)
  let b := stdHilbertBasis ℂ H
  have hI : ‖ContinuousLinearMap.id ℂ H‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one norm_id_le_one
  have hCV : ‖(C†).comp V‖ₑ ≤ ‖C‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((opNorm_comp_le _ _).trans ?_)
    rw [adjoint.norm_map]
    calc ‖C‖ * ‖V‖ ≤ ‖C‖ * 1 := by gcongr
      _ = ‖C‖ := mul_one _
  calc traceNorm (C.comp T) ≤ ∑' i, ‖⟪V (b i), (C.comp T) (b i)⟫_ℂ‖ₑ :=
        traceNorm_le_of_adjoint_comp b hV
    _ = ∑' i, ‖⟪((C†).comp V) (b i), T (ContinuousLinearMap.id ℂ H (b i))⟫_ℂ‖ₑ := by
        congr 1; ext i
        rw [comp_apply, comp_apply, adjoint_inner_left, id_apply]
    _ ≤ ‖(C†).comp V‖ₑ * ‖ContinuousLinearMap.id ℂ H‖ₑ * traceNorm T := tsum_enorm_inner_le b T _ _
    _ ≤ ‖C‖ₑ * 1 * traceNorm T := by gcongr
    _ = ‖C‖ₑ * traceNorm T := by rw [mul_one]
theorem traceNorm_smul_le (c : ℂ) (T : H →L[ℂ] H) : traceNorm (c • T) ≤ ‖c‖ₑ * traceNorm T := by
  have h : c • T = (c • ContinuousLinearMap.id ℂ H).comp T := by ext x; simp
  rw [h]
  refine (traceNorm_comp_left_le _ _).trans ?_
  gcongr
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ((norm_smul_le _ _).trans ?_)
  calc ‖c‖ * ‖ContinuousLinearMap.id ℂ H‖ ≤ ‖c‖ * 1 := by gcongr; exact norm_id_le_one
    _ = ‖c‖ := mul_one _
theorem IsTraceClass.add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T) :=
  (traceNorm_add_le S T).trans_lt (ENNReal.add_lt_top.2 ⟨hS, hT⟩)
theorem IsTraceClass.smul {T : H →L[ℂ] H} (hT : IsTraceClass T) (c : ℂ) :
    IsTraceClass (c • T) :=
  (traceNorm_smul_le c T).trans_lt (ENNReal.mul_lt_top (by simp) hT)
variable (H) in

def traceClass : Submodule ℂ (H →L[ℂ] H) where
  carrier := {T | IsTraceClass T}
  add_mem' hS hT := hS.add hT
  zero_mem' := by
    show traceNorm (0 : H →L[ℂ] H) < ∞
    rw [traceNorm_zero]; exact ENNReal.zero_lt_top
  smul_mem' c _ hT := hT.smul c
end Ideal
section Trace
def trace (T : H →L[ℂ] H) : ℂ :=
  ∑' i, ⟪stdHilbertBasis ℂ H i, T (stdHilbertBasis ℂ H i)⟫_ℂ
end Trace
end
end GroundTheory.Automorphic


