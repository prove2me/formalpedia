-- Prove2me | solution 1 for AronszajnRK.Limits.restricted_kernel_ll
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:25:15.511706+00:00
-- url     : https://prove2.me/submissions/709d7d40-5068-4858-8cee-8dc1190ed35b

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence
import Definitions.Def_AronszajnRK_Limits_KernelLE

set_option autoImplicit false

namespace FbdffAux

open scoped InnerProductSpace

variable {Y : Type*} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G] [RKHS ℂ G Y ℂ]

lemma kerFun_inner_one (x : Y) (f : G) : ⟪RKHS.kerFun G x 1, f⟫_ℂ = f x := by
  rw [RKHS.kerFun_inner]; simp

lemma kernelFn_eq_inner (x y : Y) :
    AronszajnRK.Sum.kernelFn G x y = ⟪RKHS.kerFun G x 1, RKHS.kerFun G y 1⟫_ℂ := by
  rw [kerFun_inner_one, RKHS.kerFun_apply]
  rfl

end FbdffAux

open scoped ComplexOrder InnerProductSpace in
open AronszajnRK.Limits in
theorem solution {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H) {m n : ℕ} (hmn : m < n) :
    KernelLE
      (fun x y : E m => AronszajnRK.Sum.kernelFn (H n) (Set.inclusion (hS.mono hmn.le) x)
        (Set.inclusion (hS.mono hmn.le) y))
      (AronszajnRK.Sum.kernelFn (H m)) := by
  classical
  unfold KernelLE
  refine ⟨?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.sub_apply, Matrix.of_apply, FbdffAux.kernelFn_eq_inner, star_sub,
      Complex.star_def, inner_conj_symm]
  · intro ξ
    obtain ⟨u, hu⟩ : ∃ w : H m, w = ξ.sum fun i c => c • RKHS.kerFun (H m) i 1 := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ w : H n, w = ξ.sum fun i c =>
        c • RKHS.kerFun (H n) (Set.inclusion (hS.mono hmn.le) i) 1 := ⟨_, rfl⟩
    have hQ : (ξ.sum fun i xi => ξ.sum fun j xj => star xi *
        (Matrix.of (AronszajnRK.Sum.kernelFn (H m)) - Matrix.of (fun x y : E m =>
          AronszajnRK.Sum.kernelFn (H n) (Set.inclusion (hS.mono hmn.le) x)
            (Set.inclusion (hS.mono hmn.le) y))) i j * xj) = ⟪u, u⟫_ℂ - ⟪v, v⟫_ℂ := by
      rw [Finsupp.sum_comm]
      rw [hu, hv]
      simp only [Finsupp.sum_inner, Finsupp.inner_sum, inner_smul_left, inner_smul_right,
        Matrix.sub_apply, Matrix.of_apply, FbdffAux.kernelFn_eq_inner]
      rw [← Finsupp.sum_sub]
      refine Finsupp.sum_congr fun i _ => ?_
      rw [Finsupp.mul_sum, Finsupp.mul_sum, ← Finsupp.sum_sub]
      refine Finsupp.sum_congr fun j _ => ?_
      simp only [Complex.star_def]
      ring
    obtain ⟨g, hg⟩ := hS.restrict_mem hmn.le v
    have hgv : ‖g‖ ≤ ‖v‖ := hS.norm_restrict_le hmn.le v g hg
    have hvv : ⟪v, v⟫_ℂ = ⟪u, g⟫_ℂ := by
      nth_rewrite 1 [hv]
      rw [hu]
      simp only [Finsupp.sum_inner, inner_smul_left, FbdffAux.kerFun_inner_one]
      refine Finsupp.sum_congr fun i _ => ?_
      rw [hg i.1 i.2 (hS.mono hmn.le i.2)]
    have hu2 : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u
    have hv2 : ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
    have h1 : ‖v‖ ^ 2 ≤ ‖u‖ * ‖v‖ := by
      have h := norm_inner_le_norm (𝕜 := ℂ) u g
      rw [← hvv, hv2, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
      nlinarith [norm_nonneg u]
    have h2 : ‖v‖ ≤ ‖u‖ := by
      nlinarith [norm_nonneg u, norm_nonneg v, sq_nonneg (‖v‖ - ‖u‖)]
    rw [hQ, hu2, hv2, ← Complex.ofReal_sub]
    exact Complex.zero_le_real.mpr (by nlinarith [norm_nonneg u, norm_nonneg v])
