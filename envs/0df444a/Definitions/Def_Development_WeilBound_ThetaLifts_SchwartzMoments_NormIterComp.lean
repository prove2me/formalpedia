-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_NormIterComp
-- name    : Development_WeilBound_ThetaLifts_SchwartzMoments_NormIterComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:15.148556+00:00
-- url     : https://prove2.me/theorems/e50a1228-5f62-4e4e-a3a2-32a4870fcc70
-- title:
--   Norm Iter Comp
-- statement:
--   Definitions and structural lemmas for Norm Iter Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/NormIterComp.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKOwn
open scoped SchwartzMap ContDiff
variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
theorem norm_iter_comp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : E →L[ℝ] A) (φ : 𝓢(A, ℂ)) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (⇑φ ∘ p) x‖ ≤ ‖iteratedFDeriv ℝ i φ (p x)‖ * ‖p‖ ^ i := by
  rw [p.iteratedFDeriv_comp_right (φ.smooth ⊤) _ (by exact_mod_cast le_top)]
  simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ i φ (p x)) (fun _ => p)
theorem norm_le_prod (x : WithLp 2 (A × B)) :
    ‖x‖ ≤ (1 + ‖WithLp.fstL 2 ℝ A B x‖) * (1 + ‖WithLp.sndL 2 ℝ A B x‖) := by
  have h := WithLp.prod_norm_sq_eq_of_L2 x
  have h1 := norm_nonneg x.fst
  have h2 := norm_nonneg x.snd
  have h3 : ‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖ := by
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    nlinarith [mul_nonneg h1 h2]
  change ‖x‖ ≤ (1 + ‖x.fst‖) * (1 + ‖x.snd‖)
  nlinarith [mul_nonneg h1 h2]
def tens (φ : 𝓢(A, ℂ)) (f : 𝓢(B, ℂ)) : 𝓢(WithLp 2 (A × B), ℂ) where
  toFun x := (⇑φ ∘ WithLp.fstL 2 ℝ A B) x * (⇑f ∘ WithLp.sndL 2 ℝ A B) x
  smooth' := ((φ.smooth ⊤).comp (WithLp.fstL 2 ℝ A B).contDiff).mul ((f.smooth ⊤).comp (WithLp.sndL 2 ℝ A B).contDiff)
  decay' k n := by
    set p := WithLp.fstL 2 ℝ A B
    set q := WithLp.sndL 2 ℝ A B
    set S : ℝ := 2 ^ k * ((Finset.Iic (k, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ
    set T : ℝ := 2 ^ k * ((Finset.Iic (k, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (S * ‖p‖ ^ i) * (T * ‖q‖ ^ (n - i)), fun x => ?_⟩
    have h1 := norm_iteratedFDeriv_mul_le ((φ.smooth ⊤).comp p.contDiff) ((f.smooth ⊤).comp q.contDiff) x (n := n)
      (by exact_mod_cast le_top)
    refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h2 : (1 + ‖p x‖) ^ k * ‖iteratedFDeriv ℝ i φ (p x)‖ ≤ S :=
      SchwartzMap.one_add_le_sup_seminorm_apply (m := (k, n)) le_rfl hi' φ _
    have h3 : (1 + ‖q x‖) ^ k * ‖iteratedFDeriv ℝ (n - i) f (q x)‖ ≤ T :=
      SchwartzMap.one_add_le_sup_seminorm_apply (m := (k, n)) le_rfl (Nat.sub_le _ _) f _
    have h4 := norm_iter_comp p φ i x
    have h5 := norm_iter_comp q f (n - i) x
    have h6 : ‖x‖ ≤ (1 + ‖p x‖) * (1 + ‖q x‖) := norm_le_prod x
    have hS : 0 ≤ S := le_trans (by positivity) h2
    calc _ ≤ ((1 + ‖p x‖) * (1 + ‖q x‖)) ^ k * ((n.choose i : ℝ) * (‖iteratedFDeriv ℝ i φ (p x)‖ * ‖p‖ ^ i) *
          (‖iteratedFDeriv ℝ (n - i) f (q x)‖ * ‖q‖ ^ (n - i))) := by gcongr
      _ = (n.choose i : ℝ) * (((1 + ‖p x‖) ^ k * ‖iteratedFDeriv ℝ i φ (p x)‖) * ‖p‖ ^ i) *
          (((1 + ‖q x‖) ^ k * ‖iteratedFDeriv ℝ (n - i) f (q x)‖) * ‖q‖ ^ (n - i)) := by
          rw [mul_pow]; ring
      _ ≤ _ := by gcongr
end PositivityTheory.ThKOwn
end


