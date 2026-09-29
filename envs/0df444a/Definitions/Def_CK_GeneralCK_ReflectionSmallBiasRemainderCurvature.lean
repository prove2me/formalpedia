-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasRemainderCurvature
-- name    : CK_GeneralCK_ReflectionSmallBiasRemainderCurvature
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:59:24.900271+00:00
-- url     : https://prove2.me/theorems/fd77b48f-96cc-49c2-8ccd-6c67888ab4df
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasRemainderCurvature` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasRemainderCurvature` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasRemainderCurvature` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasRemainderCurvature (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasRemainderCurvature.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasPartialCauchy

-- ===== source module GeneralCK.ReflectionSmallBiasRemainderCurvature =====
section

/-! Mixed Cauchy and mean-value estimates for an order-24 remainder. -/

namespace GeneralCK.Reflection.SmallBiasRemainder

open Set Filter Asymptotics SmallBiasPartialCauchy
open scoped Topology

theorem norm_in_auxiliary_disc {a : ℝ} {c z : ℂ}
    (hc : ‖c‖ ≤ a) (hz : z ∈ Metric.closedBall c (a/7)) :
    ‖z‖ ≤ 8*a/7 := by
  have hh := norm_le_of_mem_closedBall hz
  calc
    ‖z‖ ≤ ‖c‖ + a/7 := hh
    _ ≤ a + a/7 := add_le_add hc le_rfl
    _ = 8*a/7 := by ring

theorem remainder_curvature_bound {f : ℂ × ℂ → ℂ}
    (hf : ∀ z, ‖z‖ ≤ (21/50:ℝ) → AnalyticAt ℂ f z)
    (hbnd : ∀ z, ‖z‖ ≤ (21/50:ℝ) → ‖f z‖ ≤ 4)
    (haxis : ∀ a : ℂ, f (a, 0) = 0)
    (horder : f =O[𝓝 0] (fun z : ℂ × ℂ => ‖z‖ ^ 24))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (ha1 : a ≤ 3/20) :
    ‖partialAA f ((a:ℂ), (b:ℂ))‖ < (1/8:ℝ) * a^3 * b := by
  have haR : a < (21/50:ℝ) := by linarith
  have hr : 0 < a/7 := by positivity
  have hsmall : 8*a/7 < (21/50:ℝ) := by linarith
  have hanorm : ‖(a:ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hbnorm : ‖(b:ℂ)‖ = b := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
  have hd : DifferentiableOn ℂ f (Metric.ball 0 (21/50:ℝ)) := by
    intro z hz
    exact (hf z (by simpa only [Metric.mem_closedBall, dist_zero_right] using
      (Metric.ball_subset_closedBall hz))).differentiableAt.differentiableWithinAt
  have hzero : f 0 = 0 := haxis 0
  let M : ℝ := 4 * ((8*a/7)/(21/50:ℝ))^24
  let C : ℝ := 2*M/(a/7)^3
  have hlocal : ∀ v : ℂ, ‖v‖ ≤ a →
      ‖deriv (fun w : ℂ => partialAA f ((a:ℂ), w)) v‖ ≤ C := by
    intro v hv
    have hgeom : ∀ z ∈ Metric.closedBall (a:ℂ) (a/7),
        ∀ w ∈ Metric.closedBall v (a/7), ‖(z,w)‖ ≤ 8*a/7 := by
      intro z hz w hw
      rw [Prod.norm_def]
      exact max_le (norm_in_auxiliary_disc hanorm.le hz) (norm_in_auxiliary_disc hv hw)
    apply norm_deriv_partialAA_le hr
    · intro z hz w hw
      exact hf (z,w) ((hgeom z hz w hw).trans hsmall.le)
    · intro z hz w hw
      have hz' := hgeom z hz w hw
      have hh := norm_le_of_order hd hzero
        (fun u hu => hbnd u (by simpa only [Metric.mem_closedBall, dist_zero_right] using
          (Metric.ball_subset_closedBall hu))) horder (hz'.trans_lt hsmall)
      calc
        ‖f (z,w)‖ ≤ 4 * (‖(z,w)‖ / (21/50:ℝ))^24 := hh
        _ ≤ M := by dsimp [M]; gcongr; exact hz'
  have hbase : partialAA f ((a:ℂ), 0) = 0 := by
    have hz : ‖((a:ℂ), (0:ℂ))‖ ≤ (21/50:ℝ) := by
      simp only [Prod.norm_def, norm_zero, hanorm, max_eq_left ha.le]
      exact haR.le
    rw [partialAA_eq_deriv2 (hf _ hz)]
    have hh : (fun z : ℂ => f (z,0)) = fun _ => (0:ℂ) := funext haxis
    rw [hh]
    simp
  have hmean : ‖partialAA f ((a:ℂ), (b:ℂ))‖ ≤ C*b := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (𝕜 := ℂ) (f := fun w : ℂ => partialAA f ((a:ℂ), w))
      (s := Metric.closedBall (0:ℂ) a) (C := C)
      (fun v hv => by
        have hv' : ‖v‖ ≤ a := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
        have hz : ‖((a:ℂ),v)‖ ≤ (21/50:ℝ) := by
          rw [Prod.norm_def, hanorm]
          exact (max_le le_rfl hv').trans haR.le
        exact ((analyticAt_partialAA (hf _ hz)).comp
          (analyticAt_const.prod analyticAt_id)).differentiableAt)
      (fun v hv => hlocal v (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv))
      (convex_closedBall (0:ℂ) a)
      (show (0:ℂ) ∈ Metric.closedBall (0:ℂ) a from Metric.mem_closedBall_self ha.le)
      (show (b:ℂ) ∈ Metric.closedBall (0:ℂ) a from by
        simpa only [Metric.mem_closedBall, dist_zero_right, hbnorm] using hba)
    simpa only [hbase, sub_zero, hbnorm] using hh
  have hid : C*b =
      (8*7^3*((8/7:ℝ)/(21/50:ℝ))^24*a^18) * (a^3*b) := by
    dsimp [C, M]
    field_simp [ha.ne']
    <;> ring
  calc
    _ ≤ C*b := hmean
    _ = (8*7^3*((8/7:ℝ)/(21/50:ℝ))^24*a^18) * (a^3*b) := hid
    _ < (1/8:ℝ) * (a^3*b) :=
      mul_lt_mul_of_pos_right (normalized_remainder_bound ha.le ha1) (by positivity)
    _ = _ := by ring

end GeneralCK.Reflection.SmallBiasRemainder

end


