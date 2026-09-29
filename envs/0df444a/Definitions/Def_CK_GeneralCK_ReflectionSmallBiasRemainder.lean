-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasRemainder
-- name    : CK_GeneralCK_ReflectionSmallBiasRemainder
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:50:42.921427+00:00
-- url     : https://prove2.me/theorems/b3997e6f-a71d-4aa4-b03d-36aa4847d3b5
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasRemainder` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasRemainder` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasRemainder` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasRemainder (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasRemainder.lean)

import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Asymptotics.Lemmas

-- ===== source module GeneralCK.ReflectionSmallBiasRemainder =====
section

/-!
# Remainder estimates for the small-bias reflection proof

A degree-22 approximation with error of order 24 can be bounded by the
higher-order Schwarz lemma. The statements here retain the approximation
and analytic hypotheses explicitly.
-/

namespace GeneralCK.Reflection.SmallBiasRemainder

open Set Filter Asymptotics
open scoped Topology

theorem norm_le_of_order {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {R M : ℝ} {n : ℕ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) (hzero : f 0 = 0)
    (hbound : ∀ x ∈ Metric.ball (0 : E) R, ‖f x‖ ≤ M)
    (horder : f =O[𝓝 0] (fun x : E => ‖x‖ ^ (n + 1)))
    {x : E} (hx : ‖x‖ < R) : ‖f x‖ ≤ M * (‖x‖ / R) ^ (n + 1) := by
  have hlo : f =o[𝓝 0] (fun x : E => ‖x‖ ^ n) :=
    horder.trans_isLittleO (isLittleO_norm_pow_norm_pow (Nat.lt_succ_self n))
  have hh := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hf
    (show MapsTo f (Metric.ball 0 R) (Metric.closedBall (f 0) M) from by
      intro z hz
      simpa only [Metric.mem_closedBall, hzero, dist_zero_right] using hbound z hz)
    (by simpa only [hzero, sub_zero] using hlo)
    (show x ∈ Metric.ball 0 R by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  simpa only [hzero, dist_zero_right] using hh

theorem norm_deriv2_le {f : ℂ → ℂ} {c : ℂ} {r M : ℝ}
    (hr : 0 < r) (hf : DiffContOnCl ℂ f (Metric.ball c r))
    (hb : ∀ z ∈ Metric.sphere c r, ‖f z‖ ≤ M) :
    ‖deriv (deriv f) c‖ ≤ 2 * M / r ^ 2 := by
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hr hf hb
  norm_num [iteratedDeriv_succ] at hh
  exact hh

/-- Every retained factored monomial contributes a nonnegative curvature;
its normalized quadratic factor is at least eight. -/
theorem monomial_factor_ge_eight (i : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    8 ≤ (2 * (i : ℝ) + 5) * (2 * (i : ℝ) + 4) -
      2 * (2 * (i : ℝ) + 3) * (2 * (i : ℝ) + 2) * z ^ 2 +
      (2 * (i : ℝ) + 1) * (2 * (i : ℝ)) * z ^ 4 := by
  have hs : 0 ≤ 1 - z ^ 2 := by nlinarith
  calc
    (8 : ℝ) ≤ 8 + (1 - z ^ 2) * (16 * (i : ℝ) + 12) +
        (1 - z ^ 2) ^ 2 * (4 * (i : ℝ) ^ 2 + 2 * (i : ℝ)) := by
      have h1 : 0 ≤ (1 - z ^ 2) * (16 * (i : ℝ) + 12) := by positivity
      have h2 : 0 ≤ (1 - z ^ 2) ^ 2 * (4 * (i : ℝ) ^ 2 + 2 * (i : ℝ)) := by positivity
      linarith
    _ = _ := by ring

/-- Exact rational comparison after three Cauchy derivatives with radius `a/7`. -/
theorem normalized_remainder_constant_lt :
    (8 : ℝ) * 7 ^ 3 * ((8 / 7 : ℝ) / (21 / 50 : ℝ)) ^ 24 * (3 / 20 : ℝ) ^ 18 <
      (1 / 8 : ℝ) := by norm_num

theorem normalized_remainder_bound {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ (3 / 20 : ℝ)) :
    (8 : ℝ) * 7 ^ 3 * ((8 / 7 : ℝ) / (21 / 50 : ℝ)) ^ 24 * a ^ 18 < (1 / 8 : ℝ) := by
  calc
    _ ≤ (8 : ℝ) * 7 ^ 3 * ((8 / 7 : ℝ) / (21 / 50 : ℝ)) ^ 24 * (3 / 20 : ℝ) ^ 18 := by
      gcongr
    _ < (1 / 8 : ℝ) := normalized_remainder_constant_lt

end GeneralCK.Reflection.SmallBiasRemainder

end


