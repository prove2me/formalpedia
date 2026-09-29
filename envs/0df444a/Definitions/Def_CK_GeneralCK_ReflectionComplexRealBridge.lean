-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionComplexRealBridge
-- name    : CK_GeneralCK_ReflectionComplexRealBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T09:49:53.641421+00:00
-- url     : https://prove2.me/theorems/08ee75b2-7a22-480b-8127-2b82b7dde245
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionComplexRealBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionComplexRealBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionComplexRealBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionComplexRealBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionComplexRealBridge.lean)

import Definitions.Def_CK_GeneralCK_ReflectionComplexFixedPoint
import Definitions.Def_CK_GeneralCK_ReflectionContactInverse
import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanCertificate

-- ===== source module GeneralCK.ReflectionComplexRealBridge =====
section

/-!
# The complex contact point on the real axis

This file identifies the Banach fixed point constructed from the principal
complex logarithm with the manuscript's real `biasContact`, and hence with
the normalized `radialContact` formula.
-/

namespace GeneralCK.Reflection.ComplexRealBridge

open Set Function
open Certificates.Reflection
open ComplexEntropy ComplexFixedPoint

/-- On the real interval `(-1,1)`, the principal-log extension is exactly the
real bias entropy used in the manuscript. -/
theorem entropyExt_ofReal {c : ℝ} (hc₀ : -1 < c) (hc₁ : c < 1) :
    entropyExt (c : ℂ) = (biasE c : ℂ) := by
  have hp : 0 ≤ 1 + c := (by linarith : 0 ≤ 1 + c)
  have hm : 0 ≤ 1 - c := (by linarith : 0 ≤ 1 - c)
  have hpLog : Complex.log (1 + (c : ℂ)) = (Real.log (1 + c) : ℂ) := by
    calc
      Complex.log (1 + (c : ℂ)) = Complex.log ((1 + c : ℝ) : ℂ) := by norm_num
      _ = (Real.log (1 + c) : ℂ) := (Complex.ofReal_log hp).symm
  have hmLog : Complex.log (1 - (c : ℂ)) = (Real.log (1 - c) : ℂ) := by
    calc
      Complex.log (1 - (c : ℂ)) = Complex.log ((1 - c : ℝ) : ℂ) := by norm_num
      _ = (Real.log (1 - c) : ℂ) := (Complex.ofReal_log hm).symm
  unfold entropyExt biasE
  rw [hpLog, hmLog]
  norm_num

/-- The manuscript contact solves the real entropy fixed-point equation. -/
theorem biasContact_fixed_eq {tau : ℝ} (htau : 0 < tau) :
    biasContact (1 / tau) = tau * biasE (biasContact (1 / tau)) := by
  have hy : 0 < 1 / tau := one_div_pos.mpr htau
  have hc := biasContact_mem hy
  have hR := biasR_biasContact hy
  unfold biasR at hR
  have he := (div_eq_iff hc.1.ne').mp hR
  field_simp [htau.ne'] at he ⊢
  nlinarith

/-- For `0 < tau ≤ 7/10`, the manuscript contact lies well inside the
complex-contraction disc.  The stronger bound `49/100` is recorded because
it is useful independently of the bridge. -/
theorem biasContact_le_49_div_100 {tau : ℝ} (htau : 0 < tau)
    (htau_le : tau ≤ 7 / 10) : biasContact (1 / tau) ≤ 49 / 100 := by
  have hy : 0 < 1 / tau := one_div_pos.mpr htau
  have hc := biasContact_mem hy
  have hE : biasE (biasContact (1 / tau)) ≤ Real.log 2 := by
    have hmono := biasE_antitone
      (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      (show biasContact (1 / tau) ∈ Icc (0 : ℝ) 1 from ⟨hc.1.le, hc.2.le⟩)
      hc.1.le
    simpa [biasE] using hmono
  have hlog : Real.log 2 < 7 / 10 :=
    GeneralCK.Certificates.SmallMean.fixed_log_two_lt
  have hEnonneg : 0 ≤ biasE (biasContact (1 / tau)) := by
    have heq := biasContact_fixed_eq htau
    nlinarith [hc.1]
  rw [biasContact_fixed_eq htau]
  calc
    tau * biasE (biasContact (1 / tau)) ≤
        (7 / 10) * (7 / 10) :=
      mul_le_mul htau_le (le_trans hE hlog.le) hEnonneg (by norm_num)
    _ = 49 / 100 := by norm_num

/-- A real parameter in the manuscript range satisfies the complex norm
hypothesis used by the contraction theorem. -/
theorem norm_ofReal_tau_le {tau : ℝ} (htau : 0 < tau)
    (htau_le : tau ≤ 7 / 10) : ‖(tau : ℂ)‖ ≤ (7 / 10 : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htau]
  exact htau_le

/-- Exact real-axis bridge: the chosen complex Banach fixed point is the
manuscript's bias contact at reciprocal slope. -/
theorem fixedPoint_eq_biasContact {tau : ℝ} (htau : 0 < tau)
    (htau_le : tau ≤ 7 / 10)
    (htau_complex : ‖(tau : ℂ)‖ ≤ (7 / 10 : ℝ)) :
    fixedPoint (tau : ℂ) htau_complex = (biasContact (1 / tau) : ℂ) := by
  let c : ℝ := biasContact (1 / tau)
  have hy : 0 < 1 / tau := one_div_pos.mpr htau
  have hc := biasContact_mem hy
  have hcBound : c ≤ 4 / 5 :=
    (biasContact_le_49_div_100 htau htau_le).trans (by norm_num)
  have hcpos : 0 < c := by exact hc.1
  have hcDisc : (c : ℂ) ∈ Metric.closedBall 0 (4 / 5 : ℝ) := by
    simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_pos hcpos]
    exact hcBound
  have hfix : IsFixedPt
      (ComplexDiscElementary.contactMap entropyExt (tau : ℂ)) (c : ℂ) := by
    unfold IsFixedPt ComplexDiscElementary.contactMap
    rw [entropyExt_ofReal (by linarith [hc.1]) hc.2]
    norm_cast
    simpa only [c] using (biasContact_fixed_eq htau).symm
  exact (eq_fixedPoint htau_complex hcDisc hfix).symm

/-- The same bridge with its norm proof discharged from real inequalities. -/
theorem fixedPoint_eq_biasContact' {tau : ℝ} (htau : 0 < tau)
    (htau_le : tau ≤ 7 / 10) :
    fixedPoint (tau : ℂ) (norm_ofReal_tau_le htau htau_le) =
      (biasContact (1 / tau) : ℂ) :=
  fixedPoint_eq_biasContact htau htau_le _

/-- Expanded form of the exact bridge in terms of the original radial
contact notion. -/
theorem fixedPoint_eq_radialContact {tau : ℝ} (htau : 0 < tau)
    (htau_le : tau ≤ 7 / 10) :
    fixedPoint (tau : ℂ) (norm_ofReal_tau_le htau htau_le) =
      ((1 - 2 * radialContact 1 ((1 / tau) / Real.log 2) : ℝ) : ℂ) := by
  simpa only [biasContact] using fixedPoint_eq_biasContact' htau htau_le

end GeneralCK.Reflection.ComplexRealBridge

end


