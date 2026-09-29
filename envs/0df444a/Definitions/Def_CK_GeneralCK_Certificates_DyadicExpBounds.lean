-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_DyadicExpBounds
-- name    : CK_GeneralCK_Certificates_DyadicExpBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:14:23.732711+00:00
-- url     : https://prove2.me/theorems/85f04309-54e2-4656-824e-07bed5d82ca9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.DyadicExpBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.DyadicExpBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.DyadicExpBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.DyadicExpBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/DyadicExpBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicFastLog
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_GeneralCK_E8_interval_checkers

-- ===== source module GeneralCK.Certificates.DyadicExpBounds =====
section

/-!
# Exponential bounds reduced to checked logarithm bounds

This checker proves an enclosure for `Real.exp x` by checking logarithms of
positive rational lower and upper candidates.  It adds no transcendental
approximation algorithm or trust boundary beyond `DyadicFastLog.check`.
-/

namespace GeneralCK.Certificates.DyadicExp

open DyadicInterval


















theorem check_sound {p : ℕ} {input : DyadicInterval p}
    {lowerNum lowerDen upperNum upperDen : ℤ}
    {lowerExponent lowerTerms upperExponent upperTerms : ℕ}
    {logLower logUpper : DyadicInterval p}
    (hc : check input lowerNum lowerDen upperNum upperDen
      lowerExponent lowerTerms upperExponent upperTerms logLower logUpper = true)
    {x : ℝ} (hx : input.Contains x) :
    (enclosure p lowerNum lowerDen upperNum upperDen).Contains (Real.exp x) := by
  have htop := Bool.and_eq_true_iff.mp hc
  have hpair := Bool.and_eq_true_iff.mp htop.1
  have hlogLower := DyadicFastLog.check_sound hpair.1
  have hlogUpper := DyadicFastLog.check_sound hpair.2
  have hcmp : logLower.hi ≤ input.lo ∧ input.hi ≤ logUpper.lo :=
    of_decide_eq_true htop.2
  have hlDen : 0 < lowerDen := (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hpair.1).1).1).1).2
  have huDen : 0 < upperDen := (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hpair.2).1).1).1).2
  have hlNum : 0 < lowerNum := (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hpair.1).1).1).1).1
  have huNum : 0 < upperNum := (of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hpair.2).1).1).1).1
  have hs : (0 : ℝ) < DyadicInterval.scale p := DyadicInterval.scale_cast_pos p
  have hlogLowerLe : Real.log ((lowerNum : ℝ) / lowerDen) ≤ x := by
    have h1 := hlogLower.2
    have h2 : (logLower.hi : ℝ) ≤ (input.lo : ℝ) := by exact_mod_cast hcmp.1
    have h3 := hx.1
    nlinarith
  have hxLeLogUpper : x ≤ Real.log ((upperNum : ℝ) / upperDen) := by
    have h1 := hx.2
    have h2 : (input.hi : ℝ) ≤ (logUpper.lo : ℝ) := by exact_mod_cast hcmp.2
    have h3 := hlogUpper.1
    nlinarith
  have hlRatPos : (0 : ℝ) < (lowerNum : ℝ) / lowerDen := by
    positivity
  have huRatPos : (0 : ℝ) < (upperNum : ℝ) / upperDen := by
    positivity
  have hlExp : (lowerNum : ℝ) / lowerDen ≤ Real.exp x :=
    (Real.log_le_iff_le_exp hlRatPos).mp hlogLowerLe
  have hExpU : Real.exp x ≤ (upperNum : ℝ) / upperDen :=
    (Real.le_log_iff_exp_le huRatPos).mp hxLeLogUpper
  have hlFrac := DyadicFastLog.fraction_sound p lowerNum hlDen
  have huFrac := DyadicFastLog.fraction_sound p upperNum huDen
  constructor
  · exact hlFrac.1.trans (mul_le_mul_of_nonneg_left hlExp hs.le)
  · exact (mul_le_mul_of_nonneg_left hExpU hs.le).trans huFrac.2

end GeneralCK.Certificates.DyadicExp

end


