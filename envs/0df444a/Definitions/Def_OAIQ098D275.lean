-- Prove2me | Definitions.Def_OAIQ098D275
-- name    : OAIQ098D275
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:46:08.821913+00:00
-- url     : https://prove2.me/theorems/d5dc0de3-4fc3-4e41-898d-75bdbc93d365
-- title:
--   Definitions bundle OAIQ098D275 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 13 definitions, 1 instance and 39 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.tm1_84_1.s5`, `OAI.SharpPlanar.CachedData.trans22`, `OAI.SharpPlanar.CachedData.trans22_r4`, `OAI.SharpPlanar.CachedData.trans34`, `OAI.SharpPlanar.CachedData.trans34_r5`, `OAI.SharpPlanar.CachedData.trans50`, `OAI.SharpPlanar.CachedData.trans50_r2`, `OAI.SharpPlanar.CachedData.trans66`, `OAI.SharpPlanar.CachedData.trans66_r3`, `OAI.SharpPlanar.CachedData.trans83`, `OAI.SharpPlanar.CachedData.trans83_r2`, `OAI.SharpPlanar.IntegerBasis.uAmplitudeBox`, `OAI.SharpPlanar.IntegerBasis.vAmplitudeBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_CanonicalRows`, `PlanarPacking_Certificate_TableMoments7`, `PlanarPacking_Certificate_TableMoments73`, `PlanarPacking_Certificate_TableMoments75`, `PlanarPacking_Certificate_TableMoments76`, `PlanarPacking_Certificate_TableMoments79`, `PlanarPacking_Certificate_TableMoments81`, `PlanarPacking_Certificate_TableMoments84`, `PlanarPacking_Certificate_TableMoments85`, `PlanarPacking_Certificate_TableMoments87`, `PlanarPacking_Certificate_TableMoments88`, `PlanarPacking_Certificate_TableMoments9`, `PlanarPacking_Certificate_TableMoments91`, `PlanarPacking_Certificate_TableMoments93`, `PlanarPacking_Certificate_TableMoments96`, `PlanarPacking_Certificate_TableMoments97`, `PlanarPacking_Certificate_TableMoments99`, `PlanarPacking_Certificate_TransformedPowers30`, `PlanarPacking_Certificate_TransformedPowers40`, `PlanarPacking_Certificate_TransformedPowers50`, `PlanarPacking_Certificate_TransformedPowers70`, `PlanarPacking_Certificate_TransformedPowers90`, `PlanarPacking_FiniteInverse`, `PlanarPacking_FiniteTail`, `PlanarPacking_NodeIntervals`.
--
--   **Imports.** It imports the bundles `OAIQ098D010`, `OAIQ098D041`, `OAIQ098D125`, `OAIQ098D253`, `OAIQ098D254`, `OAIQ098D255`, `OAIQ098D256`, `OAIQ098D257`, `OAIQ098D258` and `OAIQ098D259` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D399`, `OAIQ098D421`, `OAIQ098D431`, `OAIQ098D453`, `OAIQ098D458`, `OAIQ098D465` and `OAIQ098D466`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D010
import Definitions.Def_OAIQ098D041
import Definitions.Def_OAIQ098D125
import Definitions.Def_OAIQ098D253
import Definitions.Def_OAIQ098D254
import Definitions.Def_OAIQ098D255
import Definitions.Def_OAIQ098D256
import Definitions.Def_OAIQ098D257
import Definitions.Def_OAIQ098D258
import Definitions.Def_OAIQ098D259

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerIntervals

instance instDecidableSqNormCheck (a : CBox) (m n : ℤ) : Decidable (a.SqNormCheck m n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

lemma CBox.norm_le_rat {a : CBox} {z : ℂ} {m n : ℤ} (hz : a.Contains z)
    (hc : a.SqNormCheck m n) : ‖z‖ ≤ (m:ℝ)/n := by
  have hn : (0:ℝ) < n := by exact_mod_cast hc.1
  have hm : (0:ℝ) ≤ m := by exact_mod_cast hc.2.1
  have hr := RBox.abs_bound hz.1
  have hi := RBox.abs_bound hz.2
  have hb1 : (0:ℝ) ≤ a.re.bound := (mul_nonneg precision_pos.le (abs_nonneg _)).trans hr
  have hb2 : (0:ℝ) ≤ a.im.bound := (mul_nonneg precision_pos.le (abs_nonneg _)).trans hi
  have hs1 : (precision:ℝ)^2*z.re^2 ≤ (a.re.bound:ℝ)^2 := by
    simpa only [mul_pow, sq_abs] using
      (sq_le_sq₀ (mul_nonneg precision_pos.le (abs_nonneg _)) hb1).mpr hr
  have hs2 : (precision:ℝ)^2*z.im^2 ≤ (a.im.bound:ℝ)^2 := by
    simpa only [mul_pow, sq_abs] using
      (sq_le_sq₀ (mul_nonneg precision_pos.le (abs_nonneg _)) hb2).mpr hi
  have hh : (((a.re.bound:ℝ)^2+(a.im.bound:ℝ)^2)*(n:ℝ)^2) ≤ ((precision:ℝ)*m)^2 := by
    exact_mod_cast hc.2.2
  have he : ‖z‖^2 = z.re^2+z.im^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  have hk : ((precision:ℝ)*‖z‖)^2 ≤ (a.re.bound:ℝ)^2+(a.im.bound:ℝ)^2 := by
    rw [mul_pow,he]; nlinarith only [hs1,hs2]
  have hkn := mul_le_mul_of_nonneg_right hk (sq_nonneg (n:ℝ))
  have hbound : (‖z‖*(n:ℝ))^2 ≤ (m:ℝ)^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos precision_pos)).mp
    nlinarith only [hkn,hh]
  apply (le_div_iff₀ hn).mpr
  nlinarith only [hbound,mul_nonneg (norm_nonneg z) hn.le,hm]

end SharpPlanar.IntegerIntervals

namespace SharpPlanar


lemma z_sq_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖z t‖^2 ≤ ‖z s‖^2 := by
  rw [z_sq,z_sq]
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_left (by norm_num) (by unfold h; positivity)
  nlinarith


lemma piece_kernel_bounds (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖lambda t‖ ≤ lambdaCap ⟨j.val,by omega⟩ ∧
    ‖z t‖ ≤ zCap ⟨j.val,by omega⟩ ∧
    dampingCap ⟨j.val+1,by omega⟩+slopeCap j*(((j.val:ℝ)+1)/6-t) ≤ (z t).im := by
  have hs : 0 ≤ (j.val:ℝ)/6 := by positivity
  have hb := (endpoint_kernel_bounds ⟨j.val,by omega⟩).1
  have ha := (endpoint_kernel_bounds ⟨j.val,by omega⟩).2.1
  refine ⟨?_,?_,piece_damping_bound j ht⟩
  · exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (lambda_sq_antitone hs ht.1)).trans hb
  · exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (z_sq_antitone hs ht.1)).trans ha

end SharpPlanar

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

def uAmplitudeBox (t : RBox) (a b : CBox) : CBox :=
  ((rcast (piBounds.mul piBounds)).scale (-2) 1).mul
    (b.add (((rcast t).mul a).neg))
def vAmplitudeBox (a : CBox) : CBox := (piI.scale 2 1).mul a

end SharpPlanar.IntegerBasis

namespace SharpPlanar
open IntegerBasis

lemma kernelMoment_segment_bound (j : Fin 6) (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s)
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖kernelMoment ell s t‖ ≤ segmentEnvelope j ell s t := by
  obtain ⟨hl,hz,hi⟩ := piece_kernel_bounds j ht
  have hex : ‖Complex.exp (Complex.I*Real.pi*z t*s)‖ ≤
      Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
      Real.exp (-(Real.pi*slopeCap j*s)*(((j.val:ℝ)+1)/6-t)) := by
    rw [← Real.exp_add,Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,zero_sub,
      sub_zero,zero_add]
    nlinarith [mul_le_mul_of_nonneg_right hi (mul_nonneg Real.pi_pos.le hs)]
  unfold kernelMoment segmentEnvelope
  rw [norm_mul,norm_mul,norm_pow,norm_mul,norm_mul,Complex.norm_I,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_mul]
  have hp : (Real.pi*‖z t‖)^ell ≤ (Real.pi*zCap ⟨j.val,by omega⟩)^ell := by
    gcongr
  calc
    _ ≤ lambdaCap ⟨j.val,by omega⟩*(Real.pi*zCap ⟨j.val,by omega⟩)^ell *
        (Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
         Real.exp (-(Real.pi*slopeCap j*s)*(((j.val:ℝ)+1)/6-t))) :=
      mul_le_mul (mul_le_mul hl hp (by positivity) (lambdaCap_nonneg _)) hex
        (norm_nonneg _) (mul_nonneg (lambdaCap_nonneg _) (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg _)) _))
    _ = _ := by ring

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_NodeIntervals
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

lemma K_column_contains {n : Node} {m : ℕ} (hn : n.val ≤ 100) (hm : m ≤ 100)
    (d e : Bool) {a : CBox}
    (ha : a.Contains (momentRuleValue quadraturePoint fejerWeight n.val m d e)) :
    (inflate a.re).Contains (K (positiveData (columnVector n d)) (if e then 1 else 0) m) :=
  inflate_contains ha.1 (K_column_rule_error hn hm d e)

end Numerical
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments7
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_7_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_7_0

namespace tm1_7_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_7_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers30
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def trans22_r4 : Fin 16 → Fin 16 → CBox := ![trans22_r4_0,trans22_r4_1,trans22_r4_2,trans22_r4_3,trans22_r4_4,trans22_r4_5,trans22_r4_6,trans22_r4_7,trans22_r4_8,trans22_r4_9,trans22_r4_10,trans22_r4_11,trans22_r4_12,trans22_r4_13,trans22_r4_14,trans22_r4_15]
noncomputable def trans22 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans22_r0,trans22_r1,trans22_r2,trans22_r3,trans22_r4,trans22_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers40
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def trans34_r5 : Fin 16 → Fin 16 → CBox := ![trans34_r5_0,trans34_r5_1,trans34_r5_2,trans34_r5_3,trans34_r5_4,trans34_r5_5,trans34_r5_6,trans34_r5_7,trans34_r5_8,trans34_r5_9,trans34_r5_10,trans34_r5_11,trans34_r5_12,trans34_r5_13,trans34_r5_14,trans34_r5_15]
noncomputable def trans34 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans34_r0,trans34_r1,trans34_r2,trans34_r3,trans34_r4,trans34_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers50
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def trans50_r2 : Fin 16 → Fin 16 → CBox := ![trans50_r2_0,trans50_r2_1,trans50_r2_2,trans50_r2_3,trans50_r2_4,trans50_r2_5,trans50_r2_6,trans50_r2_7,trans50_r2_8,trans50_r2_9,trans50_r2_10,trans50_r2_11,trans50_r2_12,trans50_r2_13,trans50_r2_14,trans50_r2_15]
noncomputable def trans50 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans50_r0,trans50_r1,trans50_r2,trans50_r3,trans50_r4,trans50_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers70
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def trans66_r3 : Fin 16 → Fin 16 → CBox := ![trans66_r3_0,trans66_r3_1,trans66_r3_2,trans66_r3_3,trans66_r3_4,trans66_r3_5,trans66_r3_6,trans66_r3_7,trans66_r3_8,trans66_r3_9,trans66_r3_10,trans66_r3_11,trans66_r3_12,trans66_r3_13,trans66_r3_14,trans66_r3_15]
noncomputable def trans66 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans66_r0,trans66_r1,trans66_r2,trans66_r3,trans66_r4,trans66_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments73
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_73_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_73_0

namespace tm1_73_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_73_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments75
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_75_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_75_0

namespace tm1_75_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_75_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments76
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_76_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_76_0

namespace tm1_76_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_76_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments79
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_79_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_79_0

namespace tm1_79_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_79_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers90
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def trans83_r2 : Fin 16 → Fin 16 → CBox := ![trans83_r2_0,trans83_r2_1,trans83_r2_2,trans83_r2_3,trans83_r2_4,trans83_r2_5,trans83_r2_6,trans83_r2_7,trans83_r2_8,trans83_r2_9,trans83_r2_10,trans83_r2_11,trans83_r2_12,trans83_r2_13,trans83_r2_14,trans83_r2_15]
noncomputable def trans83 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans83_r0,trans83_r1,trans83_r2,trans83_r3,trans83_r4,trans83_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments81
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_81_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_81_0

namespace tm1_81_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_81_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments84
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_84_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_84_0

namespace tm1_84_1
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_84_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments85
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_85_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_85_0

namespace tm1_85_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_85_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments87
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_87_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_87_0

namespace tm1_87_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_87_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments88
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_88_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_88_0

namespace tm1_88_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_88_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments9
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_9_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_9_0

namespace tm1_9_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_9_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments91
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_91_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_91_0

namespace tm1_91_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_91_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments93
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_93_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_93_0

namespace tm1_93_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_93_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments96
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_96_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_96_0

namespace tm1_96_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_96_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments97
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_97_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_97_0

namespace tm1_97_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_97_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments99
attribute [-instance] _root_.OAI.SharpPlanar.IntegerIntervals.instDecidableSqNormCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical

namespace tm1_99_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_99_0

namespace tm1_99_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_99_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverse bounds for the central interpolation block

Exact rational approximate inverses give bounds for the two central blocks.
-/

namespace SharpPlanar.Numerical
lemma Wminus_norm : ‖matrixL1 Wminus‖ < (183:ℝ)/100 := matrixL1_norm_lt Wminus_column
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the interpolation operator

Coordinate projections and shell estimates bound the tails of the interpolation operator.
-/

namespace SharpPlanar.Numerical
open scoped BigOperators
lemma compressed_low_L : RL.comp (S.comp IJ) = matrixL1 Lmat := by
  rw [compressed_S_matrix]
  rfl
end SharpPlanar.Numerical

end OAI
end


