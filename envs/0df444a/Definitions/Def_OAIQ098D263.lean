-- Prove2me | Definitions.Def_OAIQ098D263
-- name    : OAIQ098D263
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:24:47.512406+00:00
-- url     : https://prove2.me/theorems/2f8c6b4a-2fa5-44eb-a038-231f1bc1ad3b
-- title:
--   Definitions bundle OAIQ098D263 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 955 declarations of OpenAI's Lean: 378 definitions, 6 instances and 571 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.amp1_1`, `OAI.SharpPlanar.CachedData.amp1_11`, `OAI.SharpPlanar.CachedData.amp1_15`, `OAI.SharpPlanar.CachedData.amp4_0`, `OAI.SharpPlanar.CachedData.amp4_01`, `OAI.SharpPlanar.CachedData.amp4_05`, `OAI.SharpPlanar.CachedData.amp7_1`, `OAI.SharpPlanar.CachedData.amp7_12`, `OAI.SharpPlanar.CachedData.atomPoint0`, `OAI.SharpPlanar.CachedData.atomPoint1`, `OAI.SharpPlanar.CachedData.atomPoint2`, `OAI.SharpPlanar.CachedData.atomPoint3`, `OAI.SharpPlanar.CachedData.atomPoint4`, `OAI.SharpPlanar.CachedData.atomPoint5`, `OAI.SharpPlanar.CachedData.atomPoint6`, `OAI.SharpPlanar.CachedData.atomPoints`, `OAI.SharpPlanar.CachedData.cm100_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm100_1_0_0.s0`, `OAI.SharpPlanar.CachedData.cm100_1_0_0.sums`, `OAI.SharpPlanar.CachedData.column100_0Expr`, `OAI.SharpPlanar.CachedData.kernel1_0`, `OAI.SharpPlanar.CachedData.kernel1_0_r0`, `OAI.SharpPlanar.CachedData.power82`, `OAI.SharpPlanar.CachedData.power93_r2`, `OAI.SharpPlanar.CachedData.power96`, `OAI.SharpPlanar.CachedData.power96_r3`, `OAI.SharpPlanar.CachedData.power99`, `OAI.SharpPlanar.CachedData.power99_r5`, `OAI.SharpPlanar.IntegerBasis.cachedMomentRuleBox`, `OAI.SharpPlanar.IntegerBasis.kernel0Box`, `OAI.SharpPlanar.IntegerBasis.phaseBase`, `OAI.SharpPlanar.IntegerBasis.phaseBox`, `OAI.SharpPlanar.IntegerCompact.nodeLookup`, `OAI.SharpPlanar.IntegerCompact.partialBox`, `OAI.SharpPlanar.IntegerCompact.rootLookup`, `OAI.SharpPlanar.IntegerCompact.rootRows`, `OAI.SharpPlanar.IntegerCompact.roots0`, `OAI.SharpPlanar.IntegerCompact.roots1`, `OAI.SharpPlanar.IntegerCompact.roots10`, `OAI.SharpPlanar.IntegerCompact.roots11` and 338 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_BasisIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean), [`PlanarPacking_Certificate_Amplitudes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Amplitudes.lean), [`PlanarPacking_Certificate_AtomKernels`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/AtomKernels.lean), [`PlanarPacking_Certificate_Columns100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns100.lean), [`PlanarPacking_Certificate_KernelValues10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues10.lean), [`PlanarPacking_Certificate_Powers100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers100.lean), [`PlanarPacking_Certificate_Powers90`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers90.lean), [`PlanarPacking_Certificate_UMoments100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments100.lean), [`PlanarPacking_Fejer`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean), [`PlanarPacking_Grid`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Grid.lean), [`PlanarPacking_Intervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean), [`PlanarPacking_Roots`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Roots.lean).
--
--   **Imports.** It imports the bundles `OAIQ098D006`, `OAIQ098D007`, `OAIQ098D008`, `OAIQ098D009`, `OAIQ098D010`, `OAIQ098D012`, `OAIQ098D013`, `OAIQ098D014`, `OAIQ098D015`, `OAIQ098D016`, `OAIQ098D017`, `OAIQ098D018`, `OAIQ098D019`, `OAIQ098D020`, `OAIQ098D021`, `OAIQ098D023`, `OAIQ098D024`, `OAIQ098D026`, `OAIQ098D027`, `OAIQ098D028`, `OAIQ098D029`, `OAIQ098D031`, `OAIQ098D032`, `OAIQ098D033`, `OAIQ098D034`, `OAIQ098D035`, `OAIQ098D036`, `OAIQ098D037`, `OAIQ098D038`, `OAIQ098D039`, `OAIQ098D040`, `OAIQ098D041`, `OAIQ098D042`, `OAIQ098D043`, `OAIQ098D044`, `OAIQ098D045`, `OAIQ098D046`, `OAIQ098D047`, `OAIQ098D048`, `OAIQ098D049`, `OAIQ098D052` and `OAIQ098D053` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D276`, `OAIQ098D277`, `OAIQ098D278`, `OAIQ098D279`, `OAIQ098D280`, `OAIQ098D281`, `OAIQ098D282`, `OAIQ098D283`, `OAIQ098D284`, `OAIQ098D285`, `OAIQ098D286`, `OAIQ098D287`, `OAIQ098D288`, `OAIQ098D289`, `OAIQ098D290`, `OAIQ098D291`, `OAIQ098D292`, `OAIQ098D293`, `OAIQ098D294`, `OAIQ098D295`, `OAIQ098D296`, `OAIQ098D297`, `OAIQ098D298`, `OAIQ098D299`, `OAIQ098D300`, `OAIQ098D301`, `OAIQ098D302`, `OAIQ098D303`, `OAIQ098D304`, `OAIQ098D305`, `OAIQ098D306`, `OAIQ098D307`, `OAIQ098D308`, `OAIQ098D309`, `OAIQ098D310`, `OAIQ098D311`, `OAIQ098D312`, `OAIQ098D313`, `OAIQ098D314`, `OAIQ098D315`, `OAIQ098D316`, `OAIQ098D317`, `OAIQ098D318`, `OAIQ098D319`, `OAIQ098D320`, `OAIQ098D321`, `OAIQ098D322`, `OAIQ098D323`, `OAIQ098D324`, `OAIQ098D325`, `OAIQ098D326`, `OAIQ098D327`, `OAIQ098D328`, `OAIQ098D329`, `OAIQ098D330`, `OAIQ098D331`, `OAIQ098D332`, `OAIQ098D333`, `OAIQ098D334`, `OAIQ098D335`, `OAIQ098D336`, `OAIQ098D337`, `OAIQ098D338`, `OAIQ098D339`, `OAIQ098D340`, `OAIQ098D341`, `OAIQ098D342`, `OAIQ098D343`, `OAIQ098D344`, `OAIQ098D345`, `OAIQ098D346`, `OAIQ098D347`, `OAIQ098D348`, `OAIQ098D349`, `OAIQ098D350`, `OAIQ098D351`, `OAIQ098D352`, `OAIQ098D353`, `OAIQ098D354`, `OAIQ098D355`, `OAIQ098D356`, `OAIQ098D357`, `OAIQ098D358`, `OAIQ098D359`, `OAIQ098D360`, `OAIQ098D361`, `OAIQ098D362`, `OAIQ098D363`, `OAIQ098D364`, `OAIQ098D365`, `OAIQ098D366`, `OAIQ098D367`, `OAIQ098D368`, `OAIQ098D369`, `OAIQ098D370`, `OAIQ098D371`, `OAIQ098D372`, `OAIQ098D373`, `OAIQ098D374`, `OAIQ098D375`, `OAIQ098D376`, `OAIQ098D377`, `OAIQ098D378`, `OAIQ098D379`, `OAIQ098D380`, `OAIQ098D381`, `OAIQ098D382`, `OAIQ098D383`, `OAIQ098D384`, `OAIQ098D385`, `OAIQ098D386`, `OAIQ098D387`, `OAIQ098D388`, `OAIQ098D389`, `OAIQ098D390`, `OAIQ098D391`, `OAIQ098D392`, `OAIQ098D393`, `OAIQ098D394`, `OAIQ098D395`, `OAIQ098D396`, `OAIQ098D397`, `OAIQ098D398`, `OAIQ098D399`, `OAIQ098D400`, `OAIQ098D401`, `OAIQ098D402`, `OAIQ098D403`, `OAIQ098D404`, `OAIQ098D405`, `OAIQ098D406`, `OAIQ098D407`, `OAIQ098D408`, `OAIQ098D409`, `OAIQ098D410`, `OAIQ098D411`, `OAIQ098D412`, `OAIQ098D413`, `OAIQ098D414`, `OAIQ098D415`, `OAIQ098D416`, `OAIQ098D417`, `OAIQ098D418`, `OAIQ098D419`, `OAIQ098D420`, `OAIQ098D421`, `OAIQ098D422`, `OAIQ098D423`, `OAIQ098D424`, `OAIQ098D425`, `OAIQ098D426`, `OAIQ098D427`, `OAIQ098D428`, `OAIQ098D429`, `OAIQ098D430`, `OAIQ098D431`, `OAIQ098D432`, `OAIQ098D433`, `OAIQ098D434`, `OAIQ098D435`, `OAIQ098D436`, `OAIQ098D437`, `OAIQ098D438`, `OAIQ098D439`, `OAIQ098D440`, `OAIQ098D441`, `OAIQ098D442`, `OAIQ098D443`, `OAIQ098D444`, `OAIQ098D445`, `OAIQ098D446`, `OAIQ098D447`, `OAIQ098D448`, `OAIQ098D449`, `OAIQ098D450`, `OAIQ098D451`, `OAIQ098D452`, `OAIQ098D453`, `OAIQ098D454`, `OAIQ098D455`, `OAIQ098D456`, `OAIQ098D457`, `OAIQ098D458`, `OAIQ098D459`, `OAIQ098D460`, `OAIQ098D461`, `OAIQ098D462`, `OAIQ098D463`, `OAIQ098D464` and `OAIQ098D466`; the statements `OAI.SharpPlanar.CachedData.atomPoint0_contains`, `OAI.SharpPlanar.CachedData.atomPoint1_contains`, `OAI.SharpPlanar.CachedData.atomPoint2_contains`, `OAI.SharpPlanar.CachedData.atomPoint3_contains`, `OAI.SharpPlanar.CachedData.atomPoint4_contains`, `OAI.SharpPlanar.CachedData.atomPoint5_contains`, `OAI.SharpPlanar.CachedData.atomPoint6_contains`, `OAI.SharpPlanar.IntegerBasis.kernel0Box_contains` and `OAI.SharpPlanar.cached_density_rule_contains`; the proofs of `OAI.SharpPlanar.CachedData.atomPoint0_contains`, `OAI.SharpPlanar.CachedData.atomPoint1_contains`, `OAI.SharpPlanar.CachedData.atomPoint2_contains`, `OAI.SharpPlanar.CachedData.atomPoint3_contains`, `OAI.SharpPlanar.CachedData.atomPoint4_contains`, `OAI.SharpPlanar.CachedData.atomPoint5_contains`, `OAI.SharpPlanar.CachedData.atomPoint6_contains` and `OAI.SharpPlanar.fullFactor_step_contains`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D006
import Definitions.Def_OAIQ098D007
import Definitions.Def_OAIQ098D008
import Definitions.Def_OAIQ098D009
import Definitions.Def_OAIQ098D010
import Definitions.Def_OAIQ098D012
import Definitions.Def_OAIQ098D013
import Definitions.Def_OAIQ098D014
import Definitions.Def_OAIQ098D015
import Definitions.Def_OAIQ098D016
import Definitions.Def_OAIQ098D017
import Definitions.Def_OAIQ098D018
import Definitions.Def_OAIQ098D019
import Definitions.Def_OAIQ098D020
import Definitions.Def_OAIQ098D021
import Definitions.Def_OAIQ098D023
import Definitions.Def_OAIQ098D024
import Definitions.Def_OAIQ098D026
import Definitions.Def_OAIQ098D027
import Definitions.Def_OAIQ098D028
import Definitions.Def_OAIQ098D029
import Definitions.Def_OAIQ098D031
import Definitions.Def_OAIQ098D032
import Definitions.Def_OAIQ098D033
import Definitions.Def_OAIQ098D034
import Definitions.Def_OAIQ098D035
import Definitions.Def_OAIQ098D036
import Definitions.Def_OAIQ098D037
import Definitions.Def_OAIQ098D038
import Definitions.Def_OAIQ098D039
import Definitions.Def_OAIQ098D040
import Definitions.Def_OAIQ098D041
import Definitions.Def_OAIQ098D042
import Definitions.Def_OAIQ098D043
import Definitions.Def_OAIQ098D044
import Definitions.Def_OAIQ098D045
import Definitions.Def_OAIQ098D046
import Definitions.Def_OAIQ098D047
import Definitions.Def_OAIQ098D048
import Definitions.Def_OAIQ098D049
import Definitions.Def_OAIQ098D052
import Definitions.Def_OAIQ098D053

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

instance instDecidableAddCheck_1 (a b c : CBox) : Decidable (a.AddCheck b c) := inferInstanceAs (Decidable (_ ∧ _))
instance instDecidableMulCheck_1 (a b c : CBox) : Decidable (a.MulCheck b c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

lemma CBox.mul_contains {a b c : CBox} {x y : ℂ} (hx : a.Contains x) (hy : b.Contains y)
    (hc : a.MulCheck b c) : c.Contains (x*y) := by
  have hrr := mul_bounds hx.1 hy.1
  have hri := mul_bounds hx.1 hy.2
  have hir := mul_bounds hx.2 hy.1
  have hii := mul_bounds hx.2 hy.2
  have h₁ : (c.re.lo:ℝ)*precision ≤ (mulLo a.re b.re:ℝ)-(mulHi a.im b.im:ℝ) := by exact_mod_cast hc.1
  have h₂ : (mulHi a.re b.re:ℝ)-(mulLo a.im b.im:ℝ) ≤ (c.re.hi:ℝ)*precision := by exact_mod_cast hc.2.1
  have h₃ : (c.im.lo:ℝ)*precision ≤ (mulLo a.re b.im:ℝ)+(mulLo a.im b.re:ℝ) := by exact_mod_cast hc.2.2.1
  have h₄ : (mulHi a.re b.im:ℝ)+(mulHi a.im b.re:ℝ) ≤ (c.im.hi:ℝ)*precision := by exact_mod_cast hc.2.2.2
  constructor <;> constructor
  · apply (mul_le_mul_iff_right₀ precision_pos).mp
    simp only [Complex.mul_re]
    nlinarith only [hrr.1,hii.2,h₁]
  · apply (mul_le_mul_iff_right₀ precision_pos).mp
    simp only [Complex.mul_re]
    nlinarith only [hrr.2,hii.1,h₂]
  · apply (mul_le_mul_iff_right₀ precision_pos).mp
    simp only [Complex.mul_im]
    nlinarith only [hri.1,hir.1,h₃]
  · apply (mul_le_mul_iff_right₀ precision_pos).mp
    simp only [Complex.mul_im]
    nlinarith only [hri.2,hir.2,h₄]


instance instDecidableRatCheck_1 (a : CBox) (mr nr mi ni : ℤ) : Decidable (a.RatCheck mr nr mi ni) :=
  inferInstanceAs (Decidable (_ ∧ _))
lemma CBox.neg_contains {a : CBox} {z : ℂ} (hz : a.Contains z) : a.neg.Contains (-z) :=
  ⟨RBox.neg_contains hz.1,RBox.neg_contains hz.2⟩

instance instDecidableScaleCheck_1 (a c : CBox) (m n : ℤ) : Decidable (a.ScaleCheck c m n) := inferInstanceAs (Decidable (_ ∧ _))
lemma CBox.scale_contains {a c : CBox} {z : ℂ} {m n : ℤ} (hz : a.Contains z)
    (hc : a.ScaleCheck c m n) : c.Contains (((m:ℂ)/n)*z) := by
  constructor
  · simpa using RBox.scale_contains hz.1 hc.1
  · simpa using RBox.scale_contains hz.2 hc.2

lemma CBox.norm_le {a : CBox} {z : ℂ} {n : ℤ} (hz : a.Contains z) (hc : a.NormCheck n) :
    ‖z‖ ≤ (n:ℝ) := by
  have h₁ := RBox.abs_bound hz.1
  have h₂ := RBox.abs_bound hz.2
  have hc' : (a.re.bound:ℝ)+a.im.bound ≤ (precision:ℝ)*n := by exact_mod_cast hc
  have hh := mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im z) precision_pos.le
  apply (mul_le_mul_iff_right₀ precision_pos).mp
  nlinarith only [h₁,h₂,hc',hh]

instance instDecidableWidenCheck (a c : CBox) (n : ℤ) : Decidable (a.WidenCheck c n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
lemma CBox.widen_contains {a c : CBox} {z w : ℂ} {n : ℤ} (hz : a.Contains z)
    (herr : (precision:ℝ)*‖w-z‖ ≤ (n:ℝ)) (hc : a.WidenCheck c n) : c.Contains w := by
  have hr : (precision:ℝ)*|(w-z).re| ≤ (n:ℝ) :=
    (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm (w-z)) precision_pos.le).trans herr
  have hi : (precision:ℝ)*|(w-z).im| ≤ (n:ℝ) :=
    (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm (w-z)) precision_pos.le).trans herr
  have hra : |(precision:ℝ)*(w-z).re| ≤ (n:ℝ) := by simpa [abs_mul,abs_of_pos precision_pos] using hr
  have hia : |(precision:ℝ)*(w-z).im| ≤ (n:ℝ) := by simpa [abs_mul,abs_of_pos precision_pos] using hi
  rcases abs_le.mp hra with ⟨hrl,hru⟩
  rcases abs_le.mp hia with ⟨hil,hiu⟩
  have h₁ : (c.re.lo:ℝ) ≤ (a.re.lo:ℝ)-n := by exact_mod_cast hc.1
  have h₂ : (a.re.hi:ℝ)+n ≤ (c.re.hi:ℝ) := by exact_mod_cast hc.2.1
  have h₃ : (c.im.lo:ℝ) ≤ (a.im.lo:ℝ)-n := by exact_mod_cast hc.2.2.1
  have h₄ : (a.im.hi:ℝ)+n ≤ (c.im.hi:ℝ) := by exact_mod_cast hc.2.2.2
  simp only [Complex.sub_re] at hrl hru
  simp only [Complex.sub_im] at hil hiu
  exact ⟨⟨by nlinarith only [hz.1.1,hrl,h₁],by nlinarith only [hz.1.2,hru,h₂]⟩,
    ⟨by nlinarith only [hz.2.1,hil,h₃],by nlinarith only [hz.2.2,hiu,h₄]⟩⟩

lemma horner_step {a b p m c : CBox} {z : ℂ} {k n : ℕ}
    (hz : a.Contains z) (hb : b.Contains (expHorner z (k+1) n))
    (hp : p.RatCheck 1 (k.factorial:ℤ) 0 1) (hm : a.MulCheck b m)
    (hc : p.AddCheck m c) : c.Contains (expHorner z k (n+1)) := by
  have hr : p.Contains ((k.factorial:ℂ)⁻¹) := by simpa using CBox.rat_contains hp
  exact CBox.add_contains hr (CBox.mul_contains hz hb hm) hc

lemma exp_from_horner {a b c : CBox} {z : ℂ} (hz : a.Contains z)
    (hn : a.NormCheck 1) (hb : b.Contains (expHorner z 0 32))
    (hc : b.WidenCheck c 1) : c.Contains (Complex.exp z) := by
  apply CBox.widen_contains hb _ hc
  simpa using exp_small_error (by simpa using CBox.norm_le hz hn)

lemma power_mul {a b c : CBox} {z : ℂ} {j k : ℕ}
    (ha : a.Contains (z^j)) (hb : b.Contains (z^k)) (hc : a.MulCheck b c) :
    c.Contains (z^(j+k)) := by rw [pow_add]; exact CBox.mul_contains ha hb hc


lemma CBox.inv_checked {a c : CBox} {rr ii den dinv : RBox} {z : ℂ}
    (hz : a.Contains z) (hrr : a.re.MulCheck a.re rr) (hii : a.im.MulCheck a.im ii)
    (hs : rr.AddCheck ii den) (hi : den.InvCheck dinv)
    (hr : a.re.MulCheck dinv c.re) (him : a.im.neg.MulCheck dinv c.im) :
    c.Contains z⁻¹ := by
  have hden : den.Contains (Complex.normSq z) :=
    RBox.add_contains (RBox.mul_contains hz.1 hz.1 hrr) (RBox.mul_contains hz.2 hz.2 hii) hs
  have hdinv := RBox.inv_contains hden hi
  constructor
  · simpa [Complex.inv_re,div_eq_mul_inv] using RBox.mul_contains hz.1 hdinv hr
  · simpa [Complex.inv_im,div_eq_mul_inv] using RBox.mul_contains (RBox.neg_contains hz.2) hdinv him

lemma CBox.ofReal_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (⟨a,⟨0,0⟩⟩ : CBox).Contains (x:ℂ) := by
  exact ⟨hx,by simp [RBox.Contains]⟩

end IntegerIntervals
end SharpPlanar

namespace SharpPlanar.IntegerIntervals

def CBox.horner (a : CBox) (k : ℕ) : ℕ → CBox
  | 0 => CBox.rat 1 (k.factorial:ℤ) 0 1
  | n+1 => (CBox.rat 1 (k.factorial:ℤ) 0 1).add (a.mul (a.horner (k+1) n))
def CBox.squareIter (a : CBox) : ℕ → CBox
  | 0 => a
  | n+1 => let b := a.squareIter n; b.mul b
def CBox.exp (a : CBox) (k : ℕ := 11) : CBox :=
  (((a.scale 1 (2^k)).horner 0 32).widen 1).squareIter k

lemma CBox.rat_check (mr nr mi ni : ℤ) (hr : 0 < nr) (hi : 0 < ni) :
    (CBox.rat mr nr mi ni).RatCheck mr nr mi ni :=
  ⟨RBox.rat_check _ _ hr,RBox.rat_check _ _ hi⟩
lemma CBox.add_check (a b : CBox) : a.AddCheck b (a.add b) :=
  ⟨RBox.add_check _ _,RBox.add_check _ _⟩
lemma CBox.mul_check (a b : CBox) : a.MulCheck b (a.mul b) :=
  ⟨floor_mul_le _ (by norm_num [precision]),le_ceil_mul _ (by norm_num [precision]),
   floor_mul_le _ (by norm_num [precision]),le_ceil_mul _ (by norm_num [precision])⟩
lemma CBox.scale_check (a : CBox) (m n : ℤ) (hn : 0 < n) : a.ScaleCheck (a.scale m n) m n :=
  ⟨RBox.scale_check _ _ _ hn,RBox.scale_check _ _ _ hn⟩
lemma CBox.widen_check (a : CBox) (k : ℤ) : a.WidenCheck (a.widen k) k := by
  exact ⟨le_rfl,le_rfl,le_rfl,le_rfl⟩

lemma CBox.contains_rat (mr nr mi ni : ℤ) (hr : 0 < nr) (hi : 0 < ni) :
    (CBox.rat mr nr mi ni).Contains ((mr:ℂ)/nr+(mi:ℂ)/ni*Complex.I) :=
  CBox.rat_contains (CBox.rat_check _ _ _ _ hr hi)
lemma CBox.contains_add {a b : CBox} {x y : ℂ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := CBox.add_contains hx hy (CBox.add_check _ _)
lemma CBox.contains_mul {a b : CBox} {x y : ℂ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := CBox.mul_contains hx hy (CBox.mul_check _ _)
lemma CBox.contains_scale {a : CBox} {z : ℂ} (hz : a.Contains z) (m n : ℤ) (hn : 0 < n) :
    (a.scale m n).Contains (((m:ℂ)/n)*z) := CBox.scale_contains hz (CBox.scale_check _ _ _ hn)
lemma CBox.contains_horner {a : CBox} {z : ℂ} (hz : a.Contains z) (k n : ℕ) :
    (a.horner k n).Contains (expHorner z k n) := by
  induction n generalizing k with
  | zero =>
    simpa [CBox.horner,expHorner] using CBox.contains_rat 1 (k.factorial:ℤ) 0 1
      (by exact_mod_cast Nat.factorial_pos k) (by norm_num)
  | succ n ih =>
    exact horner_step hz (ih (k+1)) (CBox.rat_check _ _ _ _
      (by exact_mod_cast Nat.factorial_pos k) (by norm_num))
      (CBox.mul_check _ _) (CBox.add_check _ _)
lemma CBox.contains_squareIter {a : CBox} {z : ℂ} (hz : a.Contains z) (k : ℕ) :
    (a.squareIter k).Contains (z^(2^k)) := by
  induction k with
  | zero => simpa [CBox.squareIter] using hz
  | succ k ih =>
    rw [pow_succ,show 2^k*2=2^k+2^k from by omega,pow_add]
    exact CBox.contains_mul ih ih
lemma CBox.contains_exp {a : CBox} {z : ℂ} (hz : a.Contains z) (k : ℕ)
    (hn : (a.scale 1 (2^k)).NormCheck 1) : (a.exp k).Contains (Complex.exp z) := by
  have he := exp_from_horner (CBox.contains_scale hz 1 (2^k) (by positivity)) hn
    (CBox.contains_horner (CBox.contains_scale hz 1 (2^k) (by positivity)) 0 32)
    (CBox.widen_check _ 1)
  have hs := CBox.contains_squareIter he k
  rw [← Complex.exp_nat_mul] at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  push_cast
  field_simp


lemma CBox.contains_inv {a : CBox} {z : ℂ} (hz : a.Contains z)
    (hi : ((a.re.mul a.re).add (a.im.mul a.im)).InvCheck
      ((a.re.mul a.re).add (a.im.mul a.im)).inv) :
    a.inv.Contains z⁻¹ :=
  CBox.inv_checked hz (RBox.mul_check _ _) (RBox.mul_check _ _) (RBox.add_check _ _)
    hi (RBox.mul_check _ _) (RBox.mul_check _ _)

def CBox.powBin (a : CBox) : ℕ → ℕ → CBox
  | 0, _ => CBox.rat 1 1 0 1
  | k+1, n =>
    let b := a.powBin k (n/2)
    let b2 := b.mul b
    if n%2 = 0 then b2 else b2.mul a

lemma CBox.contains_powBin {a : CBox} {z : ℂ} (hz : a.Contains z) (k n : ℕ)
    (hn : n < 2^k) : (a.powBin k n).Contains (z^n) := by
  induction k generalizing n with
  | zero =>
    have : n=0 := by simpa using hn
    subst n
    simpa [CBox.powBin] using CBox.contains_rat 1 1 0 1 (by norm_num) (by norm_num)
  | succ k ih =>
    have hd : n/2 < 2^k := by rw [pow_succ] at hn; omega
    have he : n%2+2*(n/2)=n := Nat.mod_add_div n 2
    have hb := CBox.contains_mul (ih (n/2) hd) (ih (n/2) hd)
    rw [← pow_add] at hb
    dsimp only [CBox.powBin]
    split_ifs with h
    · convert hb using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      omega
    · have hh := CBox.contains_mul hb hz
      rw [← pow_succ] at hh
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      omega

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerIntervals

def lamDenBox (a : RBox) : CBox := (rcast bBounds).mul (denBox a)
def lamBox (a : RBox) : CBox := (CBox.rat 0 1 1 1).mul (lamDenBox a).inv
def zBox (a : RBox) : CBox := ((denBox a).inv.scale (-4) 3).add (CBox.rat 0 1 (-2) 5)
def directArgBox (a : RBox) : CBox := (piI.mul (rcast a)).neg
def quarterArgBox (a : RBox) : CBox := (piI.mul (zBox a)).scale 1 4

def PointBox.Check (a : RBox) : Prop :=
  (denBox a).GoodInv ∧ (lamDenBox a).GoodInv ∧
  ((directArgBox a).scale 1 8).NormCheck 1 ∧
  ((quarterArgBox a).scale 1 8).NormCheck 1
instance instDecidableCheck (a : RBox) : Decidable (PointBox.Check a) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def PointBox.calc (a : RBox) : PointBox :=
  ⟨a,lamBox a,zBox a,(directArgBox a).exp 3,(quarterArgBox a).exp 3⟩

def PointBox.Contains (a : PointBox) (x : ℝ) : Prop :=
  a.t.Contains x ∧ a.lam.Contains (pointLambda x) ∧ a.z.Contains (pointZ x) ∧
  a.direct.Contains (Complex.exp (-Complex.I*Real.pi*x)) ∧
  a.quarter.Contains (Complex.exp (Complex.I*Real.pi*pointZ x/4))

lemma rcast_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (rcast a).Contains (x:ℂ) := CBox.ofReal_contains hx
lemma piI_contains : piI.Contains (Complex.I*Real.pi) := by
  constructor
  · norm_num [CBox.Contains,RBox.Contains,piI]
  · simpa [piI] using piBounds_contains
lemma denBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (denBox a).Contains ((x:ℂ)+Complex.I*(2/5:ℂ)) := by
  constructor
  · simpa [denBox] using hx
  · simpa [denBox] using RBox.contains_rat 2 5 (by norm_num)
lemma lamDenBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (lamDenBox a).Contains (((Real.sqrt 3/2:ℝ):ℂ)*((x:ℂ)+Complex.I*(2/5:ℂ))) :=
  CBox.contains_mul (rcast_contains bBounds_contains) (denBox_contains hx)
lemma lamBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hi : (lamDenBox a).GoodInv) : (lamBox a).Contains (pointLambda x) := by
  have hI : (CBox.rat 0 1 1 1).Contains Complex.I := by
    simpa using CBox.contains_rat 0 1 1 1 (by norm_num) (by norm_num)
  simpa only [lamBox,pointLambda,div_eq_mul_inv] using
    CBox.contains_mul hI (CBox.contains_inv (lamDenBox_contains hx) hi)
lemma zBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hi : (denBox a).GoodInv) : (zBox a).Contains (pointZ x) := by
  have hc : (CBox.rat 0 1 (-2) 5).Contains (-Complex.I*(2/5:ℂ)) := by
    convert CBox.contains_rat 0 1 (-2) 5 (by norm_num) (by norm_num) using 1 <;> first | rfl | ring
  have hh := CBox.contains_add
    (CBox.contains_scale (CBox.contains_inv (denBox_contains hx) hi) (-4) 3 (by norm_num)) hc
  unfold zBox
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [pointZ,div_eq_mul_inv,sub_eq_add_neg]
  ring
lemma directArgBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x) :
    (directArgBox a).Contains (-Complex.I*Real.pi*x) := by
  simpa only [directArgBox,neg_mul] using CBox.neg_contains (CBox.contains_mul piI_contains (rcast_contains hx))
lemma quarterArgBox_contains {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hi : (denBox a).GoodInv) :
    (quarterArgBox a).Contains (Complex.I*Real.pi*pointZ x/4) := by
  have hh := CBox.contains_scale (CBox.contains_mul piI_contains (zBox_contains hx hi)) 1 4 (by norm_num)
  unfold quarterArgBox
  convert hh using 1 <;> first | rfl | ring

lemma PointBox.calc_contains {a : RBox} {x : ℝ} (hx : a.Contains x)
    (hc : PointBox.Check a) : (PointBox.calc a).Contains x := by
  exact ⟨hx,lamBox_contains hx hc.2.1,zBox_contains hx hc.1,
    CBox.contains_exp (directArgBox_contains hx) 3 hc.2.2.1,
    CBox.contains_exp (quarterArgBox_contains hx hc.1) 3 hc.2.2.2⟩

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Roots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Certified roots of unity

Integer enclosures for the 1024th roots of unity, obtained from a certified
Taylor approximation and repeated squaring.
-/

namespace SharpPlanar
namespace IntegerRoots
open IntegerIntervals
lemma fact0_check : fact0.RatCheck 1 1 0 1 := by decide +kernel
lemma fact1_check : fact1.RatCheck 1 1 0 1 := by decide +kernel
lemma fact2_check : fact2.RatCheck 1 2 0 1 := by decide +kernel
lemma fact3_check : fact3.RatCheck 1 6 0 1 := by decide +kernel
lemma fact4_check : fact4.RatCheck 1 24 0 1 := by decide +kernel
lemma fact5_check : fact5.RatCheck 1 120 0 1 := by decide +kernel
lemma fact6_check : fact6.RatCheck 1 720 0 1 := by decide +kernel
lemma fact7_check : fact7.RatCheck 1 5040 0 1 := by decide +kernel
lemma fact8_check : fact8.RatCheck 1 40320 0 1 := by decide +kernel
lemma fact9_check : fact9.RatCheck 1 362880 0 1 := by decide +kernel
lemma fact10_check : fact10.RatCheck 1 3628800 0 1 := by decide +kernel
lemma fact11_check : fact11.RatCheck 1 39916800 0 1 := by decide +kernel
lemma fact12_check : fact12.RatCheck 1 479001600 0 1 := by decide +kernel
lemma fact13_check : fact13.RatCheck 1 6227020800 0 1 := by decide +kernel
lemma fact14_check : fact14.RatCheck 1 87178291200 0 1 := by decide +kernel
lemma fact15_check : fact15.RatCheck 1 1307674368000 0 1 := by decide +kernel
lemma fact16_check : fact16.RatCheck 1 20922789888000 0 1 := by decide +kernel
lemma fact17_check : fact17.RatCheck 1 355687428096000 0 1 := by decide +kernel
lemma fact18_check : fact18.RatCheck 1 6402373705728000 0 1 := by decide +kernel
lemma fact19_check : fact19.RatCheck 1 121645100408832000 0 1 := by decide +kernel
lemma fact20_check : fact20.RatCheck 1 2432902008176640000 0 1 := by decide +kernel
lemma fact21_check : fact21.RatCheck 1 51090942171709440000 0 1 := by decide +kernel
lemma fact22_check : fact22.RatCheck 1 1124000727777607680000 0 1 := by decide +kernel
lemma fact23_check : fact23.RatCheck 1 25852016738884976640000 0 1 := by decide +kernel
lemma fact24_check : fact24.RatCheck 1 620448401733239439360000 0 1 := by decide +kernel
lemma fact25_check : fact25.RatCheck 1 15511210043330985984000000 0 1 := by decide +kernel
lemma fact26_check : fact26.RatCheck 1 403291461126605635584000000 0 1 := by decide +kernel
lemma fact27_check : fact27.RatCheck 1 10888869450418352160768000000 0 1 := by decide +kernel
lemma fact28_check : fact28.RatCheck 1 304888344611713860501504000000 0 1 := by decide +kernel
lemma fact29_check : fact29.RatCheck 1 8841761993739701954543616000000 0 1 := by decide +kernel
lemma fact30_check : fact30.RatCheck 1 265252859812191058636308480000000 0 1 := by decide +kernel
lemma fact31_check : fact31.RatCheck 1 8222838654177922817725562880000000 0 1 := by decide +kernel
lemma fact32_check : fact32.RatCheck 1 263130836933693530167218012160000000 0 1 := by decide +kernel
lemma phaseInput_contains : phaseInput.Contains (Complex.I*Real.pi/512) := by
  constructor
  · norm_num [phaseInput,RBox.Contains,Complex.mul_re,Complex.I_re,Complex.I_im]
  · have hh := RBox.scale_contains piBounds_contains
      (c:=phaseInput.im) (m:=1) (n:=512) (by decide +kernel)
    simpa [div_eq_mul_inv,mul_comm] using hh
lemma small_contains : small.Contains ((1/2048:ℂ)*(Complex.I*Real.pi/512)) := by
  simpa using CBox.scale_contains phaseInput_contains (c:=small) (m:=1) (n:=2048) (by decide +kernel)
lemma h32 : poly32.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 32 0) := by
  simpa [expHorner,poly32,Nat.factorial] using CBox.rat_contains fact32_check
lemma h31 : poly31.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 31 1) := by
  exact horner_step small_contains h32 fact31_check (m:=mul31) (by decide +kernel) (by decide +kernel)
lemma h30 : poly30.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 30 2) := by
  exact horner_step small_contains h31 fact30_check (m:=mul30) (by decide +kernel) (by decide +kernel)
lemma h29 : poly29.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 29 3) := by
  exact horner_step small_contains h30 fact29_check (m:=mul29) (by decide +kernel) (by decide +kernel)
lemma h28 : poly28.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 28 4) := by
  exact horner_step small_contains h29 fact28_check (m:=mul28) (by decide +kernel) (by decide +kernel)
lemma h27 : poly27.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 27 5) := by
  exact horner_step small_contains h28 fact27_check (m:=mul27) (by decide +kernel) (by decide +kernel)
lemma h26 : poly26.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 26 6) := by
  exact horner_step small_contains h27 fact26_check (m:=mul26) (by decide +kernel) (by decide +kernel)
lemma h25 : poly25.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 25 7) := by
  exact horner_step small_contains h26 fact25_check (m:=mul25) (by decide +kernel) (by decide +kernel)
lemma h24 : poly24.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 24 8) := by
  exact horner_step small_contains h25 fact24_check (m:=mul24) (by decide +kernel) (by decide +kernel)
lemma h23 : poly23.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 23 9) := by
  exact horner_step small_contains h24 fact23_check (m:=mul23) (by decide +kernel) (by decide +kernel)
lemma h22 : poly22.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 22 10) := by
  exact horner_step small_contains h23 fact22_check (m:=mul22) (by decide +kernel) (by decide +kernel)
lemma h21 : poly21.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 21 11) := by
  exact horner_step small_contains h22 fact21_check (m:=mul21) (by decide +kernel) (by decide +kernel)
lemma h20 : poly20.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 20 12) := by
  exact horner_step small_contains h21 fact20_check (m:=mul20) (by decide +kernel) (by decide +kernel)
lemma h19 : poly19.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 19 13) := by
  exact horner_step small_contains h20 fact19_check (m:=mul19) (by decide +kernel) (by decide +kernel)
lemma h18 : poly18.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 18 14) := by
  exact horner_step small_contains h19 fact18_check (m:=mul18) (by decide +kernel) (by decide +kernel)
lemma h17 : poly17.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 17 15) := by
  exact horner_step small_contains h18 fact17_check (m:=mul17) (by decide +kernel) (by decide +kernel)
lemma h16 : poly16.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 16 16) := by
  exact horner_step small_contains h17 fact16_check (m:=mul16) (by decide +kernel) (by decide +kernel)
lemma h15 : poly15.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 15 17) := by
  exact horner_step small_contains h16 fact15_check (m:=mul15) (by decide +kernel) (by decide +kernel)
lemma h14 : poly14.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 14 18) := by
  exact horner_step small_contains h15 fact14_check (m:=mul14) (by decide +kernel) (by decide +kernel)
lemma h13 : poly13.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 13 19) := by
  exact horner_step small_contains h14 fact13_check (m:=mul13) (by decide +kernel) (by decide +kernel)
lemma h12 : poly12.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 12 20) := by
  exact horner_step small_contains h13 fact12_check (m:=mul12) (by decide +kernel) (by decide +kernel)
lemma h11 : poly11.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 11 21) := by
  exact horner_step small_contains h12 fact11_check (m:=mul11) (by decide +kernel) (by decide +kernel)
lemma h10 : poly10.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 10 22) := by
  exact horner_step small_contains h11 fact10_check (m:=mul10) (by decide +kernel) (by decide +kernel)
lemma h9 : poly9.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 9 23) := by
  exact horner_step small_contains h10 fact9_check (m:=mul9) (by decide +kernel) (by decide +kernel)
lemma h8 : poly8.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 8 24) := by
  exact horner_step small_contains h9 fact8_check (m:=mul8) (by decide +kernel) (by decide +kernel)
lemma h7 : poly7.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 7 25) := by
  exact horner_step small_contains h8 fact7_check (m:=mul7) (by decide +kernel) (by decide +kernel)
lemma h6 : poly6.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 6 26) := by
  exact horner_step small_contains h7 fact6_check (m:=mul6) (by decide +kernel) (by decide +kernel)
lemma h5 : poly5.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 5 27) := by
  exact horner_step small_contains h6 fact5_check (m:=mul5) (by decide +kernel) (by decide +kernel)
lemma h4 : poly4.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 4 28) := by
  exact horner_step small_contains h5 fact4_check (m:=mul4) (by decide +kernel) (by decide +kernel)
lemma h3 : poly3.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 3 29) := by
  exact horner_step small_contains h4 fact3_check (m:=mul3) (by decide +kernel) (by decide +kernel)
lemma h2 : poly2.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 2 30) := by
  exact horner_step small_contains h3 fact2_check (m:=mul2) (by decide +kernel) (by decide +kernel)
lemma h1 : poly1.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 1 31) := by
  exact horner_step small_contains h2 fact1_check (m:=mul1) (by decide +kernel) (by decide +kernel)
lemma h0 : poly0.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 0 32) := by
  exact horner_step small_contains h1 fact0_check (m:=mul0) (by decide +kernel) (by decide +kernel)
lemma sq0_contains : sq0.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^0)) := by
  simpa using exp_from_horner small_contains (b:=poly0) (c:=sq0) (by decide +kernel) h0 (by decide +kernel)
lemma sq1_contains : sq1.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^1)) := by
  exact power_mul sq0_contains sq0_contains (by decide +kernel)
lemma sq2_contains : sq2.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^2)) := by
  exact power_mul sq1_contains sq1_contains (by decide +kernel)
lemma sq3_contains : sq3.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^3)) := by
  exact power_mul sq2_contains sq2_contains (by decide +kernel)
lemma sq4_contains : sq4.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^4)) := by
  exact power_mul sq3_contains sq3_contains (by decide +kernel)
lemma sq5_contains : sq5.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^5)) := by
  exact power_mul sq4_contains sq4_contains (by decide +kernel)
lemma sq6_contains : sq6.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^6)) := by
  exact power_mul sq5_contains sq5_contains (by decide +kernel)
lemma sq7_contains : sq7.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^7)) := by
  exact power_mul sq6_contains sq6_contains (by decide +kernel)
lemma sq8_contains : sq8.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^8)) := by
  exact power_mul sq7_contains sq7_contains (by decide +kernel)
lemma sq9_contains : sq9.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^9)) := by
  exact power_mul sq8_contains sq8_contains (by decide +kernel)
lemma sq10_contains : sq10.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^10)) := by
  exact power_mul sq9_contains sq9_contains (by decide +kernel)
lemma sq11_contains : sq11.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^11)) := by
  exact power_mul sq10_contains sq10_contains (by decide +kernel)
lemma phase_contains : sq11.Contains (rootPhase 1) := by
  have hh := sq11_contains
  rw [← Complex.exp_nat_mul] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold rootPhase
  congr 1
  norm_num
  ring
lemma root0_contains : root0.Contains (rootPhase 0) := by
  simpa [rootPhase] using CBox.rat_contains (a:=root0) (mr:=1) (nr:=1) (mi:=0) (ni:=1) (by decide +kernel)
lemma root1_contains : root1.Contains (rootPhase 1) := phase_contains
lemma root2_contains : root2.Contains (rootPhase 2) := by
  have hh := CBox.mul_contains root1_contains root1_contains (c:=root2) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid3_contains : mid3.Contains (rootPhase 2) := root2_contains
lemma root3_contains : root3.Contains (rootPhase 3) := by
  have hh := CBox.mul_contains mid3_contains root1_contains (c:=root3) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root4_contains : root4.Contains (rootPhase 4) := by
  have hh := CBox.mul_contains root2_contains root2_contains (c:=root4) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid5_contains : mid5.Contains (rootPhase 4) := root4_contains
lemma root5_contains : root5.Contains (rootPhase 5) := by
  have hh := CBox.mul_contains mid5_contains root1_contains (c:=root5) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root6_contains : root6.Contains (rootPhase 6) := by
  have hh := CBox.mul_contains root3_contains root3_contains (c:=root6) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root8_contains : root8.Contains (rootPhase 8) := by
  have hh := CBox.mul_contains root4_contains root4_contains (c:=root8) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root10_contains : root10.Contains (rootPhase 10) := by
  have hh := CBox.mul_contains root5_contains root5_contains (c:=root10) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root12_contains : root12.Contains (rootPhase 12) := by
  have hh := CBox.mul_contains root6_contains root6_contains (c:=root12) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root16_contains : root16.Contains (rootPhase 16) := by
  have hh := CBox.mul_contains root8_contains root8_contains (c:=root16) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root20_contains : root20.Contains (rootPhase 20) := by
  have hh := CBox.mul_contains root10_contains root10_contains (c:=root20) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root24_contains : root24.Contains (rootPhase 24) := by
  have hh := CBox.mul_contains root12_contains root12_contains (c:=root24) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root32_contains : root32.Contains (rootPhase 32) := by
  have hh := CBox.mul_contains root16_contains root16_contains (c:=root32) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid33 : CBox := root32
lemma mid33_contains : mid33.Contains (rootPhase 32) := root32_contains
lemma root33_contains : root33.Contains (rootPhase 33) := by
  have hh := CBox.mul_contains mid33_contains root1_contains (c:=root33) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid35 : CBox := root34
def mid37 : CBox := root36
def mid39 : CBox := root38
lemma root40_contains : root40.Contains (rootPhase 40) := by
  have hh := CBox.mul_contains root20_contains root20_contains (c:=root40) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root48_contains : root48.Contains (rootPhase 48) := by
  have hh := CBox.mul_contains root24_contains root24_contains (c:=root48) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid51 : CBox := root50
def mid53 : CBox := root52
def mid55 : CBox := root54
def mid57 : CBox := root56
def mid59 : CBox := root58
def mid61 : CBox := root60
def mid63 : CBox := root62
lemma root64_contains : root64.Contains (rootPhase 64) := by
  have hh := CBox.mul_contains root32_contains root32_contains (c:=root64) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid65_contains : mid65.Contains (rootPhase 64) := root64_contains
lemma root65_contains : root65.Contains (rootPhase 65) := by
  have hh := CBox.mul_contains mid65_contains root1_contains (c:=root65) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root66_contains : root66.Contains (rootPhase 66) := by
  have hh := CBox.mul_contains root33_contains root33_contains (c:=root66) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid67_contains : mid67.Contains (rootPhase 66) := root66_contains
lemma root67_contains : root67.Contains (rootPhase 67) := by
  have hh := CBox.mul_contains mid67_contains root1_contains (c:=root67) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root80_contains : root80.Contains (rootPhase 80) := by
  have hh := CBox.mul_contains root40_contains root40_contains (c:=root80) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid81_contains : mid81.Contains (rootPhase 80) := root80_contains
lemma root81_contains : root81.Contains (rootPhase 81) := by
  have hh := CBox.mul_contains mid81_contains root1_contains (c:=root81) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root96_contains : root96.Contains (rootPhase 96) := by
  have hh := CBox.mul_contains root48_contains root48_contains (c:=root96) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid97_contains : mid97.Contains (rootPhase 96) := root96_contains
lemma root97_contains : root97.Contains (rootPhase 97) := by
  have hh := CBox.mul_contains mid97_contains root1_contains (c:=root97) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root128_contains : root128.Contains (rootPhase 128) := by
  have hh := CBox.mul_contains root64_contains root64_contains (c:=root128) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid129_contains : mid129.Contains (rootPhase 128) := root128_contains
lemma root129_contains : root129.Contains (rootPhase 129) := by
  have hh := CBox.mul_contains mid129_contains root1_contains (c:=root129) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root130_contains : root130.Contains (rootPhase 130) := by
  have hh := CBox.mul_contains root65_contains root65_contains (c:=root130) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid131_contains : mid131.Contains (rootPhase 130) := root130_contains
lemma root131_contains : root131.Contains (rootPhase 131) := by
  have hh := CBox.mul_contains mid131_contains root1_contains (c:=root131) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root132_contains : root132.Contains (rootPhase 132) := by
  have hh := CBox.mul_contains root66_contains root66_contains (c:=root132) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid133_contains : mid133.Contains (rootPhase 132) := root132_contains
lemma root133_contains : root133.Contains (rootPhase 133) := by
  have hh := CBox.mul_contains mid133_contains root1_contains (c:=root133) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root134_contains : root134.Contains (rootPhase 134) := by
  have hh := CBox.mul_contains root67_contains root67_contains (c:=root134) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid135_contains : mid135.Contains (rootPhase 134) := root134_contains
lemma root135_contains : root135.Contains (rootPhase 135) := by
  have hh := CBox.mul_contains mid135_contains root1_contains (c:=root135) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root160_contains : root160.Contains (rootPhase 160) := by
  have hh := CBox.mul_contains root80_contains root80_contains (c:=root160) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid161_contains : mid161.Contains (rootPhase 160) := root160_contains
lemma root161_contains : root161.Contains (rootPhase 161) := by
  have hh := CBox.mul_contains mid161_contains root1_contains (c:=root161) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root162_contains : root162.Contains (rootPhase 162) := by
  have hh := CBox.mul_contains root81_contains root81_contains (c:=root162) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid163_contains : mid163.Contains (rootPhase 162) := root162_contains
lemma root163_contains : root163.Contains (rootPhase 163) := by
  have hh := CBox.mul_contains mid163_contains root1_contains (c:=root163) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root192_contains : root192.Contains (rootPhase 192) := by
  have hh := CBox.mul_contains root96_contains root96_contains (c:=root192) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid193_contains : mid193.Contains (rootPhase 192) := root192_contains
lemma root193_contains : root193.Contains (rootPhase 193) := by
  have hh := CBox.mul_contains mid193_contains root1_contains (c:=root193) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root194_contains : root194.Contains (rootPhase 194) := by
  have hh := CBox.mul_contains root97_contains root97_contains (c:=root194) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid195_contains : mid195.Contains (rootPhase 194) := root194_contains
lemma root195_contains : root195.Contains (rootPhase 195) := by
  have hh := CBox.mul_contains mid195_contains root1_contains (c:=root195) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root256_contains : root256.Contains (rootPhase 256) := by
  have hh := CBox.mul_contains root128_contains root128_contains (c:=root256) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid257 : CBox := root256
lemma mid257_contains : mid257.Contains (rootPhase 256) := root256_contains
lemma root257_contains : root257.Contains (rootPhase 257) := by
  have hh := CBox.mul_contains mid257_contains root1_contains (c:=root257) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root258_contains : root258.Contains (rootPhase 258) := by
  have hh := CBox.mul_contains root129_contains root129_contains (c:=root258) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid259_contains : mid259.Contains (rootPhase 258) := root258_contains
lemma root259_contains : root259.Contains (rootPhase 259) := by
  have hh := CBox.mul_contains mid259_contains root1_contains (c:=root259) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root260_contains : root260.Contains (rootPhase 260) := by
  have hh := CBox.mul_contains root130_contains root130_contains (c:=root260) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid261_contains : mid261.Contains (rootPhase 260) := root260_contains
lemma root261_contains : root261.Contains (rootPhase 261) := by
  have hh := CBox.mul_contains mid261_contains root1_contains (c:=root261) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root262_contains : root262.Contains (rootPhase 262) := by
  have hh := CBox.mul_contains root131_contains root131_contains (c:=root262) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid263_contains : mid263.Contains (rootPhase 262) := root262_contains
lemma root263_contains : root263.Contains (rootPhase 263) := by
  have hh := CBox.mul_contains mid263_contains root1_contains (c:=root263) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root264_contains : root264.Contains (rootPhase 264) := by
  have hh := CBox.mul_contains root132_contains root132_contains (c:=root264) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid265_contains : mid265.Contains (rootPhase 264) := root264_contains
lemma root265_contains : root265.Contains (rootPhase 265) := by
  have hh := CBox.mul_contains mid265_contains root1_contains (c:=root265) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root266_contains : root266.Contains (rootPhase 266) := by
  have hh := CBox.mul_contains root133_contains root133_contains (c:=root266) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid267_contains : mid267.Contains (rootPhase 266) := root266_contains
lemma root267_contains : root267.Contains (rootPhase 267) := by
  have hh := CBox.mul_contains mid267_contains root1_contains (c:=root267) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root268_contains : root268.Contains (rootPhase 268) := by
  have hh := CBox.mul_contains root134_contains root134_contains (c:=root268) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid269_contains : mid269.Contains (rootPhase 268) := root268_contains
lemma root269_contains : root269.Contains (rootPhase 269) := by
  have hh := CBox.mul_contains mid269_contains root1_contains (c:=root269) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root270_contains : root270.Contains (rootPhase 270) := by
  have hh := CBox.mul_contains root135_contains root135_contains (c:=root270) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid271_contains : mid271.Contains (rootPhase 270) := root270_contains
lemma root271_contains : root271.Contains (rootPhase 271) := by
  have hh := CBox.mul_contains mid271_contains root1_contains (c:=root271) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root320_contains : root320.Contains (rootPhase 320) := by
  have hh := CBox.mul_contains root160_contains root160_contains (c:=root320) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid321_contains : mid321.Contains (rootPhase 320) := root320_contains
lemma root321_contains : root321.Contains (rootPhase 321) := by
  have hh := CBox.mul_contains mid321_contains root1_contains (c:=root321) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root322_contains : root322.Contains (rootPhase 322) := by
  have hh := CBox.mul_contains root161_contains root161_contains (c:=root322) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root324_contains : root324.Contains (rootPhase 324) := by
  have hh := CBox.mul_contains root162_contains root162_contains (c:=root324) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root326_contains : root326.Contains (rootPhase 326) := by
  have hh := CBox.mul_contains root163_contains root163_contains (c:=root326) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root384_contains : root384.Contains (rootPhase 384) := by
  have hh := CBox.mul_contains root192_contains root192_contains (c:=root384) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root386_contains : root386.Contains (rootPhase 386) := by
  have hh := CBox.mul_contains root193_contains root193_contains (c:=root386) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root388_contains : root388.Contains (rootPhase 388) := by
  have hh := CBox.mul_contains root194_contains root194_contains (c:=root388) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root390_contains : root390.Contains (rootPhase 390) := by
  have hh := CBox.mul_contains root195_contains root195_contains (c:=root390) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid405 : CBox := root404
def mid407 : CBox := root406
def mid409 : CBox := root408
def mid411 : CBox := root410
def mid413 : CBox := root412
def mid497 : CBox := root496
lemma root512_contains : root512.Contains (rootPhase 512) := by
  have hh := CBox.mul_contains root256_contains root256_contains (c:=root512) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid513 : CBox := root512
lemma mid513_contains : mid513.Contains (rootPhase 512) := root512_contains
lemma root513_contains : root513.Contains (rootPhase 513) := by
  have hh := CBox.mul_contains mid513_contains root1_contains (c:=root513) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root514_contains : root514.Contains (rootPhase 514) := by
  have hh := CBox.mul_contains root257_contains root257_contains (c:=root514) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid515_contains : mid515.Contains (rootPhase 514) := root514_contains
lemma root515_contains : root515.Contains (rootPhase 515) := by
  have hh := CBox.mul_contains mid515_contains root1_contains (c:=root515) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root516_contains : root516.Contains (rootPhase 516) := by
  have hh := CBox.mul_contains root258_contains root258_contains (c:=root516) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid517_contains : mid517.Contains (rootPhase 516) := root516_contains
lemma root517_contains : root517.Contains (rootPhase 517) := by
  have hh := CBox.mul_contains mid517_contains root1_contains (c:=root517) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root518_contains : root518.Contains (rootPhase 518) := by
  have hh := CBox.mul_contains root259_contains root259_contains (c:=root518) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid519_contains : mid519.Contains (rootPhase 518) := root518_contains
lemma root519_contains : root519.Contains (rootPhase 519) := by
  have hh := CBox.mul_contains mid519_contains root1_contains (c:=root519) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root520_contains : root520.Contains (rootPhase 520) := by
  have hh := CBox.mul_contains root260_contains root260_contains (c:=root520) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid521_contains : mid521.Contains (rootPhase 520) := root520_contains
lemma root521_contains : root521.Contains (rootPhase 521) := by
  have hh := CBox.mul_contains mid521_contains root1_contains (c:=root521) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root522_contains : root522.Contains (rootPhase 522) := by
  have hh := CBox.mul_contains root261_contains root261_contains (c:=root522) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid523_contains : mid523.Contains (rootPhase 522) := root522_contains
lemma root523_contains : root523.Contains (rootPhase 523) := by
  have hh := CBox.mul_contains mid523_contains root1_contains (c:=root523) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root524_contains : root524.Contains (rootPhase 524) := by
  have hh := CBox.mul_contains root262_contains root262_contains (c:=root524) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid525_contains : mid525.Contains (rootPhase 524) := root524_contains
lemma root525_contains : root525.Contains (rootPhase 525) := by
  have hh := CBox.mul_contains mid525_contains root1_contains (c:=root525) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root526_contains : root526.Contains (rootPhase 526) := by
  have hh := CBox.mul_contains root263_contains root263_contains (c:=root526) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid527_contains : mid527.Contains (rootPhase 526) := root526_contains
lemma root527_contains : root527.Contains (rootPhase 527) := by
  have hh := CBox.mul_contains mid527_contains root1_contains (c:=root527) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root528_contains : root528.Contains (rootPhase 528) := by
  have hh := CBox.mul_contains root264_contains root264_contains (c:=root528) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid529_contains : mid529.Contains (rootPhase 528) := root528_contains
lemma root529_contains : root529.Contains (rootPhase 529) := by
  have hh := CBox.mul_contains mid529_contains root1_contains (c:=root529) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root530_contains : root530.Contains (rootPhase 530) := by
  have hh := CBox.mul_contains root265_contains root265_contains (c:=root530) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid531_contains : mid531.Contains (rootPhase 530) := root530_contains
lemma root531_contains : root531.Contains (rootPhase 531) := by
  have hh := CBox.mul_contains mid531_contains root1_contains (c:=root531) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root532_contains : root532.Contains (rootPhase 532) := by
  have hh := CBox.mul_contains root266_contains root266_contains (c:=root532) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid533_contains : mid533.Contains (rootPhase 532) := root532_contains
lemma root533_contains : root533.Contains (rootPhase 533) := by
  have hh := CBox.mul_contains mid533_contains root1_contains (c:=root533) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root534_contains : root534.Contains (rootPhase 534) := by
  have hh := CBox.mul_contains root267_contains root267_contains (c:=root534) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid535_contains : mid535.Contains (rootPhase 534) := root534_contains
lemma root535_contains : root535.Contains (rootPhase 535) := by
  have hh := CBox.mul_contains mid535_contains root1_contains (c:=root535) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root536_contains : root536.Contains (rootPhase 536) := by
  have hh := CBox.mul_contains root268_contains root268_contains (c:=root536) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid537_contains : mid537.Contains (rootPhase 536) := root536_contains
lemma root537_contains : root537.Contains (rootPhase 537) := by
  have hh := CBox.mul_contains mid537_contains root1_contains (c:=root537) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root538_contains : root538.Contains (rootPhase 538) := by
  have hh := CBox.mul_contains root269_contains root269_contains (c:=root538) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid539_contains : mid539.Contains (rootPhase 538) := root538_contains
lemma root539_contains : root539.Contains (rootPhase 539) := by
  have hh := CBox.mul_contains mid539_contains root1_contains (c:=root539) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root540_contains : root540.Contains (rootPhase 540) := by
  have hh := CBox.mul_contains root270_contains root270_contains (c:=root540) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid541_contains : mid541.Contains (rootPhase 540) := root540_contains
lemma root541_contains : root541.Contains (rootPhase 541) := by
  have hh := CBox.mul_contains mid541_contains root1_contains (c:=root541) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root542_contains : root542.Contains (rootPhase 542) := by
  have hh := CBox.mul_contains root271_contains root271_contains (c:=root542) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid543_contains : mid543.Contains (rootPhase 542) := root542_contains
lemma root543_contains : root543.Contains (rootPhase 543) := by
  have hh := CBox.mul_contains mid543_contains root1_contains (c:=root543) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root640_contains : root640.Contains (rootPhase 640) := by
  have hh := CBox.mul_contains root320_contains root320_contains (c:=root640) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid641_contains : mid641.Contains (rootPhase 640) := root640_contains
lemma root641_contains : root641.Contains (rootPhase 641) := by
  have hh := CBox.mul_contains mid641_contains root1_contains (c:=root641) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root642_contains : root642.Contains (rootPhase 642) := by
  have hh := CBox.mul_contains root321_contains root321_contains (c:=root642) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid643_contains : mid643.Contains (rootPhase 642) := root642_contains
lemma root643_contains : root643.Contains (rootPhase 643) := by
  have hh := CBox.mul_contains mid643_contains root1_contains (c:=root643) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root644_contains : root644.Contains (rootPhase 644) := by
  have hh := CBox.mul_contains root322_contains root322_contains (c:=root644) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid645_contains : mid645.Contains (rootPhase 644) := root644_contains
lemma root645_contains : root645.Contains (rootPhase 645) := by
  have hh := CBox.mul_contains mid645_contains root1_contains (c:=root645) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root648_contains : root648.Contains (rootPhase 648) := by
  have hh := CBox.mul_contains root324_contains root324_contains (c:=root648) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid649_contains : mid649.Contains (rootPhase 648) := root648_contains
lemma root649_contains : root649.Contains (rootPhase 649) := by
  have hh := CBox.mul_contains mid649_contains root1_contains (c:=root649) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root652_contains : root652.Contains (rootPhase 652) := by
  have hh := CBox.mul_contains root326_contains root326_contains (c:=root652) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid653_contains : mid653.Contains (rootPhase 652) := root652_contains
lemma root653_contains : root653.Contains (rootPhase 653) := by
  have hh := CBox.mul_contains mid653_contains root1_contains (c:=root653) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root768_contains : root768.Contains (rootPhase 768) := by
  have hh := CBox.mul_contains root384_contains root384_contains (c:=root768) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid769 : CBox := root768
lemma mid769_contains : mid769.Contains (rootPhase 768) := root768_contains
lemma root769_contains : root769.Contains (rootPhase 769) := by
  have hh := CBox.mul_contains mid769_contains root1_contains (c:=root769) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root772_contains : root772.Contains (rootPhase 772) := by
  have hh := CBox.mul_contains root386_contains root386_contains (c:=root772) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid773_contains : mid773.Contains (rootPhase 772) := root772_contains
lemma root773_contains : root773.Contains (rootPhase 773) := by
  have hh := CBox.mul_contains mid773_contains root1_contains (c:=root773) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root776_contains : root776.Contains (rootPhase 776) := by
  have hh := CBox.mul_contains root388_contains root388_contains (c:=root776) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid777_contains : mid777.Contains (rootPhase 776) := root776_contains
lemma root777_contains : root777.Contains (rootPhase 777) := by
  have hh := CBox.mul_contains mid777_contains root1_contains (c:=root777) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root780_contains : root780.Contains (rootPhase 780) := by
  have hh := CBox.mul_contains root390_contains root390_contains (c:=root780) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid781_contains : mid781.Contains (rootPhase 780) := root780_contains
lemma root781_contains : root781.Contains (rootPhase 781) := by
  have hh := CBox.mul_contains mid781_contains root1_contains (c:=root781) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
end IntegerRoots
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Fejer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar
open IntegerIntervals

lemma weight_root_contains (v a n : ℕ) (b : CBox)
    (hn : (2*a*(2*v+1))%1024 = n) (hb : b.Contains (rootPhase n)) :
    b.re.Contains (Real.cos (2*(a:ℝ)*fejerAngle v)) := by
  have hh := hb.1
  rw [← hn,rootPhase_mod,fejer_root_cos] at hh
  exact hh

lemma fejerPartial_checked_step (v N n : ℕ) (a : RBox) (r : CBox) (b : RBox)
    (ha : a.Contains (fejerPartial v N))
    (hr : r.Contains (rootPhase n))
    (hn : (2*(N+1)*(2*v+1))%1024 = n)
    (he : a.add (r.re.scale 1 (4*((N+1:ℕ):ℤ)^2-1)) = b) :
    b.Contains (fejerPartial v (N+1)) := by
  rw [← he,fejerPartial_succ]
  apply RBox.contains_add ha
  have hh := RBox.contains_scale (weight_root_contains v (N+1) n r hn hr)
    1 (4*((N+1:ℕ):ℤ)^2-1) (by
      have hN : (1:ℤ) ≤ (N+1:ℕ) := by omega
      nlinarith [sq_nonneg ((N+1:ℕ):ℤ)])
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

end SharpPlanar

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
def roots0 : Fin 32 → CBox := ![IntegerRoots.root0,IntegerRoots.root1,IntegerRoots.root2,IntegerRoots.root3,IntegerRoots.root4,IntegerRoots.root5,IntegerRoots.root6,IntegerRoots.root7,IntegerRoots.root8,IntegerRoots.root9,IntegerRoots.root10,IntegerRoots.root11,IntegerRoots.root12,IntegerRoots.root13,IntegerRoots.root14,IntegerRoots.root15,IntegerRoots.root16,IntegerRoots.root17,IntegerRoots.root18,IntegerRoots.root19,IntegerRoots.root20,IntegerRoots.root21,IntegerRoots.root22,IntegerRoots.root23,IntegerRoots.root24,IntegerRoots.root25,IntegerRoots.root26,IntegerRoots.root27,IntegerRoots.root28,IntegerRoots.root29,IntegerRoots.root30,IntegerRoots.root31]
def roots1 : Fin 32 → CBox := ![IntegerRoots.root32,IntegerRoots.root33,IntegerRoots.root34,IntegerRoots.root35,IntegerRoots.root36,IntegerRoots.root37,IntegerRoots.root38,IntegerRoots.root39,IntegerRoots.root40,IntegerRoots.root41,IntegerRoots.root42,IntegerRoots.root43,IntegerRoots.root44,IntegerRoots.root45,IntegerRoots.root46,IntegerRoots.root47,IntegerRoots.root48,IntegerRoots.root49,IntegerRoots.root50,IntegerRoots.root51,IntegerRoots.root52,IntegerRoots.root53,IntegerRoots.root54,IntegerRoots.root55,IntegerRoots.root56,IntegerRoots.root57,IntegerRoots.root58,IntegerRoots.root59,IntegerRoots.root60,IntegerRoots.root61,IntegerRoots.root62,IntegerRoots.root63]
def roots8 : Fin 32 → CBox := ![IntegerRoots.root256,IntegerRoots.root257,IntegerRoots.root258,IntegerRoots.root259,IntegerRoots.root260,IntegerRoots.root261,IntegerRoots.root262,IntegerRoots.root263,IntegerRoots.root264,IntegerRoots.root265,IntegerRoots.root266,IntegerRoots.root267,IntegerRoots.root268,IntegerRoots.root269,IntegerRoots.root270,IntegerRoots.root271,IntegerRoots.root272,IntegerRoots.root273,IntegerRoots.root274,IntegerRoots.root275,IntegerRoots.root276,IntegerRoots.root277,IntegerRoots.root278,IntegerRoots.root279,IntegerRoots.root280,IntegerRoots.root281,IntegerRoots.root282,IntegerRoots.root283,IntegerRoots.root284,IntegerRoots.root285,IntegerRoots.root286,IntegerRoots.root287]
def roots10 : Fin 32 → CBox := ![IntegerRoots.root320,IntegerRoots.root321,IntegerRoots.root322,IntegerRoots.root323,IntegerRoots.root324,IntegerRoots.root325,IntegerRoots.root326,IntegerRoots.root327,IntegerRoots.root328,IntegerRoots.root329,IntegerRoots.root330,IntegerRoots.root331,IntegerRoots.root332,IntegerRoots.root333,IntegerRoots.root334,IntegerRoots.root335,IntegerRoots.root336,IntegerRoots.root337,IntegerRoots.root338,IntegerRoots.root339,IntegerRoots.root340,IntegerRoots.root341,IntegerRoots.root342,IntegerRoots.root343,IntegerRoots.root344,IntegerRoots.root345,IntegerRoots.root346,IntegerRoots.root347,IntegerRoots.root348,IntegerRoots.root349,IntegerRoots.root350,IntegerRoots.root351]
def roots11 : Fin 32 → CBox := ![IntegerRoots.root352,IntegerRoots.root353,IntegerRoots.root354,IntegerRoots.root355,IntegerRoots.root356,IntegerRoots.root357,IntegerRoots.root358,IntegerRoots.root359,IntegerRoots.root360,IntegerRoots.root361,IntegerRoots.root362,IntegerRoots.root363,IntegerRoots.root364,IntegerRoots.root365,IntegerRoots.root366,IntegerRoots.root367,IntegerRoots.root368,IntegerRoots.root369,IntegerRoots.root370,IntegerRoots.root371,IntegerRoots.root372,IntegerRoots.root373,IntegerRoots.root374,IntegerRoots.root375,IntegerRoots.root376,IntegerRoots.root377,IntegerRoots.root378,IntegerRoots.root379,IntegerRoots.root380,IntegerRoots.root381,IntegerRoots.root382,IntegerRoots.root383]
def roots12 : Fin 32 → CBox := ![IntegerRoots.root384,IntegerRoots.root385,IntegerRoots.root386,IntegerRoots.root387,IntegerRoots.root388,IntegerRoots.root389,IntegerRoots.root390,IntegerRoots.root391,IntegerRoots.root392,IntegerRoots.root393,IntegerRoots.root394,IntegerRoots.root395,IntegerRoots.root396,IntegerRoots.root397,IntegerRoots.root398,IntegerRoots.root399,IntegerRoots.root400,IntegerRoots.root401,IntegerRoots.root402,IntegerRoots.root403,IntegerRoots.root404,IntegerRoots.root405,IntegerRoots.root406,IntegerRoots.root407,IntegerRoots.root408,IntegerRoots.root409,IntegerRoots.root410,IntegerRoots.root411,IntegerRoots.root412,IntegerRoots.root413,IntegerRoots.root414,IntegerRoots.root415]
def roots15 : Fin 32 → CBox := ![IntegerRoots.root480,IntegerRoots.root481,IntegerRoots.root482,IntegerRoots.root483,IntegerRoots.root484,IntegerRoots.root485,IntegerRoots.root486,IntegerRoots.root487,IntegerRoots.root488,IntegerRoots.root489,IntegerRoots.root490,IntegerRoots.root491,IntegerRoots.root492,IntegerRoots.root493,IntegerRoots.root494,IntegerRoots.root495,IntegerRoots.root496,IntegerRoots.root497,IntegerRoots.root498,IntegerRoots.root499,IntegerRoots.root500,IntegerRoots.root501,IntegerRoots.root502,IntegerRoots.root503,IntegerRoots.root504,IntegerRoots.root505,IntegerRoots.root506,IntegerRoots.root507,IntegerRoots.root508,IntegerRoots.root509,IntegerRoots.root510,IntegerRoots.root511]
def roots16 : Fin 32 → CBox := ![IntegerRoots.root512,IntegerRoots.root513,IntegerRoots.root514,IntegerRoots.root515,IntegerRoots.root516,IntegerRoots.root517,IntegerRoots.root518,IntegerRoots.root519,IntegerRoots.root520,IntegerRoots.root521,IntegerRoots.root522,IntegerRoots.root523,IntegerRoots.root524,IntegerRoots.root525,IntegerRoots.root526,IntegerRoots.root527,IntegerRoots.root528,IntegerRoots.root529,IntegerRoots.root530,IntegerRoots.root531,IntegerRoots.root532,IntegerRoots.root533,IntegerRoots.root534,IntegerRoots.root535,IntegerRoots.root536,IntegerRoots.root537,IntegerRoots.root538,IntegerRoots.root539,IntegerRoots.root540,IntegerRoots.root541,IntegerRoots.root542,IntegerRoots.root543]
lemma roots16_contains (j : Fin 32) : (roots16 j).Contains (rootPhase (512+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root512_contains
  · exact IntegerRoots.root513_contains
  · exact IntegerRoots.root514_contains
  · exact IntegerRoots.root515_contains
  · exact IntegerRoots.root516_contains
  · exact IntegerRoots.root517_contains
  · exact IntegerRoots.root518_contains
  · exact IntegerRoots.root519_contains
  · exact IntegerRoots.root520_contains
  · exact IntegerRoots.root521_contains
  · exact IntegerRoots.root522_contains
  · exact IntegerRoots.root523_contains
  · exact IntegerRoots.root524_contains
  · exact IntegerRoots.root525_contains
  · exact IntegerRoots.root526_contains
  · exact IntegerRoots.root527_contains
  · exact IntegerRoots.root528_contains
  · exact IntegerRoots.root529_contains
  · exact IntegerRoots.root530_contains
  · exact IntegerRoots.root531_contains
  · exact IntegerRoots.root532_contains
  · exact IntegerRoots.root533_contains
  · exact IntegerRoots.root534_contains
  · exact IntegerRoots.root535_contains
  · exact IntegerRoots.root536_contains
  · exact IntegerRoots.root537_contains
  · exact IntegerRoots.root538_contains
  · exact IntegerRoots.root539_contains
  · exact IntegerRoots.root540_contains
  · exact IntegerRoots.root541_contains
  · exact IntegerRoots.root542_contains
  · exact IntegerRoots.root543_contains
def roots24 : Fin 32 → CBox := ![IntegerRoots.root768,IntegerRoots.root769,IntegerRoots.root770,IntegerRoots.root771,IntegerRoots.root772,IntegerRoots.root773,IntegerRoots.root774,IntegerRoots.root775,IntegerRoots.root776,IntegerRoots.root777,IntegerRoots.root778,IntegerRoots.root779,IntegerRoots.root780,IntegerRoots.root781,IntegerRoots.root782,IntegerRoots.root783,IntegerRoots.root784,IntegerRoots.root785,IntegerRoots.root786,IntegerRoots.root787,IntegerRoots.root788,IntegerRoots.root789,IntegerRoots.root790,IntegerRoots.root791,IntegerRoots.root792,IntegerRoots.root793,IntegerRoots.root794,IntegerRoots.root795,IntegerRoots.root796,IntegerRoots.root797,IntegerRoots.root798,IntegerRoots.root799]
def rootRows : Fin 32 → Fin 32 → CBox := ![roots0,roots1,roots2,roots3,roots4,roots5,roots6,roots7,roots8,roots9,roots10,roots11,roots12,roots13,roots14,roots15,roots16,roots17,roots18,roots19,roots20,roots21,roots22,roots23,roots24,roots25,roots26,roots27,roots28,roots29,roots30,roots31]
def rootLookup (n : ℕ) : CBox :=
  rootRows ⟨(n%1024)/32,by omega⟩ ⟨n%32,by omega⟩

def partialBox (v : ℕ) : ℕ → RBox
  | 0 => ⟨0,0⟩
  | N+1 => (partialBox v N).add ((rootLookup (2*(N+1)*(2*v+1))).re.scale 1
      (4*((N+1:ℕ):ℤ)^2-1))

def weightBoxCalc (v : ℕ) : RBox :=
  ((RBox.rat 1 1).add ((partialBox v 127).scale (-2) 1)).scale 1 256

def nodeLookup (n : Fin 256) : RBox := (rootLookup (2*n.val+1)).re
end SharpPlanar.IntegerCompact


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

def phaseBase : CBox := (piI.scale 1 6).exp 1
lemma phaseBase_contains : phaseBase.Contains (phase12 1) := by
  have hi := CBox.contains_scale piI_contains 1 6 (by norm_num)
  have he := CBox.contains_exp hi 1 (by decide +kernel)
  unfold phaseBase
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  unfold phase12
  congr 1
  norm_num
  ring

def phaseBox (n : ℕ) : CBox := phaseBase.powBin 4 (n%12)
lemma phaseBox_contains (n : ℕ) : (phaseBox n).Contains (phase12 n) := by
  have hh := CBox.contains_powBin phaseBase_contains 4 (n%12) (by omega)
  rw [← phase12_eq_pow,phase12_mod] at hh
  exact hh

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerIntervals

def CBox.powFast (a : CBox) : ℕ → ℕ → CBox
  | 0, _ => CBox.rat 1 1 0 1
  | k+1,n => if n=0 then CBox.rat 1 1 0 1 else if n=1 then a else
      let b := a.powFast k (n/2)
      let b2 := b.mul b
      if n%2=0 then b2 else b2.mul a

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

def kernel0Box (p : PointBox) (m : ℕ) : CBox := p.lam.mul (p.quarter.powFast 9 (4*m))

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerIntervals

def finSum : {N : ℕ} → (Fin N → CBox) → CBox
  | 0, _ => zeroBox
  | N+1, f => (f 0).add (finSum (fun i : Fin N => f i.succ))

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

def cachedMomentRuleBox (c k : Fin 6 → Fin 16 → Fin 16 → CBox) : CBox :=
  finSum fun j => (finSum (fun i => finSum (fun v => (c j i v).mul (k j i v)))).scale 1 6

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma waveAmplitudeBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t)
    {a b : CBox} {n j : ℕ} (ha : a.Contains (basisAlpha n j))
    (hb : b.Contains (basisBeta n j)) (d : Bool) :
    (waveAmplitudeBox p a b d).Contains (waveAmplitude d n j t) := by
  cases d
  · have hh := CBox.contains_mul
      (CBox.contains_scale (CBox.contains_mul (rcast_contains piBounds_contains)
        (rcast_contains piBounds_contains)) (-2) 1 (by norm_num))
      (CBox.contains_add hb (CBox.neg_contains (CBox.contains_mul (rcast_contains hp.1) ha)))
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [waveAmplitudeBox,waveAmplitude,Bool.false_eq_true,ite_false, if_false,Int.cast_neg,Int.cast_ofNat,Int.cast_one] <;> ring)
  · have hh := CBox.contains_mul (CBox.contains_scale piI_contains 2 1 (by norm_num)) ha
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [waveAmplitudeBox,waveAmplitude,ite_true, if_true,Int.cast_ofNat,Int.cast_one] <;> ring)

end SharpPlanar.IntegerBasis

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourier quadrature grid

Certified rational enclosures for the quadrature points and their Fourier
kernels on each of the six subintervals.
-/

namespace SharpPlanar.IntegerGrid
open IntegerIntervals IntegerCompact

def p4_136 : PointBox := ⟨⟨741323197177328785072848080857,741323197177328785073453055739⟩,⟨⟨650938837499990198461294320426,650938837499990198484666363189⟩,⟨1206390150455966036506491327121,1206390150455966036550791424901⟩⟩,⟨⟨(-1393019356226930236845891689190),(-1393019356226930236842993948457)⟩,⟨351639426113202806591374697725,351639426113202806592324854584⟩⟩,⟨⟨(-687571466260280555399908182723),(-687571466260280555385799179553)⟩,⟨(-726116711544836900578951438041),(-726116711544836900565517142201)⟩⟩,⟨⟨348133869985757097052537605228,348133869985757097058572356547⟩,⟨(-674089106169342623180512102903),(-674089106169342623173921493931)⟩⟩⟩

def p4_137 : PointBox := ⟨⟨740306780757341269395210434541,740306780757341269395822722030⟩,⟨⟨652323312611147580150549125804,652323312611147580173981474106⟩,⟨1207298428930308556987650325729,1207298428930308557032016665079⟩⟩,⟨⟨(-1394068145870251830441990681084),(-1394068145870251830439052782314)⟩,⟨353238080269428909333452831284,353238080269428909334417243976⟩⟩,⟨⟨(-685249353401782965636896452722),(-685249353401782965622768798708)⟩,⟨(-728308536035682034322995932052),(-728308536035682034309544648814)⟩⟩,⟨⟨347142354219569525616322997916,347142354219569525622395121232⟩,⟨(-673529440149953537944036504662),(-673529440149953537937407872693)⟩⟩⟩

def p4_138 : PointBox := ⟨⟨739291824100517235614217254763,739291824100517235614836152658⟩,⟨⟨653709780872728698450046091814,653709780872728698473537916013⟩,⟨1208205740834372528503957376984,1208205740834372528548387109913⟩⟩,⟨⟨(-1395115819414352402165256472050),(-1395115819414352402162281665161)⟩,⟨354839035917522371572693692868,354839035917522371573671323679⟩⟩,⟨⟨(-682923603553140187192486154386),(-682923603553140187178343234824)⟩,⟨(-730489802605069505915051265491),(-730489802605069505901586199027)⟩⟩,⟨⟨346152507575305757080666286732,346152507575305757086772961532⟩,⟨(-672968140999446914780978150144),(-672968140999446914774314561100)⟩⟩⟩

def p4_139 : PointBox := ⟨⟨738278480055595897440015240971,738278480055595897440641455939⟩,⟨⟨655098028659278569622502594207,655098028659278569646054981628⟩,⟨1209111942214973457729932013595,1209111942214973457774428146041⟩⟩,⟨⟨(-1396162210636412316165040793427),(-1396162210636412316162025563032)⟩,⟨356442046384055312075095341150,356442046384055312076087374436⟩⟩,⟨⟨(-680594622185110176534724221135),(-680594622185110176520562714581)⟩,⟨(-732660194259731251800327840559),(-732660194259731251786845809370)⟩⟩,⟨⟨345164486542658498769819854745,345164486542658498775964049266⟩,⟨(-672405301113602584818782555712),(-672405301113602584812080808987)⟩⟩⟩

def p4_140 : PointBox := ⟨⟨737266901228463047689549183767,737266901228463047690181755011⟩,⟨⟨656487840223481132600728956837,656487840223481132624340701210⟩,⟨1210016889139330737032739558070,1210016889139330737077298140411⟩⟩,⟨⟨(-1397207153337172314385007386388),(-1397207153337172314381956242941)⟩,⟨358046862545485721247833500502,358046862545485721248838480831⟩⟩,⟨⟨(-678262818179299751494077877938),(-678262818179299751479902394623)⟩,⟨(-734819399223696438849184747269),(-734819399223696438835690120902)⟩⟩,⟨⟨344178447180604485386269586078,344178447180604485392447401838⟩,⟨(-671841014261926772469782867588),(-671841014261926772463047192602)⟩⟩⟩

def p4_141 : PointBox := ⟨⟨736257239959169173214723937451,736257239959169173215363825250⟩,⟨⟨657878997722609763396759318112,657878997722609763420431844727⟩,⟨1210920437725883016484670340043,1210920437725883016529295434674⟩⟩,⟨⟨(-1398250481376516043216330748068),(-1398250481376516043213238944792)⟩,⟨359653232858699884367893122630,359653232858699884368912641944⟩⟩,⟨⟨(-675928603713374076962226345290),(-675928603713374076948032352321)⟩,⟨(-736967110990774475006103589770),(-736967110990774474992592033395)⟩⟩,⟨⟨343194545082793260303753054203,343194545082793260309968509488⟩,⟨(-671275375570173896865177975326),(-671275375570173896858404036221)⟩⟩⟩

def p4_142 : PointBox := ⟨⟨735249648298987603649832569032,735249648298987603650479017719⟩,⟨⟨659271281246475590550384123941,659271281246475590574116487072⟩,⟨1211822444175235299319501481975,1211822444175235299364189973725⟩⟩,⟨⟨(-1399292028709204681282396351808),(-1399292028709204681279267424100)⟩,⟨361260903393284316477282008849,361260903393284316478314930080⟩⟩,⟨⟨(-673592394144174780538993981219),(-673592394144174780524785107173)⟩,⟨(-739103028373662322963576307475),(-739103028373662322950051255453)⟩⟩,⟨⟨342212935343124579513072405826,342212935343124579519322436268⟩,⟨(-670708481501870654739448247579),(-670708481501870654732639368789)⟩⟩⟩

def p4_143 : PointBox := ⟨⟨734244277987516148936648572286,734244277987516148937302333820⟩,⟨⟨660664468846886914644391764483,660664468846886914668185093616⟩,⟨1212722764801220845896965856160,1212722764801220845941720938129⟩⟩,⟨⟨(-1400331629420744136669690670786),(-1400331629420744136666520864146)⟩,⟨362869617865542569957620557157,362869617865542569958668148358⟩⟩,⟨⟨(-671254607888824431446667896197),(-671254607888824431432440594701)⟩,⟨(-741226855549649227213982722303),(-741226855549649227200440779035)⟩⟩,⟨⟨341233772521536513851119688183,341233772521536513857407459896⟩,⟨(-670140429838844872800578382864),(-670140429838844872793731151600)⟩⟩⟩

def p4_144 : PointBox := ⟨⟨733241280429825674036357844907,733241280429825674037017800943⟩,⟨⟨662058336568632081752256942003,662058336568632081776109764580⟩,⟨1213621256062060665600229172902,1213621256062060665645046181812⟩⟩,⟨⟨(-1401369117763364928997409969506),(-1401369117763364928994204595438)⟩,⟨364479117674271175180723737552,364479117674271175181784271158⟩⟩,⟨⟨(-668915666303896241531146448671),(-668915666303896241516906067451)⟩,⟨(-743338302102894823196701764482),(-743338302102894823183147999976)⟩⟩,⟨⟨340257210610026261461948660178,340257210610026261468269592107⟩,⟨(-669571319660762487111939357645),(-669571319660762487105058734435)⟩⟩⟩

def p4_145 : PointBox := ⟨⟨732240806673659052168910894493,732240806673659052169578154171⟩,⟨⟨663452658481997173199846924721,663452658481997173223760855497⟩,⟨1214517774591603089163759669991,1214517774591603089208643297916⟩⟩,⟨⟨(-1402404328192094540403225232494),(-1402404328192094540399978794156)⟩,⟨366089141938307834383292778744,366089141938307834384368101143⟩⟩,⟨⟨(-666575993562728879893099642414),(-666575993562728879878840931219)⟩,⟨(-745437083063259488990242342258),(-745437083063259488976671739190)⟩⟩,⟨⟨339283402998925587904849024110,339283402998925587911207767754⟩,⟨(-669001251323676880730717429214),(-669001251323676880723798396800)⟩⟩⟩

def p4_146 : PointBox := ⟨⟨731243007386683930333583483526,731243007386683930334257237137⟩,⟨⟨664847206716828852582397529697,664847206716828852606371502697⟩,⟨1215412177230625646578199774921,1215412177230625646623146633225⟩⟩,⟨⟨(-1403437095400901710812279062743),(-1403437095400901710808995388357)⟩,⟨367699427535863809456147417514,367699427535863809457236288774⟩⟩,⟨⟨(-664236016530967232012339403319),(-664236016530967231998066235769)⟩,⟨(-747522918941668721663273992232),(-747522918941668721649690217029)⟩⟩,⟨⟨338312502443452685699634488403,338312502443452685706027730279⟩,⟨(-668430326437595687623736588643),(-668430326437595687616782735038)⟩⟩⟩

def p4_147 : PointBox := ⟨⟨730248032833802732760571595039,730248032833802732761252640290⟩,⟨⟨666241751498151656009261420564,666241751498151656033296607948⟩,⟨1216304321058181228791631553724,1216304321058181228836645026442⟩⟩,⟨⟨(-1404467254358891867729797255138),(-1404467254358891867726472346808)⟩,⟨369309709145651226165446821585,369309709145651226166550595334⟩⟩,⟨⟨(-661896164640410779664171263225),(-661896164640410779649879865638)⟩,⟨(-749595535761996268521637955695),(-749595535761996268508037396589)⟩⟩,⟨⟨337344661030562088200261083488,337344661030562088206692191030⟩,⟨(-667858647843071049525952394872),(-667858647843071049518960091715)⟩⟩⟩

def p4_148 : PointBox := ⟨⟨729256032854523319323655857370,729256032854523319324343083465⟩,⟨⟨667636061183347923542277995553,667636061183347923566372884228⟩,⟨1217194063422970285751117230570,1217194063422970285796192630197⟩⟩,⟨⟨(-1405494640346532620209761843046),(-1405494640346532620206401017376)⟩,⟨370919719289814761001478959002,370919719289814761002595897476⟩⟩,⟨⟨(-659556869761252029141746179488),(-659556869761252029127441850717)⟩,⟨(-751654665089453714566453152487),(-751654665089453714552840831703)⟩⟩,⟨⟨336380030146114084389281502858,336380030146114084395745893577⟩,⟨(-667286319586820191714945072556),(-667286319586820191707919274689)⟩⟩⟩

def p4_149 : PointBox := ⟨⟨728267156840393706809526528306,728267156840393706810221028780⟩,⟨⟨669029902300907449302488565467,669029902300907449326644732010⟩,⟨1218081261974720609709531309799,1218081261974720609754673270582⟩⟩,⟨⟨(-1406519088991888011533571624150),(-1406519088991888011530169428213)⟩,⟨372529188378675883018892235610,372529188378675883020024178030⟩⟩,⟨⟨(-657218566072788072104843467010),(-657218566072788072090521021741)⟩,⟨(-753700044055477217983292109134),(-753700044055477217969663071663)⟩⟩,⟨⟨335418760442384861419860871339,335418760442384861426363151046⟩,⟨(-666713446896384062429869398534),(-666713446896384062422805141592)⟩⟩⟩

def p4_150 : PointBox := ⟨⟨727281553712504251291759546913,727281553712504251292460457012⟩,⟨⟨670423039590752775361994876130,670423039590752775386211129613⟩,⟨1218965774695556071941716864240,1218965774695556071986921716085⟩⟩,⟨⟨(-1407540436306840016384424384328),(-1407540436306840016380984948564)⟩,⟨374137844757296492403926074124,374137844757296492405071673470⟩⟩,⟨⟨(-654881689932688925729595580457),(-654881689932688925715259141125)⟩,⟨(-755731415379105091866058474454),(-755731415379105091852416622595)⟩⟩,⟨⟨334461001805938350492065971118,334461001805938350498602570310⟩,⟨(-666140136153832657637755629892),(-666140136153832657630656772343)⟩⟩⟩

def p4_151 : PointBox := ⟨⟨726299371899060679698008651078,726299371899060679698716815154⟩,⟨⟨671815236046144870994801092127,671815236046144871019078648591⟩,⟨1219847459931335523823813268041,1219847459931335523869084591611⟩⟩,⟨⟨(-1408558518723275586795869051934),(-1408558518723275586792388128642)⟩,⟨375745414753867430866506382605,375745414753867430867667080679⟩⟩,⟨⟨(-652546679744906766838916451908),(-652546679744906766824562013191)⟩,⟨(-757748527384842949081708966562),(-757748527384842949068050468454)⟩⟩,⟨⟨333506903325880468988316435521,333506903325880468994890928146⟩,⟨(-665566494868526526809680376152),(-665566494868526526802543068758)⟩⟩⟩

def p4_152 : PointBox := ⟨⟨725320759313031347989382380835,725320759313031347990096529423⟩,⟨⟨673206252957172724879444196578,673206252957172724903781264517⟩,⟨1220726176422942940354303912210,1220726176422942940399636286942⟩⟩,⟨⟨(-1409573173129217397721486816358),(-1409573173129217397717970545914)⟩,⟨377351622729925937170516976477,377351622729925937171690751807⟩⟩,⟨⟨(-650213975826310548597395948552),(-650213975826310548583029549496)⟩,⟨(-759751134017016154635157760033),(-759751134017016154621488341260)⟩⟩,⟨⟨332556613262516137823966050489,332556613262516137830573155677⟩,⟨(-664992631648944825074241994591),(-664992631648944825067071938017)⟩⟩⟩

def p4_153 : PointBox := ⟨⟨724345863329872092192688677585,724345863329872092193410054003⟩,⟨⟨674595849955829134238830428933,674595849955829134263228779533⟩,⟨1221601783337509776325507303736,1221601783337509776370906008404⟩⟩,⟨⟨(-1410584236904876318515622161190),(-1410584236904876318512064323809)⟩,⟨378956191132404685121438332402,378956191132404685122627286975⟩⟩,⟨⟨(-647884020272130768550299308559),(-647884020272130768535915042500)⟩,⟨(-761738994850612362529279259927),(-761738994850612362515593279695)⟩⟩,⟨⟨331610279016429107868529960805,331610279016429107875174930030⟩,⟨(-664418656173591141325348088447),(-664418656173591141318139625310)⟩⟩⟩

def p4_154 : PointBox := ⟨⟨723374830765332026841064031300,723374830765332026841791715572⟩,⟨⟨675983785062673702546304178247,675983785062673702570762492154⟩,⟨1222474140299550423146534002931,1222474140299550423191995081562⟩⟩,⟨⟨(-1411591547958603541689489413975),(-1411591547958603541685894447625)⟩,⟨380558840547513572139935118456,380558840547513572141137795286⟩⟩,⟨⟨(-645557256820299343809177532436),(-645557256820299343794779770454)⟩,⟨(-763711875098619948367984218212),(-763711875098619948354285814776)⟩⟩,⟨⟨330668047098004253300081717658,330668047098004253306760722012⟩,⟨(-663844679160989189334767000251),(-663844679160989189327524262546)⟩⟩⟩

def p4_155 : PointBox := ⟨⟨722407807853343633188087475755,722407807853343633188822358952⟩,⟨⟨677369814735082757263837902157,677369814735082757288357439428⟩,⟨1223343107421991598391149226365,1223343107421991598436676458527⟩⟩,⟨⟨(-1412594944762720235727711827520),(-1412594944762720235724075232337)⟩,⟨382159289756453925250898691790,382159289756453925252116622086⟩⟩,⟨⟨(-643234130714769643714547642028),(-643234130714769643700132146729)⟩,⟨(-765669545615871181267439993583),(-765669545615871181253725114764)⟩⟩,⟨⟨329730063097411583170419678328,329730063097411583177136500066⟩,⟨(-663270812338781298421458542150),(-663270812338781298414177458159)⟩⟩⟩

def p4_156 : PointBox := ⟨⟨721444940224000466866785012107,721444940224000466867525826861⟩,⟨⟨678753693917084572116123199603,678753693917084572140702115282⟩,⟨1224208545337076471075560032711,1224208545337076471121147945472⟩⟩,⟨⟨(-1413594266389202555184683067872),(-1413594266389202555181011022288)⟩,⟨383757255792963259073589728012,383757255792963259074820867419⟩⟩,⟨⟨(-640915088567901733156005637707),(-640915088567901733141578423128)⟩,⟨(-767611782899402005482947696938),(-767611782899402005469222043855)⟩⟩,⟨⟨328796471655070785646330096680,328796471655070785653079427473⟩,⟨(-662697168411943480529195582023),(-662697168411943480521881874082)⟩⟩⟩

def p4_157 : PointBox := ⟨⟨720486372881625801469730074726,720486372881625801470478053982⟩,⟨⟨680135176090776925715507439631,680135176090776925740147472960⟩,⟨1225070315227124323997166655634,1225070315227124324042820493745⟩⟩,⟨⟨(-1414589352545199839347530041327),(-1414589352545199839343816342500)⟩,⟨385352454002687158447999274406,385352454002687158449245727110⟩⟩,⟨⟨(-638600578221997791858233633624),(-638600578221997791843788833153)⟩,⟨(-769538369085343320010889275020),(-769538369085343319997147245759)⟩⟩,⟨⟨327867416432614652778940624918,327867416432614652785727693366⟩,⟨(-662123861030131680442175093169),(-662123861030131680434823132401)⟩⟩⟩

def p4_158 : PointBox := ⟨⟨719532250182935510831864290663,719532250182935510832618458655⟩,⟨⟨681514013329322651074225506891,681514013329322651098925206210⟩,⟨1225928278855126580677190010962,1225928278855126580722905526673⟩⟩,⟨⟨(-1415580043608363861018984565796),(-1415580043608363861015233966354)⟩,⟨386944598104373267988327027230,386944598104373267989587222794⟩⟩,⟨⟨(-636291048610072497438420347937),(-636291048610072497423962583039)⟩,⟨(-771449091942361649796432485107),(-771449091942361649782678455804)⟩⟩,⟨⟨326943040084369237728902387088,326943040084369237735723100019⟩,⟨(-661551004754174634117326933146),(-661551004754174634109941129780)⟩⟩⟩

def p4_159 : PointBox := ⟨⟨718582715815298478605625411207,718582715815298478606386706205⟩,⟨⟨682889956351517429872754084097,682889956351517429897514754253⟩,⟨1226782298595160078990599596170,1226782298595160079036380771955⟩⟩,⟨⟨(-1416566180661967049951780410922),(-1416566180661967049947988154544)⟩,⟨388533400252880753502818257453,388533400252880753504093818358⟩⟩,⟨⟨(-633986949615942894132031667177),(-633986949615942894117556466109)⟩,⟨(-773343744861670091611920863749),(-773343744861670091598150559908)⟩⟩,⟨⟨326023484229368071691320998295,326023484229368071698179349713⟩,⟨(-660978715021729565540773850993),(-660978715021729565533349907434)⟩⟩⟩
def row4_9 : Fin 16 → PointBox := ![p4_144,p4_145,p4_146,p4_147,p4_148,p4_149,p4_150,p4_151,p4_152,p4_153,p4_154,p4_155,p4_156,p4_157,p4_158,p4_159]
def p5_0 : PointBox := ⟨⟨999998431273550095221415862037,999998431273550095221415872872⟩,⟨⟨398173676380927874230867124866,398173676380927874244660273062⟩,⟨995432629388375199109241251539,995432629388375199143724078719⟩⟩,⟨⟨(-1149426593075030800109146962119),(-1149426593075030800109146928188)⟩,⟨59771358485503284904523635085,59771358485503284904523643676⟩⟩,⟨⟨(-999999999987855932072483209387),(-999999999987855932059376764278)⟩,⟨(-4928299490492903531323011),(-4928299490492890424883872)⟩⟩,⟨⟨591040017834859568704352083844,591040017834859568706860529139⟩,⟨(-749036609966832983175239339958),(-749036609966832983172017757497)⟩⟩⟩

def p5_1 : PointBox := ⟨⟨999985881816318618501310122165,999985881816318618501310214622⟩,⟨⟨398182291805002096205851760064,398182291805002096219645262743⟩,⟨995441675485669299348000699134,995441675485669299382484061019⟩⟩,⟨⟨(-1149437038608446528745299312414),(-1149437038608446528745299022901)⟩,⟨59781306720320154583723292601,59781306720320154583723365898⟩⟩,⟨⟨(-999999999016379876044332506565),(-999999999016379876031225685958)⟩,⟨(-44353582120917063991853206),(-44353582120917050885086333)⟩⟩,⟨⟨591029254869554995064037110683,591029254869554995066545824849⟩,⟨(-749035606294702659937211424388),(-749035606294702659933989550835)⟩⟩⟩

def p5_2 : PointBox := ⟨⟨999960784791757763589975091018,999960784791757763589975345024⟩,⟨⟨398199522149743572854440870987,398199522149743572868235081461⟩,⟨995459766681401279075913832062,995459766681401279110398258751⟩⟩,⟨⟨(-1149457928521898170154569721739),(-1149457928521898170154568926344)⟩,⟨59801202608669597775352667268,59801202608669597775352868642⟩⟩,⟨⟨(-999999992411100520873859817692),(-999999992411100520860752253097)⟩,⟨(-123198209811157541184964030),(-123198209811157528077548697)⟩⟩,⟨⟨591007730164271237861069023762,591007730164271237863578271137⟩,⟨(-749033598515668406515067852571),(-749033598515668406511845402176)⟩⟩⟩

def p5_3 : PointBox := ⟨⟨999923143979387115240731470065,999923143979387115240731965537⟩,⟨⟨398225366408088282561191178116,398225366408088282574986449676⟩,⟨995486900977797622355398115604,995486900977797622389884137152⟩⟩,⟨⟨(-1149489260508555569924021402270),(-1149489260508555569924019850662)⟩,⟨59831044987694246537685205077,59831044987694246537685597918⟩⟩,⟨⟨(-999999970850874104464937247758),(-999999970850874104451828570768)⟩,⟨(-241450307395562652392670070),(-241450307395562639284285627)⟩⟩,⟨⟨590975446169746337054774946458,590975446169746337057284991429⟩,⟨(-749030585760480306340893450509),(-749030585760480306337670137486)⟩⟩⟩

def p5_4 : PointBox := ⟨⟨999872965047774562684045987619,999872965047774562684046804446⟩,⟨⟨398259823068815049838384246863,398259823068815049852180932760⟩,⟨995523075378045479500665491464,995523075378045479535153637826⟩⟩,⟨⟨(-1149531031107997317099615896652),(-1149531031107997317099613338502)⟩,⟨59870832112386195924927075697,59870832112386195924927723406⟩⟩,⟨⟨(-999999920362759826769043788109),(-999999920362759826755933630485)⟩,⟨(-399092062066367094767044178),(-399092062066367081657370124)⟩⟩,⟨⟨590932406562305318788626893546,590932406562305318791138000443⟩,⟨(-749026566726006687096235156394),(-749026566726006687093010695017)⟩⟩⟩

def p5_5 : PointBox := ⟨⟨999810255553682634154044667181,999810255553682634154045885225⟩,⟨⟨398302890115795582245776437479,398302890115795582259574890913⟩,⟨995568285886109885008764779392,995568285886109885043255580405⟩⟩,⟨⟨(-1149583235705999685632781665726),(-1149583235705999685632777850670)⟩,⟨59920561654721021214687877808,59920561654721021214688843811⟩⟩,⟨⟨(-999999822332544153451540767809),(-999999822332544153438428761504)⟩,⟨(-596099723307589844496650933),(-596099723307589831385366948)⟩⟩,⟨⟨590878616244121241649497294342,590878616244121241652009727556⟩,⟨(-749021539676125849441550465365),(-749021539676125849438324569867)⟩⟩⟩

def p5_6 : PointBox := ⟨⟨999735024940930476247717869771,999735024940930476247719568824⟩,⟨⟨398354565026994867546426106178,398354565026994867560226680267⟩,⟨995622527506490562851764755515,995622527506490562886258740782⟩⟩,⟨⟨(-1149645868534255817320366904183),(-1149645868534255817320361581932)⟩,⟨59980230702503535965648877174,59980230702503535965650224903⟩⟩,⟨⟨(-999999653518764041329186153413),(-999999653518764041316071930766)⟩,⟨(-832443602815294557765407491),(-832443602815294544652193622)⟩⟩,⟨⟨590814081343562403244658797222,590814081343562403247172821020⟩,⟨(-749015502442914847734636268334),(-749015502442914847731408653102)⟩⟩⟩

def p5_7 : PointBox := ⟨⟨999647284538971649498539644953,999647284538971649498541904804⟩,⟨⟨398414844773222229858569022971,398414844773222229872372070785⟩,⟨995685794243918760196676098667,995685794243918760231173797726⟩⟩,⟨⟨(-1149718922670025655537814977374),(-1149718922670025655537807897470)⟩,⟨60049835757925635883728097456,60049835757925635883729890407⟩⟩,⟨⟨(-999999386070221218746835059841),(-999999386070221218733718253290)⟩,⟨(-1108088074411391807220287308),(-1108088074411391794104823676)⟩⟩,⟨⟨590738809215624974568762085106,590738809215624974571277963934⟩,⟨(-749008452428135158285917331640),(-749008452428135158282687710882)⟩⟩⟩

def p5_8 : PointBox := ⟨⟨999547047561187954343256724721,999547047561187954343259624991⟩,⟨⟨398483725816633418921305423012,398483725816633418935111297455⟩,⟨995758079102994660736051167670,995758079102994660770553109542⟩⟩,⟨⟨(-1149802390035717266216798843720),(-1149802390035717266216789756033)⟩,⟨60129372735836660490725098406,60129372735836660490727400024⟩⟩,⟨⟨(-999998987546977688958473278600),(-999998987546977688945353521429)⟩,⟨(-1422991573959935226253694974),(-1422991573959935213135662524)⟩⟩,⟨⟨590652808442450147023042071912,590652808442450147025560069861⟩,⟨(-749000386605015028579375512425),(-749000386605015028576143600790)⟩⟩⟩

def p5_9 : PointBox := ⟨⟨999434329102899544425380759997,999434329102899544425384380408⟩,⟨⟨398561204108984182393977006828,398561204108984182407786060814⟩,⟨995839374087766038827459225105,995839374087766038861965939007⟩⟩,⟨⟨(-1149896261398400309553229227939),(-1149896261398400309553217881786)⟩,⟨60218836961726792118171159720,60218836961726792118174033626⟩⟩,⟨⟨(-999998420944820660575124024645),(-999998420944820660562000949877)⟩,⟨(-1777106599296621682448321624),(-1777106599296621669327401000)⟩⟩,⟨⟨590556088833924694688457081317,590556088833924694690977462952⟩,⟨(-748991301520328258099716904374),(-748991301520328258096482415978)⟩⟩⟩

def p5_10 : PointBox := ⟨⟨999309146139091626905000916215,999309146139091626905005336135⟩,⟨⟨398647275089635847443534828956,398647275089635847457347415086⟩,⟨995929670201248925533119920291,995929670201248925567631934394⟩⟩,⟨⟨(-1150000526369252552825155942759),(-1150000526369252552825142088306)⟩,⟨60318223169424099892509489817,60318223169424099892512999454⟩⟩,⟨⟨(-999997644723183146489719977565),(-999997644723183146476593219853)⟩,⟨(-2170379710183946063432918087),(-2170379710183946050308791533)⟩⟩,⟨⟨590448661428363672614705994436,590448661428363672617229023554⟩,⟨(-748981193296769117816915618431),(-748981193296769117813678268333)⟩⟩⟩

def p5_11 : PointBox := ⟨⟨999171517521858092125488315288,999171517521858092125493614382⟩,⟨⟨398741933683313514828432710842,398741933683313514842249181850⟩,⟨996028957444891167400322707508,996028957444891167434840550694⟩⟩,⟨⟨(-1150115173402940441427709372316),(-1150115173402940441427692758506)⟩,⟨60427525498505925236825158538,60427525498505925236829367702⟩⟩,⟨⟨(-999996612836504511652870158151),(-999996612836504511639739351111)⟩,⟨(-2602751528306181257514635752),(-2602751528306181244386984434)⟩⟩,⟨⟨590330538493273790540234722412,590330538493273790542760663865⟩,⟨(-748970057635623070857241860408),(-748970057635623070854001362468)⟩⟩⟩

def p5_12 : PointBox := ⟨⟨999021463977562457617061451481,999021463977562457617067708701⟩,⟨⟨398845174297617546348564737966,398845174297617546362385446010⟩,⟨996137224817979868406744231241,996137224817979868441268430354⟩⟩,⟨⟨(-1150240189796934871768337489727),(-1150240189796934871768317867421)⟩,⟨60546737491425395089524400940,60546737491425395089529372986⟩⟩,⟨⟨(-999995274769013290938424293665),(-999995274769013290925289074041)⟩,⟨(-3074156737320050597723378402),(-3074156737320050584591886571)⟩⟩,⟨⟨590201733526195820677494076038,590201733526195820680023192949⟩,⟨(-748957889819732911305021865748),(-748957889819732911301777935893)⟩⟩⟩

def p5_13 : PointBox := ⟨⟨998859008103716553988602772121,998859008103716553988610067161⟩,⟨⟨398956990820289104984791320175,398956990820289104998616617833⟩,⟨996254460316993814889648821679,996254460316993814924179905461⟩⟩,⟨⟨(-1150375561690763435983912695035),(-1150375561690763435983889812421)⟩,⟨60675852090353939631268906145,60675852090353939631274705160⟩⟩,⟨⟨(-999993575572912641409918777379),(-999993575572912641396778779131)⟩,⟨(-3584524082978630590451307980),(-3584524082978630577315657060)⟩⟩,⟨⟨590062261255624218056947956273,590062261255624218059480514043⟩,⟨(-748944684716759891302624850515),(-748944684716759891299377202039)⟩⟩⟩

def p5_14 : PointBox := ⟨⟨998684174365577422766150024945,998684174365577422766158436315⟩,⟨⟨399077376616230586384226447179,399077376616230586398056686113⟩,⟨996380650934902092460761598018,996380650934902092495300091865⟩⟩,⟨⟨(-1150521274065200534514725676592),(-1150521274065200534514699285190)⟩,⟨60814861633740782916899144438,60814861633740782916905833718⟩⟩,⟨⟨(-999991455909946838908103457522),(-999991455909946838894958319694)⟩,⟨(-4133776373347663380604186242),(-4133776373347663367464062679)⟩⟩,⟨⟨589912137642001952497921714514,589912137642001952500457975632⟩,⟨(-748930436782739358519810035090),(-748930436782739358516558384764)⟩⟩⟩

def p5_15 : PointBox := ⟨⟨998496989092462938672730295006,998496989092462938672739902388⟩,⟨⟨399206324524281860643432482696,399206324524281860657268015272⟩,⟨996515782660410212855099195593,996515782660410212889645627961⟩⟩,⟨⟨(-1150677310741396878370960602238),(-1150677310741396878370930449496)⟩,⟨60963757852590467526884860193,60963757852590467526892504124⟩⟩,⟨⟨(-999988852096325277381528578737),(-999988852096325277368377935830)⟩,⟨(-4721830479135068362365084326),(-4721830479135068349220169976)⟩⟩,⟨⟨589751379878788372640879086691,589751379878788372643419317098⟩,⟨(-748915140065930376521377766227),(-748915140065930376518121826804)⟩⟩⟩

def p5_16 : PointBox := ⟨⟨998297480473786711203269190530,998297480473786711203280071623⟩,⟨⟨399343826853753324684828048460,399343826853753324698669225556⟩,⟨996659840477155177347132992866,996659840477155177381687886664⟩⟩,⟨⟨(-1150843654379950028425977624668),(-1150843654379950028425943463821)⟩,⟨61122531866459568279830588845,61122531866459568279839250414⟩⟩,⟨⟨(-999985696150978481160620460910),(-999985696150978481147463955857)⟩,⟨(-5348597334156017916476613355),(-5348597334156017903326598440)⟩⟩,⟨⟨589580006393597744712078483994,589580006393597744714622944629⟩,⟨(-748898788210958749449490684468),(-748898788210958749446230174659)⟩⟩⟩

def p5_17 : PointBox := ⟨⟨998085678554812862623813206780,998085678554812862623825441549⟩,⟨⟨399489875380716847994807738150,399489875380716848008654912083⟩,⟨996812808362851011765316340241,996812808362851011799880224383⟩⟩,⟨⟨(-1151020286479917744237561276454),(-1151020286479917744237522853164)⟩,⟨61291174179173845279404633182,61291174179173845279414377362⟩⟩,⟨⟨(-999981915847118695845245352822),(-999981915847118695832082619532)⟩,⟨(-6013981935957480772980328604),(-6013981935957480759824894264)⟩⟩,⟨⟨589398036849405931877257148688,589398036849405931879806106901⟩,⟨(-748881374463252819631314186803),(-748881374463252819628048817813)⟩⟩⟩

def p5_18 : PointBox := ⟨⟨997861615232131321709883446193,997861615232131321709897111715⟩,⟨⟨399644461344055778177067372448,399644461344055778190920893409⟩,⟨996974669288386416219200737479,996974669288386416253774132861⟩⟩,⟨⟨(-1151207187377776039702014826051),(-1151207187377776039701971894564)⟩,⟨61469674674267183200168681617,61469674674267183200179571275⟩⟩,⟨⟨(-999977434767075683083426775480),(-999977434767075683070257460107)⟩,⟨(-6717883346627635341147087676),(-6717883346627635327985927218)⟩⟩,⟨⟨589205492145822504257121773665,589205492145822504259675489432⟩,⟨(-748862891673771352102990678081),(-748862891673771352099720169874)⟩⟩⟩

def p5_19 : PointBox := ⟨⟨997625324248854314628080502465,997625324248854314628095678728⟩,⟨⟨399807575441275257752021161933,399807575441275257765881381980⟩,⟨997145405216876280393991919384,997145405216876280428575354642⟩⟩,⟨⟨(-1151404336246323967254139738532),(-1151404336246323967254092043434)⟩,⟨61658022610143761840226300501,61658022610143761840238401032⟩⟩,⟨⟨(-999972172360376408746104336584),(-999972172360376408732928073587)⟩,⟨(-7460194693817011944825041545),(-7460194693817011931657836522)⟩⟩,⟨⟨589002394420425395006813684377,589002394420425395009372425860⟩,⟨(-748843332304022763488761055143),(-748843332304022763485485118090)⟩⟩⟩

def p5_20 : PointBox := ⟨⟨997376841189534776351745065921,997376841189534776351761828639⟩,⟨⟨399979207824074189982319114080,399979207824074189996186382164⟩,⟨997324997102668922636208364208,997324997102668922670802356151⟩⟩,⟨⟨(-1151611711093537276304963636442),(-1151611711093537276304910935209)⟩,⟨61856206614965002675986159389,61856206614965002675999532999⟩⟩,⟨⟨(-999966044005035383367400785679),(-999966044005035383354217227516)⟩,⟨(-8240803171999634734389188894),(-8240803171999634721215638765)⟩⟩,⟨⟨588788767050155044388824873553,588788767050155044391388897830⟩,⟨(-748822688431374894072922891936),(-748822688431374894069641249559)⟩⟩⟩

def p5_21 : PointBox := ⟨⟨997116203474807447879223473180,997116203474807447879241903032⟩,⟨⟨400159348093680279303296844708,400159348093680279317171513051⟩,⟨997513424890311018020642443209,997513424890311018055247521961⟩⟩,⟨⟨(-1151829288761373215123399138211),(-1151829288761373215123341172145)⟩,⟨62064214681262937535684986845,62064214681262937535699699926⟩⟩,⟨⟨(-999958961072020488777667383499),(-999958961072020488764476162515)⟩,⟨(-9059590044003798655895480655),(-9059590044003798642715264700)⟩⟩,⟨⟨588564634652764801580654516263,588564634652764801583224094200⟩,⟨(-748800951754654461138368085398),(-748800951754654461135080445026)⟩⟩⟩

def p5_22 : PointBox := ⟨⟨996843450355753466285785569634,996843450355753466285805741550⟩,⟨⟨400347985295949661262233220002,400347985295949661276115636679⟩,⟨997710667513472287121351806292,997710667513472287155968486105⟩⟩,⟨⟨(-1152057044924528868381182293818),(-1152057044924528868381118821705)⟩,⟨62282034160281748651990804170,62282034160281748652006918768⟩⟩,⟨⟨(-999950830992857206203141309182),(-999950830992857206189942081854)⟩,⟨(-9916430642843431844506382547),(-9916430642843431831319204069)⟩⟩,⟨⟨588330023088324183143420848938,588330023088324183145996236326⟩,⟨(-748778113600035268607393581659),(-748778113600035268604099668461)⟩⟩⟩

def p5_23 : PointBox := ⟨⟨996558622907989296281204359729,996558622907989296281226354430⟩,⟨⟨400545107916232727796517767572,400545107916232727810408284480⟩,⟨997916702893832123274845137372,997916702893832123309473948049⟩⟩,⟨⟨(-1152294954089155545054256465743),(-1152294954089155545054187227528)⟩,⟨62509651756049334346569690996,62509651756049334346587274031⟩⟩,⟨⟨(-999941557330332249378046134813),(-999941557330332249364838534082)⟩,⟨(-10811194373882256837250004359),(-10811194373882256824055543065)⟩⟩,⟨⟨588084959460771417726391481002,588084959460771417728972949706⟩,⟨(-748754164927214182599837414759),(-748754164927214182596536935047)⟩⟩⟩

def p5_24 : PointBox := ⟨⟨996261764025480893458162299959,996261764025480893458186190138⟩,⟨⟨400750703874007846281549924970,400750703874007846295448888260⟩,⟨998131507939930441687487281286,998131507939930441722128730515⟩⟩,⟨⟨(-1152542989591531853268413951804),(-1152542989591531853268338712053)⟩,⟨62747053519180861525600725053,62747053519180861525619837291⟩⟩,⟨⟨(-999931039852255702091530705220),(-999931039852255702078314397644)⟩,⟨(-11743744717364172801355213157),(-11743744717364172788153182239)⟩⟩,⟨⟨587829472119511538787864593866,587829472119511538790452394611⟩,⟨(-748729096335873814614824817814),(-748729096335873814611517502884)⟩⟩⟩

def p5_25 : PointBox := ⟨⟨995952918414084030795745676648,995952918414084030795771544449⟩,⟨⟨400964760517284765125959645817,400964760517284765139867407977⟩,⟨998355058545985138765480704180,998355058545985138800135325152⟩⟩,⟨⟨(-1152801123596698219950970315124),(-1152801123596698219950888807977)⟩,⟨62994224840416375107486909314,62994224840416375107507619347⟩⟩,⟨⟨(-999919174608238863795752084512),(-999919174608238863782526698004)⟩,⟨(-12713939231344433350814699491),(-12713939231344433337604773437)⟩⟩,⟨⟨587563590661056120970180984367,587563590661056120972775393839⟩,⟨(-748702898072430783543112487676),(-748702898072430783539798038335)⟩⟩⟩

def p5_26 : PointBox := ⟨⟨995632132584811761221095158343,995632132584811761221123075697⟩,⟨⟨401187264616779594854247008736,401187264616779594868163914967⟩,⟨998587329590678654497106513433,998587329590678654531774811226⟩⟩,⟨⟨(-1153069327097055733760248336494),(-1153069327097055733760160327557)⟩,⟨63251150443894645542909803562,63251150443894645542932172094⟩⟩,⟨⟨(-999905854009443120200113668606),(-999905854009443120186878873818)⟩,⟨(-13721629555057288351060192238),(-13721629555057288337842088123)⟩⟩,⟨⟨587287345930700591373359952352,587287345930700591375961220180⟩,⟨(-748675560037068354528089492969),(-748675560037068354524767641958)⟩⟩⟩

def p5_27 : PointBox := ⟨⟨995299454846830030124586446493,995299454846830030124616495420⟩,⟨⟨401418202359863351662912302255,401418202359863351676838704529⟩,⟨998828294935916234554167566897,998828294935916234588850073841⟩⟩,⟨⟨(-1153347569910932309665588578047),(-1153347569910932309665493800408)⟩,⟨63517814380165548801114342505,63517814380165548801138438614⟩⟩,⟨⟨(-999890966911253278983170274564),(-999890966911253278969925700844)⟩,⟨(-14766661412756791341945482000),(-14766661412756791328718875542)⟩⟩,⟨⟨587000770024234884427805920348,587000770024234884430414323932⟩,⟨(-748647071791052176719306471268),(-748647071791052176715976918732)⟩⟩⟩

def p5_28 : PointBox := ⟨⟨994954935300182492663532156579,994954935300182492663564405848⟩,⟨⟨401657559344286150431236399550,401657559344286150445172640403⟩,⟨999077927425558591962073607599,999077927425558591996770819547⟩⟩,⟨⟨(-1153635820681119292695487889284),(-1153635820681119292695386117072)⟩,⟨63794200018943388660692664905,63794200018943388660718547346⟩⟩,⟨⟨(-999874398698826944727265975924),(-999874398698826944714011307981)⟩,⟨(-15848874618068444874581753616),(-15848874618068444861346375701)⟩⟩,⟨⟨586703896289683048474050333215,586703896289683048476666114718⟩,⟨(-748617422564327763110986597160),(-748617422564327763107649084820)⟩⟩⟩

def p5_29 : PointBox := ⟨⟨994598625828245631470158677447,994598625828245631470193211284⟩,⟨⟨401905320571679236175533657251,401905320571679236189480089707⟩,⟨999336198884131770673357644545,999336198884131770708070099265⟩⟩,⟨⟨(-1153934046873381736711356252440),(-1153934046873381736711247210244)⟩,⟨64080290041603688931438493705,64080290041603688931466233947⟩⟩,⟨⟨(-999856031375469652827652775995),(-999856031375469652814387635017)⟩,⟨(-16968103078890262272605487070),(-16968103078890262259361005041)⟩⟩,⟨⟨586396759329067253621387112443,586396759329067253624010556379⟩,⟨(-748586601263398273841183984259),(-748586601263398273837838204072)⟩⟩⟩

def p5_30 : PointBox := ⟨⟨994230580089915310995379033463,994230580089915310995415919817⟩,⟨⟨402161470440837147017094158494,402161470440837147031051124002⟩,⟨999603080115517115123493998978,999603080115517115158222189438⟩⟩,⟨⟨(-1154242214774945711548326479814),(-1154242214774945711548209942804)⟩,⟨64376066433426103416685970874,64376066433426103416715627642⟩⟩,⟨⟨(-999835743653783640400913892295),(-999835743653783640387637967463)⟩,⟨(-18124174802882664293424335969),(-18124174802882664280170484931)⟩⟩,⟨⟨586079395000191494084878023568,586079395000191494087509370963⟩,⟨(-748554596479481079460967736755),(-748554596479481079457613431961)⟩⟩⟩

def p5_31 : PointBox := ⟨⟨993850853511525945164537346949,993850853511525945164576669841⟩,⟨⟨402425992740782407947897198606,402425992740782407961865049526⟩,⟨999878540901624350804793942112,999878540901624350839538404893⟩⟩,⟨⟨(-1154560289492966108439545821438),(-1154560289492966108439421513201)⟩,⟨64681510475586214070754039780,64681510475586214070785685046⟩⟩,⟨⟨(-999813411049536304117662916734),(-999813411049536304104375831089)⟩,⟨(-19316911903587401168565927580),(-19316911903587401155302376486)⟩⟩,⟨⟨585751840418440124101455781749,585751840418440124104095317762⟩,⟨(-748521396496941492687292057948),(-748521396496941492683928919947)⟩⟩⟩

def p5_32 : PointBox := ⟨⟨993459503278503495288752437355,993459503278503495288794259907⟩,⟨⟨402698870643615263080715406521,402698870643615263094694480365⟩,⟨1000162550001050881016154518171,1000162550001050881050915732302⟩⟩,⟨⟨(-1154888234952978529251303899724),(-1154888234952978529251171609060)⟩,⟨64996602736899112978585874773,64996602736899112978619564039⟩⟩,⟨⟨(-999788905978192581459827021928),(-999788905978192581446528485810)⟩,⟨(-20546130607216392924323317642),(-20546130607216392911049822454)⟩⟩,⟨⟨585414133958586214813239868430,585414133958586214815887822221⟩,⟨(-748486989302001965952506885930),(-748486989302001965949134672129)⟩⟩⟩

def p5_33 : PointBox := ⟨⟨993056588326753555259672279564,993056588326753555259716689524⟩,⟨⟨402980086697151064714980582885,402980086697151064728971234038⟩,⟨1000455075147730504183927216563,1000455075147730504218705728144⟩⟩,⟨⟨(-1155226013897338959645937468554),(-1155226013897338959645796905518)⟩,⟨65321323065317791546227200422,65321323065317791546263009372⟩⟩,⟨⟨(-999762097854053694248783055858),(-999762097854053694235472677972)⟩,⟨(-21811641260152012198206341024),(-21811641260152012184922556120)⟩⟩,⟨⟨585066315256604570294804505084,585066315256604570297461173176⟩,⟨(-748451362591724957586781087405),(-748451362591724957583399476043)⟩⟩⟩

def p5_34 : PointBox := ⟨⟨992642169333785820950332043789,992642169333785820950379104009⟩,⟨⟨403269622817348050487508838344,403269622817348050501511403503⟩,⟨1000756083049574854450653887021,1000756083049574854485450173553⟩⟩,⟨⟨(-1155573587883655039798223274935),(-1155573587883655039798074227469)⟩,⟨65655650579189490700040938701,65655650579189490700078923316⟩⟩,⟨⟨(-999732853191942912549619817056),(-999732853191942912536297310043)⟩,⟨(-23113248337200892543485269458),(-23113248337200892530190952809)⟩⟩,⟨⟨584708425211484094308718657699,584708425211484094311384269719⟩,⟨(-748414503783267571650806194840),(-748414503783267571647414942968)⟩⟩⟩

def p5_35 : PointBox := ⟨⟨992216308709576280444376995039,992216308709576280444426792372⟩,⟨⟨403567460280528355155734090711,403567460280528355169748923017⟩,⟨1001065539387110965540441016241,1001065539387110965575255620641⟩⟩,⟨⟨(-1155930917283212858657218701228),(-1155930917283212858657060880361)⟩,⟨65999563658273299004761074361,65999563658273299004801310358⟩⟩,⟨⟨(-999701035711377234417778414364),(-999701035711377234404443391783)⟩,⟨(-24450750450643830122542662223),(-24450750450643830109237472774)⟩⟩,⟨⟨584340505987034055520535878589,584340505987034055523210730005⟩,⟨(-748376400023405975213722949774),(-748376400023405975210321737111)⟩⟩⟩

def p5_36 : PointBox := ⟨⟨991779070587168501214190422709,991779070587168501214243013909⟩,⟨⟨403873579715395221225289886245,403873579715395221239317317439⟩,⟨1001383408812118454176901838224,1001383408812118454211735220396⟩⟩,⟨⟨(-1156297961279403308905247022391),(-1156297961279403308905080233601)⟩,⟨66353039934522421477393216530,66353039934522421477435755694⟩⟩,⟨⟨(-999666506443162133652022060240),(-999666506443162133638674261341)⟩,⟨(-25823940360124756500380726731),(-25823940360124756487064448690)⟩⟩,⟨⟨583962601013678657913473740382,583962601013678657916158045534⟩,⟨(-748337038198327492189083333029),(-748337038198327492185671934808)⟩⟩⟩

def p5_37 : PointBox := ⟨⟨991330520813015429659506179696,991330520813015429659561656473⟩,⟨⟨404187961094849492725253620809,404187961094849492739294006754⟩,⟨1001709654946269914494476792920,1001709654946269914529329508310⟩⟩,⟨⟨(-1156674677866152149652666077955),(-1156674677866152149652490014930)⟩,⟨66716056282634680543659144720,66716056282634680543704067484⟩⟩,⟨⟨(-999629123838344805031839086529),(-999629123838344805018478105862)⟩,⟨(-27232604983422093836699587527),(-27232604983422093823371860573)⟩⟩,⟨⟨583574754990234185139784044094,583574754990234185142478113025⟩,⟨(-748296404943688164648970188468),(-748296404943688164645548267495)⟩⟩⟩

def p5_38 : PointBox := ⟨⟨990870726937063157495969900927,990870726937063157496028319798⟩,⟨⟨404510583727608598991468368783,404510583727608599005522040304⟩,⟨1002044240379778208887124865871,1002044240379778208921997372790⟩⟩,⟨⟨(-1157061023846358032452581192808),(-1157061023846358032452395659913)⟩,⟨67088588810374952100433286874,67088588810374952100480645595⟩⟩,⟨⟨(-999588743879459635771646687456),(-999588743879459635758272266619)⟩,⟨(-28676525408146060118558573867),(-28676525408146060105219184219)⟩⟩,⟨⟨583177013885662852658325993288,583177013885662852661030041025⟩,⟨(-748254486654933460787783511312),(-748254486654933460784350842228)⟩⟩⟩

def p5_39 : PointBox := ⟨⟨990399758202578148341955745660,990399758202578148342017197270⟩,⟨⟨404841426249631360375989035732,404841426249631360390056347216⟩,⟨1002387126670054433518392721136,1002387126670054433553285571260⟩⟩,⟨⟨(-1157456954830342853352798923236),(-1157456954830342853352603615488)⟩,⟨67470612848673384051733508002,67470612848673384051783383094⟩⟩,⟨⟨(-999545220193997954484936049933),(-999545220193997954471547789103)⟩,⟨(-30155476904405670263821834527),(-30155476904405670250470427171)⟩⟩,⟨⟨582769424940797369866660874190,582769424940797369869375209358⟩,⟨(-748211269497879693363012784784),(-748211269497879693359569032306)⟩⟩⟩

def p5_40 : PointBox := ⟨⟨989917685535719456485896567842,989917685535719456485961099845⟩,⟨⟨405180466615352075390191253975,405180466615352075404272529196⟩,⟨1002738274340380428210204927509,1002738274340380428245118553716⟩⟩,⟨⟨(-1157862425234318899349719533702),(-1157862425234318899349514281701)⟩,⟨67862102941503392013483349018,67862102941503392013535786431⟩⟩,⟨⟨(-999498404170032456226497387516),(-999498404170032456213095066623)⟩,⟨(-31669228938489278156348636433),(-31669228938489278142985035444)⟩⟩,⟨⟨582352036670030086174098307331,582352036670030086176823122150⟩,⟨(-748166739419553593466768734223),(-748166739419553593463313700007)⟩⟩⟩

def p5_41 : PointBox := ⟨⟨989424581534857508219624459306,989424581534857508219692169824⟩,⟨⟨405527682088727478938043651058,405527682088727478952139248867⟩,⟨1003097642878599790568792441491,1003097642878599790603727415123⟩⟩,⟨⟨(-1158277388278877361694816323011),(-1158277388278877361694600795869)⟩,⟨68263032835543577165339589880,68263032835543577165394676974⟩⟩,⟨⟨(-999448145073925075617581729343),(-999448145073925075604164918694)⟩,⟨(-33217545187602524256993238089),(-33217545187602524243617058335)⟩⟩,⟨⟨581924898862960470214931086164,581924898862960470217666711188⟩,⟨(-748120882159287361851256184974),(-748120882159287361847789508235)⟩⟩⟩

def p5_42 : PointBox := ⟨⟨988920520459641054289964595114,988920520459641054290035532971⟩,⟨⟨405883049234100294028231228493,405883049234100294042341472596⟩,⟨1003465190735831442927346967712,1003465190735831442962303723753⟩⟩,⟨⟨(-1158701795987502890950729133364),(-1158701795987502890950503155977)⟩,⟨68673375469627864493806924148,68673375469627864493864708640⟩⟩,⟨⟨(-999394290170045481142790199590),(-999394290170045481129358675718)⟩,⟨(-34800183555707492793193677880),(-34800183555707492779804739659)⟩⟩,⟨⟨581488062585994550306319491232,581488062585994550309066123241⟩,⟨(-748073683260066393722295309014),(-748073683260066393718816786255)⟩⟩⟩

def p5_43 : PointBox := ⟨⟨988405578219813939945327885197,988405578219813939945402145910⟩,⟨⟨406246543906883234688976870188,406246543906883234703102116759⟩,⟨1003840875325209887916531182143,1003840875325209887951510283798⟩⟩,⟨⟨(-1159135599185118969420312864863),(-1159135599185118969420076112366)⟩,⟨69093102963988315942442816813,69093102963988315942503384875⟩⟩,⟨⟨(-999336684842425793960246872794),(-999336684842425793946800218137)⟩,⟨(-36416896190506741202642379992),(-36416896190506741189240309925)⟩⟩,⟨⟨581041580183889826952869872497,581041580183889826955627836569⟩,⟨(-748025128080126742912475865194),(-748025128080126742908985142337)⟩⟩⟩

def p5_44 : PointBox := ⟨⟨987879832363783376730598655075,987879832363783376730676277032⟩,⟨⟨406618141244067455763140422842,406618141244067455777280987243⟩,⟨1004224653020656374144112397153,1004224653020656374179114249367⟩⟩,⟨⟨(-1159578747496668975495330930596),(-1159578747496668975495083259125)⟩,⟨69522186609295232280204717253,69522186609295232280268108928⟩⟩,⟨⟨(-999275172718275595543814097208),(-999275172718275595530352133446)⟩,⟨(-38067429501615642148177105874),(-38067429501615642134761768841)⟩⟩,⟨⟨580585505281239054831993969766,580585505281239054834763435492⟩,⟨(-747975201804799257641218598037),(-747975201804799257637715503713)⟩⟩⟩

def p5_45 : PointBox := ⟨⟨987343362066941437606535433350,987343362066941437606616520979⟩,⟨⟨406997815654559585844778763129,406997815654559585858935006911⟩,⟨1004616479155685277499868462258,1004616479155685277534893651803⟩⟩,⟨⟨(-1160031189345737911506611284055),(-1160031189345737911506352338002)⟩,⟨69960596855499319830954993656,69960596855499319831021303346⟩⟩,⟨⟨(-999209595793279781765138727493),(-999209595793279781751661001181)⟩,⟨(-39751524179966174804454729217),(-39751524179966174791025715706)⟩⟩,⟨⟨580119892783886182404749703575,580119892783886182407531022105⟩,⟨(-747923889458597182661428837888),(-747923889458597182657912987687)⟩⟩⟩

def p5_46 : PointBox := ⟨⟨986796248119741534133563401090,986796248119741534133647994048⟩,⟨⟨407385540809351622838680287001,407385540809351622852852525371⟩,⟨1005016308022250085925659949334,1005016308022250085960708883331⟩⟩,⟨⟨(-1160492871953219861716750105562),(-1160492871953219861716479734932)⟩,⟨70408303300480863583731136704,70408303300480863583800406346⟩⟩,⟨⟨(-999139794558600348240879284915),(-999139794558600348227385614039)⟩,⟨(-41468915218484917134059726471),(-41468915218484917120616897239)⟩⟩,⟨⟨579644798880267632232097835285,579644798880267632234891181112⟩,⟨(-747871175917543881487062309478),(-747871175917543881483533526493)⟩⟩⟩

def p5_47 : PointBox := ⟨⟨986238572915531671358635963955,986238572915531671358724163831⟩,⟨⟨407781289631528117483693284393,407781289631528117497881875921⟩,⟨1005424092869633456025247114146,1005424092869633456060320370446⟩⟩,⟨⟨(-1160963741336036340089897778083),(-1160963741336036340089615633872)⟩,⟨70865274678511016627207978464,70865274678511016627280301152⟩⟩,⟨⟨(-999065608129501754560058820448),(-999065608129501754546548764756)⟩,⟨(-43219331934087524533465736654),(-43219331934087524520008694955)⟩⟩,⟨⟨579160281042672004384175041937,579160281042672004386980760150⟩,⟨(-747817045921737187605502300793),(-747817045921737187601960208008)⟩⟩⟩

def p5_48 : PointBox := ⟨⟨985670420438146312672227197256,985670420438146312672319028744⟩,⟨⟨408185034286115218676452200077,408185034286115218690657448197⟩,⟨1005839785903385888554146253974,1005839785903385888589244196791⟩⟩,⟨⟨(-1161443742305910778308500079570),(-1161443742305910778308206057544)⟩,⟨71331478848530487319941024885,71331478848530487320016431166⟩⟩,⟨⟨(-998986874375518115035627211755),(-998986874375518115022100653556)⟩,⟨(-45002497991031432670665902444),(-45002497991031432657194572626)⟩⟩,⟨⟨578666398028411189159757981746,578666398028411189162576207156⟩,⟨(-747761484088146745123242240800),(-747761484088146745119686708078)⟩⟩⟩

def p5_49 : PointBox := ⟨⟨985091876249258723254966445632,985091876249258723255062023610⟩,⟨⟨408596746169776305556959272067,408596746169776305571181543737⟩,⟨1006263338284317646544665693407,1006263338284317646579788936243⟩⟩,⟨⟨(-1161932818468204493089547848791),(-1161932818468204493089241554913)⟩,⟨71806882782251080111929688417,71806882782251080112008283324⟩⟩,⟨⟨(-998903430052079102581708215696),(-998903430052079102568164660495)⟩,⟨(-46818131425667893810993050107),(-46818131425667893797506980996)⟩⟩,⟨⟨578163209880895783835517028099,578163209880895783838348144098⟩,⟨(-747704474923640547200625663467),(-747704474923640547197056269149)⟩⟩⟩

def p5_50 : PointBox := ⟨⟨984503027475495696804470887438,984503027475495696804570240823⟩,⟨⟨409016395900359085058936403731,409016395900359085073176004153⟩,⟨1006694700127548614501419839151,1006694700127548614536568756374⟩⟩,⟨⟨(-1162430912220819558086099870742),(-1162430912220819558085781185110)⟩,⟨72291452552085723458382797590,72291452552085723458464616027⟩⟩,⟨⟨(-998815110933510131910471669453),(-998815110933510131896910983626)⟩,⟨(-48665944672633746812553219107),(-48665944672633746799052318682)⟩⟩,⟨⟨577650777930607621492219267366,577650777930607621495063421776⟩,⟨(-747646002838236724936659546335),(-747646002838236724933076145214)⟩⟩⟩

def p5_51 : PointBox := ⟨⟨983903962795316606017134575617,983903962795316606017237813371⟩,⟨⟨409443953306299189968234871688,409443953306299189982492162502⟩,⟨1007133820501620869662352357413,1007133820501620869697527544925⟩⟩,⟨⟨(-1162937964753174089444614215202),(-1162937964753174089444282760070)⟩,⟨72785153318912798792881340508,72785153318912798792966483752⟩⟩,⟨⟨(-998721751947321110191962099547),(-998721751947321110178383814696)⟩,⟨(-50545644592522531767358691489),(-50545644592522531753842534153)⟩⟩,⟨⟨577129164795962138271143177980,577129164795962138274000739799⟩,⟨(-747586052158576480111449345072),(-747586052158576480107851532680)⟩⟩⟩

def p5_52 : PointBox := ⟨⟨983294772425658752791609437297,983294772425658752791716571896⟩,⟨⟨409879387415885471448823801108,409879387415885471463099074433⟩,⟨1007580647427678806672046037908,1007580647427678806707247822654⟩⟩,⟨⟨(-1163453916045255535323814173682),(-1163453916045255535323469879782)⟩,⟨73287949319680768027793582040,73287949319680768027882072336⟩⟩,⟨⟨(-998623187309696809360054893608),(-998623187309696809346458946996)⟩,⟨(-52456932501073691591048351305),(-52456932501073691577516915053)⟩⟩,⟨⟨576598434384053228852995664377,576598434384053228855866737517⟩,⟨(-747524607141613892432888960526),(-747524607141613892429276643334)⟩⟩⟩

def p5_53 : PointBox := ⟨⟨982675548108351029315114619659,982675548108351029315225774696⟩,⟨⟨410322666446392341459380432624,410322666446392341473674059353⟩,⟨1008035127878721725068472102198,1008035127878721725103701119476⟩⟩,⟨⟨(-1163978704866757638263247529258),(-1163978704866757638262889969161)⟩,⟨73799803854859283491790489389,73799803854859283491882441208⟩⟩,⟨⟨(-998519250662100726119874215448),(-998519250662100726106260078617)⟩,⟨(-54399504199917655468348340222),(-54399504199917655454801139245)⟩⟩,⟨⟨576058651891273168678678851726,576058651891273168681563847419⟩,⟨(-747461651988518165725405268997),(-747461651988518165721777993334)⟩⟩⟩

def p5_54 : PointBox := ⟨⟨982046383096297936085240870107,982046383096297936085356062077⟩,⟨⟨410773757793084684460006064378,410773757793084684474318338065⟩,⟨1008497207778933854650244865996,1008497207778933854685501452113⟩⟩,⟨⟨(-1164512268776306815114153705931),(-1164512268776306815113782795278)⟩,⟨74320679275743153558063224541,74320679275743153558158664360⟩⟩,⟨⟨(-998409775208903155163109261329),(-998409775208903155149476856589)⟩,⟨(-56373050008913573811203422243),(-56373050008913573797640419079)⟩⟩,⟨⟨575509883803800115602004710369,575509883803800115604903744990⟩,⟨(-747397170858783707909660943756),(-747397170858783707906018601655)⟩⟩⟩

def p5_55 : PointBox := ⟨⟨981407372139436037503315860181,981407372139436037503435206832⟩,⟨⟨411232628018101024257970867045,411232628018101024272302153139⟩,⟨1008966832003096856976106284183,1008966832003096857011391056838⟩⟩,⟨⟨(-1165054544120783772204622941215),(-1165054544120783772204238268517)⟩,⟨74850536971615729416032369213,74850536971615729416131407860⟩⟩,⟨⟨(-998294593855943109875534440875),(-998294593855943109861883265616)⟩,⟨(-58377254800115372272353953280),(-58377254800115372258774687406)⟩⟩,⟨⟨574952197897945643434837671234,574952197897945643437751141873⟩,⟨(-747331147884543266729562638938),(-747331147884543266725904793636)⟩⟩⟩

def p5_56 : PointBox := ⟨⟨980758611470464969945462732635,980758611470464969945586227610⟩,⟨⟨411699242839220800717539423131,411699242839220800731889997202⟩,⟨1009443944376089901857413862799,1009443944376089901892727092518⟩⟩,⟨⟨(-1165605466034746243396322238348),(-1165605466034746243395923790761)⟩,⟨75389337356778473440718317480,75389337356778473440820963371⟩⟩,⟨⟨(-998173539349932684670888636204),(-998173539349932684657218710921)⟩,⟨(-60411798033400614491509415381),(-60411798033400614477913946390)⟩⟩,⟨⟨574385663240354705371193398534,574385663240354705374121359657⟩,⟨(-747263567185079167071712264952),(-747263567185079167068038881169)⟩⟩⟩

def p5_57 : PointBox := ⟨⟨980100198790355151169049998865,980100198790355151169177780806⟩,⟨⟨412173567118521782309576192496,412173567118521782323946433652⟩,⟨1009928487672482475641935956923,1009928487672482475677278318304⟩⟩,⟨⟨(-1166164968439958805590571818644),(-1166164968439958805590159114444)⟩,⟨75937039857453667357156964874,75937039857453667357263347387⟩⟩,⟨⟨(-998046444418611465745992397942),(-998046444418611465732303133449)⟩,⟨(-62476353793795410867974399588),(-62476353793795410854362180374)⟩⟩,⟨⟨573810350188050376714344246344,573810350188050376717287154876⟩,⟨(-747194412881527516486404240746),(-747194412881527516482714811959)⟩⟩⟩

def p5_58 : PointBox := ⟨⟨979432233253634373540190327542,979432233253634373540322398756⟩,⟨⟨412655564850933814043209880966,412655564850933814057600069340⟩,⟨1010420403616225133255969483327,1010420403616225133291341268969⟩⟩,⟨⟨(-1166732984045035789944883985027),(-1166732984045035789944456981249)⟩,⟨76493602898567418814667933446,76493602898567418814778069114⟩⟩,⟨⟨(-997913141911557664252145278968),(-997913141911557664238436661350)⟩,⟨(-64570590830527285106761990858),(-64570590830527285093133046138)⟩⟩,⟨⟨573226330388315683835370019232,573226330388315683838327954938⟩,⟨(-747123669111770063261092830835),(-747123669111770063257387292273)⟩⟩⟩

def p5_59 : PointBox := ⟨⟨978754815453455496867226930350,978754815453455496867363418870⟩,⟨⟨413145199152695276139313873367,413145199152695276153724379015⟩,⟨1010919632880443458273007308458,1010919632880443458308409161890⟩⟩,⟨⟨(-1167309444345203367453327484918),(-1167309444345203367452885731021)⟩,⟨77058983890420328002319288442,77058983890420328002433299104⟩⟩,⟨⟨(-997773464941561769331839224246),(-997773464941561769318110710224)⟩,⟨(-66694172597836513048431194498),(-66694172597836513034785022368)⟩⟩,⟨⟨572633676778404790017464973780,572633676778404790020438366360⟩,⟨(-747051320045508206228672232082),(-747051320045508206224950109468)⟩⟩⟩

def p5_60 : PointBox := ⟨⟨978068047406447489590742566855,978068047406447489590883450617⟩,⟨⟨413642432249718806802306757561,413642432249718806816737841178⟩,⟨1011426115087340544611023769077,1011426115087340544646455912271⟩⟩,⟨⟨(-1167894279622186944509879531792),(-1167894279622186944509423061577)⟩,⟨77633139215253381469872137186,77633139215253381469990019919⟩⟩,⟨⟨(-997627247026467699873708110894),(-997627247026467699859959791594)⟩,⟨(-68846757297574980957676922341),(-68846757297574980944013651238)⟩⟩,⟨⟨572032463585075778941308957033,572032463585075778944297819710⟩,⟨(-746977349899513467534734220891),(-746977349899513467530995527457)⟩⟩⟩

def p5_61 : PointBox := ⟨⟨977372032537352099707564594678,977372032537352099707710023997⟩,⟨⟨414147225465873022544396353156,414147225465873022558848399390⟩,⟨1011939788808213359725868772883,1011939788808213359761331910259⟩⟩,⟨⟨(-1168487418944230057496649512818),(-1168487418944230057496177800554)⟩,⟨78216024213716848277306568013,78216024213716848277428464560⟩⟩,⟨⟨(-997474322231385674866193808656),(-997474322231385674852425048064)⟩,⟨(-71027997923620074720353747840),(-71027997923620074706672783188)⟩⟩,⟨⟨571422766323937253195203904031,571422766323937253198208730574⟩,⟨(-746901742953048548970263692958),(-746901742953048548966507879787)⟩⟩⟩

def p5_62 : PointBox := ⟨⟨976666875663448469089615340851,976666875663448469089765301992⟩,⟨⟨414659539211187151629599928605,414659539211187151644073202255⟩,⟨1012460591563588392263249897839,1012460591563588392298744272274⟩⟩,⟨⟨(-1169088790166251005200650466426),(-1169088790166251005200163516821)⟩,⟨78807593171250163882251177014,78807593171250163882377092322⟩⟩,⟨⟨(-997314525311180324528890582900),(-997314525311180324515101439155)⟩,⟨(-73237542308129509106310891611),(-73237542308129509092612328336)⟩⟩,⟨⟨570804661798600948500152010651,570804661798600948503172838675⟩,⟨(-746824483563452899338306242110),(-746824483563452899334533294017)⟩⟩⟩

def p5_63 : PointBox := ⟨⟨975952682978768036793399319335,975952682978768036793553952213⟩,⟨⟨415179332969985680241336240028,415179332969985680255831116616⟩,⟨1012988459823482026953381105244,1012988459823482026988907390420⟩⟩,⟨⟨(-1169698319930143503844832512588),(-1169698319930143503844329830364)⟩,⟨79407799304380999681641279858,79407799304380999681771348339⟩⟩,⟨⟨(-997147691853136929586632739865),(-997147691853136929572822622059)⟩,⟨(-75475033169661339332554936898),(-75475033169661339318838224767)⟩⟩,⟨⟨570178228099632554473285735306,570178228099632554476323031898⟩,⟨(-746745556181886524813720373478),(-746745556181886524809929773132)⟩⟩⟩

def p5_64 : PointBox := ⟨⟨975229562038102108537628050239,975229562038102108537787306896⟩,⟨⟨415706565288960296837601034918,415706565288960296852117752225⟩,⟨1013523329007791125976920422550,1013523329007791126012478762296⟩⟩,⟨⟨(-1170315933665227691601609858987),(-1170315933665227691601091558104)⟩,⟨80016594746951930736822395658,80016594746951930736956594334⟩⟩,⟨⟨(-996973658419708105706938458253),(-996973658419708105693107571789)⟩,⟨(-77740108163181667655255819193),(-77740108163181667641521198621)⟩⟩,⟨⟨569543544603292929859490312441,569543544603292929862544020605⟩,⟨(-746664945369225576532294894528),(-746664945369225576528486737409)⟩⟩⟩

def p5_65 : PointBox := ⟨⟨974497621740804500750193007022,974497621740804500750357059345⟩,⟨⟨416241193765186607734879500438,416241193765186607749418455561⟩,⟨1014065133486819328993959217614,1014065133486819329029550373925⟩⟩,⟨⟨(-1170941555588857847519686166548),(-1170941555588857847519151644537)⟩,⟨80633930536283330806742256225,80633930536283330806880747782⟩⟩,⟨⟨(-996792262691242745789342740960),(-996792262691242745775490360744)⟩,⟨(-80032399931980767786331823108),(-80032399931980767772578610069)⟩⟩,⟨⟨568900691970061904384431354192,568900691970061904387502032619⟩,⟨(-746582635812103049876886400440),(-746582635812103049873060062502)⟩⟩⟩

def p5_66 : PointBox := ⟨⟨973756972314391698446716154350,973756972314391698446884970644⟩,⟨⟨416783175034093286141763810123,416783175034093286156325250495⟩,⟨1014613806581944613404792659385,1014613806581944613440416819086⟩⟩,⟨⟨(-1171575108707193223716564090379),(-1171575108707193223716013406264)⟩,⟨81259756599281342259908448718,81259756599281342260051224752⟩⟩,⟨⟨(-996603343608598595975115131606),(-996603343608598595961241396506)⟩,⟨(-82351536161516501833485683309),(-82351536161516501819714051331)⟩⟩,⟨⟨568249752142936870863325201641,568249752142936870866412839889⟩,⟨(-746498612339087728290858365762),(-746498612339087728287013888149)⟩⟩⟩

def p5_67 : PointBox := ⟨⟨973007725297942996696576594894,973007725297942996696750328613⟩,⟨⟨417332464757391507523897074380,417332464757391507538481381882⟩,⟨1015169280566433682096832854031,1015169280566433682132490725504⟩⟩,⟨⟨(-1172216514816138419348357988043),(-1172216514816138419347790595882)⟩,⟨81894021738499988591747641513,81894021738499988591894850647⟩⟩,⟨⟨(-996406741515539473390288033579),(-996406741515539473376392297658)⟩,⟨(-84697139635202000568195478293),(-84697139635202000554404821464)⟩⟩,⟨⟨567590808345498390076061370504,567590808345498390079166478109⟩,⟨(-746412859936994301129615708123),(-746412859936994301125752524643)⟩⟩⟩

def p5_68 : PointBox := ⟨⟨972249993525303125554051087492,972249993525303125554229672459⟩,⟨⟨417889017610972716193855931708,417889017610972716208463326077⟩,⟨1015731486666408767821058207528,1015731486666408767856749876968⟩⟩,⟨⟨(-1172865694502459750143784828014),(-1172865694502459750143200897565)⟩,⟨82536673618166718990351647137,82536673618166718990503252572⟩⟩,⟨⟨(-996202298300817836144651905149),(-996202298300817836130734456217)⟩,⟨(-87068828292152620601732795811),(-87068828292152620587923434599)⟩⟩,⟨⟨566923945079735057324434805466,566923945079735057327557275986⟩,⟨(-746325363767317380255499638407),(-746325363767317380251617902314)⟩⟩⟩

def p5_69 : PointBox := ⟨⟨971483891108089888077466567966,971483891108089888077650189744⟩,⟨⟨418452787272782961245597638664,418452787272782961260228523439⟩,⟨1016300355061972461328486094112,1016300355061972461364212358904⟩⟩,⟨⟨(-1173522567145084088058936170499),(-1173522567145084088058335047517)⟩,⟨83187658750180897511777533126,83187658750180897511933712160⟩⟩,⟨⟨(-995989857539843190329735154223),(-995989857539843190315795211064)⟩,⟨(-89466215286905184060276831707),(-89466215286905184046448025411)⟩⟩,⟨⟨566249248123619913650818473317,566249248123619913653958908834⟩,⟨(-746236109182781933995395400669),(-746236109182781933991494438077)⟩⟩⟩

def p5_70 : PointBox := ⟨⟨970709533418509370423577921696,970709533418509370423766528631⟩,⟨⟨419023726410682234247935915780,419023726410682234262590518836⟩,⟨1016875814888496184377216653301,1016875814888496184412977637491⟩⟩,⟨⟨(-1174187050916586661752195634640),(-1174187050916586661751577439542)⟩,⟨83846922480094973778423495669,83846922480094973778584224651⟩⟩,⟨⟨(-995769264635836665975319262509),(-995769264635836665961357053677)⟩,⟨(-91888909051120450256728157185),(-91888909051120450242880166582)⟩⟩,⟨⟨565566804528430726544722397734,565566804528430726547880733512⟩,⟨(-746145081744002449929156169109),(-746145081744002449925236084601)⟩⟩⟩

def p5_71 : PointBox := ⟨⟨969927037071981311983318297952,969927037071981311983512058784⟩,⟨⟨419601786670297436321955076402,419601786670297436336633786951⟩,⟨1017457794238077938588806285537,1017457794238077938624602737091⟩⟩,⟨⟨(-1174859062784874319973518208799),(-1174859062784874319972882338689)⟩,⟨84514408973088297523608461010,84514408973088297523773904516⟩⟩,⟨⟨(-995540366960372015358700791651),(-995540366960372015344715608376)⟩,⟨(-94336513357277667410454869335),(-94336513357277667396587025090)⟩⟩,⟨⟨564876702615806514714486756044,564876702615806514717663549347⟩,⟨(-746052267236242929984919082962),(-746052267236242929980979255387)⟩⟩⟩

def p5_72 : PointBox := ⟨⟨969136519909577252114272509999,969136519909577252114471326117⟩,⟨⟨420186918662877798192035630185,420186918662877798206738638636⟩,⟨1018046220161174966784894050291,1018046220161174966820725956228⟩⟩,⟨⟨(-1175538518515070766488820643807),(-1175538518515070766488167371542)⟩,⟨85190061199943765586101486741,85190061199943765586271581767⟩⟩,⟨⟨(-995303013993203283867894291804),(-995303013993203283853886565454)⟩,⟨(-96808627384367908506108237828),(-96808627384367908492221000854)⟩⟩,⟨⟨564179031974532749270761805366,564179031974532749273956859452⟩,⟨(-745957651686269612718411081338),(-745957651686269612714451769199)⟩⟩⟩

def p5_73 : PointBox := ⟨⟨968338100980274098220376085343,968338100980274098220580169907⟩,⟨⟨420779071953161773349762912133,420779071953161773364490638431⟩,⟨1018641018668416964767581135188,1018641018668416964803449367760⟩⟩,⟨⟨(-1176225332671610276698984727119),(-1176225332671610276698313300406)⟩,⟨85873820923037716914274078618,85873820923037716914449029226⟩⟩,⟨⟨(-995057057461279476882076491038),(-995057057461279476868045324444)⟩,⟨(-99304845785590711832107644811),(-99304845785590711818200158401)⟩⟩,⟨⟨563473883457047729565556281510,563473883457047729568770281583⟩,⟨(-745861221379288108690612202246),(-745861221379288108686632635555)⟩⟩⟩

def p5_74 : PointBox := ⟨⟨967531900523025787726212784986,967531900523025787726422064349⟩,⟨⟨421378195047264621426715038874,421378195047264621441467689038⟩,⟨1019242114732605478417539064241,1019242114732605478453443677769⟩⟩,⟨⟨(-1176919418620546402545472876527),(-1176919418620546402544783484550)⟩,⟨86565628682353718565584645706,86565628682353718565764410990⟩⟩,⟨⟨(-994802351476846696857179639521),(-994802351476846696843125360235)⟩,⟨(-101824758758056326601601067437),(-101824758758056326587673688594)⟩⟩,⟨⟨562761349175662706058564061155,562761349175662706061796881629⟩,⟨(-745762962875956425783933881457),(-745762962875956425779934235678)⟩⟩⟩

def p5_75 : PointBox := ⟨⟨966718039948655743887669368999,966718039948655743887884028973⟩,⟨⟨421984235380596096049934691960,421984235380596096064712663520⟩,⟨1019849432290905113370743171796,1019849432290905113406684958861⟩⟩,⟨⟨(-1177620688532082163503757871843),(-1177620688532082163503049848266)⟩,⟨87265423781531113368425599445,87265423781531113368610361744⟩⟩,⟨⟨(-994538752674538453920188501240),(-994538752674538453906110329448)⟩,⟨(-104367952114493610412890639960),(-104367952114493610398942627800)⟩⟩,⟨⟨562041522498488405037640781245,562041522498488405040893032675⟩,⟨(-745662863029465152372805944424),(-745662863029465152368785537067)⟩⟩⟩

def p5_76 : PointBox := ⟨⟨965896641821572852368500031417,965896641821572852368719951342⟩,⟨⟨422597139305817848658398146078,422597139305817848673201606898⟩,⟨1020462894247232172298105637407,1020462894247232172334084513970⟩⟩,⟨⟨(-1178329053383328207336104209392),(-1178329053383328207335377897029)⟩,⟨87973144273959427625516220766,87973144273959427625705899372⟩⟩,⟨⟨(-994266120347355161628231091782),(-994266120347355161614129558912)⟩,⟨(-106934007356961341303187639287),(-106934007356961341289219551733)⟩⟩,⟨⟨561314498045060700892253140587,561314498045060700895524564219⟩,⟨(-745560909002675857760469493603),(-745560909002675857756428655151)⟩⟩⟩

def p5_77 : PointBox := ⟨⟨965067829841313712089471853986,965067829841313712089697264031⟩,⟨⟨423216852080850356787187673823,423216852080850356802017052169⟩,⟨1021082422474846317853619393927,1021082422474846317889636277198⟩⟩,⟨⟨(-1179044422961295404693091464002),(-1179044422961295404692346046404)⟩,⟨88688726948929964746815561986,88688726948929964747010379062⟩⟩,⟨⟨(-993984316581434217897989675502),(-993984316581434217883863812783)⟩,⟨(-109522501752558396007166903584),(-109522501752558395993177811988)⟩⟩,⟨⟨560580371681658281009516965651,560580371681658281012808300595⟩,⟨(-745457088285308561488924196030),(-745457088285308561484862094633)⟩⟩⟩

def p5_78 : PointBox := ⟨⟨964231728823913940019222907513,964231728823913940019453709935⟩,⟨⟨423843317856939381967120841482,423843317856939381981976319066⟩,⟨1021707937819150837579349379010,1021707937819150837615404246255⟩⟩,⟨⟨(-1179766705866128316507007800883),(-1179766705866128316506243543782)⟩,⟨89412107317856137761452930557,89412107317856137761652825806⟩⟩,⟨⟨(-993693206389512540127847497408),(-993693206389512540113697740984)⟩,⟨(-112133008411125911030577483278),(-112133008411125911016567850069)⟩⟩,⟨⟨559839240516305256306402745495,559839240516305256309713798428⟩,⟨(-745351388711168916310893195558),(-745351388711168916306810085336)⟩⟩⟩

def p5_79 : PointBox := ⟨⟨963388464683111335319807169291,963388464683111335320043568834⟩,⟨⟨424476479666792158421576322128,424476479666792158436458305848⟩,⟨1022339360100707060365101113335,1022339360100707060401194807067⟩⟩,⟨⟨(-1180495809514585942300732886202),(-1180495809514585942299949053021)⟩,⟨90143219600574320018722805762,90143219600574320018927981190⟩⟩,⟨⟨(-993392657842983973797765821516),(-993392657842983973783591311940)⟩,⟨(-114765096364932187627550542328),(-114765096364932187613519546633)⟩⟩,⟨⟨559091202893451786994780340190,559091202893451786998111780748⟩,⟨(-745243798475405544077335086201),(-745243798475405544073230216702)⟩⟩⟩

def p5_80 : PointBox := ⟨⟨962538164411383733581268368845,962538164411383733581510202413⟩,⟨⟨425116279412793708941028339743,425116279412793708955936958655⟩,⟨1022976608118468442364651431637,1022976608118468442400783736808⟩⟩,⟨⟨(-1181231640143776120936369962431),(-1181231640143776120935567034528)⟩,⟨90881996711737218784318721629,90881996711737218784529060736⟩⟩,⟨⟨(-993082542202454625822731833484),(-993082542202454625808533290367)⟩,⟨(-117418330650328729119380977503),(-117418330650328729105329361158)⟩⟩,⟨⟨558336358388325918455582040866,558336358388325918458933488976⟩,⟨(-745134306151787759845426302776),(-745134306151787759841300145200)⟩⟩⟩

def p5_81 : PointBox := ⟨⟨961680956060824406774644091991,961680956060824406774891626838⟩,⟨⟨425762657855313878442718854543,425762657855313878457654559970⟩,⟨1023619599653239803479267218436,1023619599653239803515439154856⟩⟩,⟨⟨(-1181974102815149912845150948706),(-1181974102815149912844327978236)⟩,⟨91628370247312000596436219013,91628370247312000596651979795⟩⟩,⟨⟨(-992762734046699888039133197598),(-992762734046699888024909493783)⟩,⟨(-120092272391363412651636383783),(-120092272391363412637563060346)⟩⟩,⟨⟨557574807800949956122636913313,557574807800949956126009219843⟩,⟨(-745022900709993717462035006148),(-745022900709993717457886599570)⟩⟩⟩

def p5_82 : PointBox := ⟨⟨960816968723857889017824341882,960816968723857889018077454075⟩,⟨⟨426415554601115868532909547747,426415554601115868547872494552⟩,⟨1024268251471367153546013265386,1024268251471367153582224725807⟩⟩,⟨⟨(-1182723101418762244313596010842),(-1182723101418762244312753348060)⟩,⟨92382270471195619884200725921,92382270471195619884421826467⟩⟩,⟨⟨(-992433111399927712702786749683),(-992433111399927712688538439522)⟩,⟨(-122786478885334400937170709937),(-122786478885334400923076256493)⟩⟩,⟨⟨556806653149814851084400256486,556806653149814851087793153330⟩,⟨(-744909571532898810045932676708),(-744909571532898810041762361839)⟩⟩⟩

def p5_83 : PointBox := ⟨⟨959946332513799132279968316231,959946332513799132280227231299⟩,⟨⟨427074908091877247628779966277,427074908091877247643770571783⟩,⟨1024922479328663500129141938171,1024922479328663500165393820434⟩⟩,⟨⟨(-1183478538677805039853809859402),(-1183478538677805039852946690610)⟩,⟨93143626301960023175373366312,93143626301960023175600030235⟩⟩,⟨⟨(-992093555857253580952415262840),(-992093555857253580938141398522)⟩,⟨(-125500503690265996294285371082),(-125500503690265996280168878165)⟩⟩,⟨⟨556031997665206219731512045127,556031997665206219734926266803⟩,⟨(-744794308433853961505199563974),(-744794308433853961501006515746)⟩⟩⟩

def p5_84 : PointBox := ⟨⟨959069178545258919744124393057,959069178545258919744388924878⟩,⟨⟨427740655592834600604471971567,427740655592834600619490339518⟩,⟨1025582197974575977227204477737,1025582197974575977263496489809⟩⟩,⟨⟨(-1184240316153419007965073807046),(-1184240316153419007964190689089)⟩,⟨93912365299740119929153460721,93912365299740119929385552056⟩⟩,⟨⟨(-991743952708293566916912947510),(-991743952708293566902614354388)⟩,⟨(-128233896714285232912984640405),(-128233896714285232898846951830)⟩⟩,⟨⟨555250945782175781228262377178,555250945782175781231697476436⟩,⟨(-744677101673943250818140375343),(-744677101673943250813925142344)⟩⟩⟩

def p5_85 : PointBox := ⟨⟨958185638914398487700723255715,958185638914398487700993689066⟩,⟨⟨428412733181563169230899694450,428412733181563169245946284291⟩,⟨1026247321156599576199416041163,1026247321156599576235749249640⟩⟩,⟨⟨(-1185008334249790178610786111118),(-1185008334249790178609882028578)⟩,⟨94688413653277627311218299274,94688413653277627311456095335⟩⟩,⟨⟨(-991384191058782944484792110591),(-991384191058782944470467586001)⟩,⟨(-130986204306875597345811832255),(-130986204306875597331651785942)⟩⟩,⟨⟨554463603133152165874084517884,554463603133152165877541402324⟩,⟨(-744557941979210119616979414575),(-744557941979210119612740971039)⟩⟩⟩

def p5_86 : PointBox := ⟨⟨957295846679036329553261078115,957295846679036329553537260703⟩,⟨⟨429091075736903019603459711407,429091075736903019618534648445⟩,⟨1026917761624942696709238840977,1026917761624942696745613046224⟩⟩,⟨⟨(-1185782492219537217404847275890),(-1185782492219537217403922671978)⟩,⟨95471696167134109760578390362,95471696167134109760821785246⟩⟩,⟨⟨(-991014163950128910565687673291),(-991014163950128910551337899818)⟩,⟨(-133756969351981865321603908332),(-133756969351981865307422205616)⟩⟩,⟨⟨553670076540185225543549543444,553670076540185225547027862659⟩,⟨(-744436820557841225990167227673),(-744436820557841225985906009304)⟩⟩⟩

def p5_87 : PointBox := ⟨⟨956399935838610177778313103612,956399935838610177778595283694⟩,⟨⟨429775616928043455009259224758,429775616928043455024362937865⟩,⟨1027593431137449666412104148235,1027593431137449666448520309149⟩⟩,⟨⟨(-1186562688169395461745260945438),(-1186562688169395461744314922073)⟩,⟨96262136249086744650640209778,96262136249086744650889450756⟩⟩,⟨⟨(-990633768476807207701276453323),(-990633768476807207686900385641)⟩,⟨(-136545731362937648734561649357),(-136545731362937648720357283225)⟩⟩,⟨⟨552870474006818164334677414113,552870474006818164338177973743⟩,⟨(-744313729117296823713834515809),(-744313729117296823709549615841)⟩⟩⟩

def p5_88 : PointBox := ⟨⟨955498041313997181491692318539,955498041313997181491980259967⟩,⟨⟨430466289203777571981558649795,430466289203777571996691195663⟩,⟨1028274240464785303413224094876,1028274240464785303449681762414⟩⟩,⟨⟨(-1187348819066203537875424283975),(-1187348819066203537874457565266)⟩,⟨97059655897720552380146987316,97059655897720552380401894607⟩⟩,⟨⟨(-990242905901513719757716644424),(-990242905901513719743315330888)⟩,⟨(-139352026579184863690416207313),(-139352026579184863676190239073)⟩⟩,⟨⟨552064904709582003288560500719,552064904709582003292082706945⟩,⟨(-744188659881376366693549837410),(-744188659881376366689241973622)⟩⟩⟩

def p5_89 : PointBox := ⟨⟨954590298927195318627780973883,954590298927195318628075005626⟩,⟨⟨431163023781939033321539711567,431163023781939033336701577759⟩,⟨1028960099395886515130632476783,1028960099395886515167132841772⟩⟩,⟨⟨(-1188140780743198325026315389496),(-1188140780743198325025326802372)⟩,⟨97864175690231032494392093858,97864175690231032494652987960⟩⟩,⟨⟨(-989841481767983486670918288649),(-989841481767983486656490335074)⟩,⟨(-142175388064751962423147189446),(-142175388064751962408898266842)⟩⟩,⟨⟨551253478989107097528663740524,551253478989107097532208635291⟩,⟨(-744061605607207863607008983177),(-744061605607207863602676974977)⟩⟩⟩

def p5_90 : PointBox := ⟨⟨953676845380869102636626966843,953676845380869102636926906126⟩,⟨⟨431865750639033304326354716656,431865750639033304341545996151⟩,⟨1029650916743685841063161850528,1029650916743685841099704613052⟩⟩,⟨⟨(-1188938467906623933332105984662),(-1188938467906623933331096073776)⟩,⟨98675614770451346575420256676,98675614770451346575687005260⟩⟩,⟨⟨(-989429406011391037221218876260),(-989429406011391037206765103406)⟩,⟨(-145015345808455422354136438592),(-145015345808455422339865396669)⟩⟩,⟨⟨550436308340846637353519567747,550436308340846637357086710821⟩,⟨(-743932559602149337953853552489),(-743932559602149337949497938978)⟩⟩⟩

def p5_91 : PointBox := ⟨⟨952757818237762664040135580240,952757818237762664040441699936⟩,⟨⟨432574398500075767030222766462,432574398500075767045443900784⟩,⟨1030346600351111755033321565199,1030346600351111755069907750877⟩⟩,⟨⟨(-1189741774142660256060457777506),(-1189741774142660256059425553224)⟩,⟨99493890837118383285272907896,99493890837118383285545783951⟩⟩,⟨⟨(-989006593066247471871080174942),(-989006593066247471856599430738)⟩,⟨(-147871426825786658167353630123),(-147871426825786658153059355324)⟩⟩,⟨⟨549613505405407286636448748589,549613505405407286640039022864⟩,⟨(-743801515740590584311934147810),(-743801515740590584307553933535)⟩⟩⟩

def p5_92 : PointBox := ⟨⟨951833355899983307161553666712,951833355899983307161865703807⟩,⟨⟨433288894828649291617379815338,433288894828649291632630830548⟩,⟨1031047057097370444707016008652,1031047057097370444743645076642⟩⟩,⟨⟨(-1190550591924676543805914285127),(-1190550591924676543804860562884)⟩,⟨100318920132392230723724355565,100318920132392230724003155246⟩⟩,⟨⟨(-988572961971711339977018080684),(-988572961971711339962511537383)⟩,⟨(-150743155262444221121291031164),(-150743155262444221106974703969)⟩⟩,⟨⟨548785183958482342261772441348,548785183958482342265385171653⟩,⟨(-743668468480643252944729571766),(-743668468480643252940325567584)⟩⟩⟩

def p5_93 : PointBox := ⟨⟨950903597588158661848397699216,950903597588158661848716003591⟩,⟨⟨434009165817194003970078208351,434009165817194003985359602119⟩,⟨1031752192904513682547399556406,1031752192904513682584072754722⟩⟩,⟨⟨(-1191364812620815328616329805228),(-1191364812620815328615253331112)⟩,⟨101150617430643765788169170214,101150617430643765788454237191⟩⟩,⟨⟨(-988128436474232046237196418711),(-988128436474232046222662589908)⟩,⟨(-153630052499468877493180695033),(-153630052499468877478840871308)⟩⟩,⟨⟨547951458900383037166209799364,547951458900383037169846095736⟩,⟨(-743533412880707142380194035071),(-743533412880707142375764982716)⟩⟩⟩

def p5_94 : PointBox := ⟨⟨949968683320470569045114476737,949968683320470569045438832950⟩,⟨⟨434735136377542143232873264820,434735136377542143248185094858⟩,⟨1032461912744297292806865888367,1032461912744297292843582808526⟩⟩,⟨⟨(-1192184326501911899520967953192),(-1192184326501911899519869382229)⟩,⟨101988896027525249107267602712,101988896027525249107558775646⟩⟩,⟨⟨(-987672945127446288993708603205),(-987672945127446288979148458020)⟩,⟨(-156531637259936918609445510741),(-156531637259936918595083168949)⟩⟩,⟨⟨547112446245163856750443031477,547112446245163856754102355906⟩,⟨(-743396344615900433567069775242),(-743396344615900433562616326020)⟩⟩⟩

def p5_95 : PointBox := ⟨⟨949028753891568857635183286523,949028753891568857635513994031⟩,⟨⟨435466730131711052960783687141,435466730131711052976126408809⟩,⟨1033176120645334603673369430672,1033176120645334603710131171029⟩⟩,⟨⟨(-1193009022749754397575136874410),(-1193009022749754397574015117857)⟩,⟨102833667729338986962863873870,102833667729338986963161453634⟩⟩,⟨⟨(-987206421389249876791736484416),(-987206421389249876777148754478)⟩,⟨(-159447425717164851882467715927),(-159447425717164851868081626658)⟩⟩,⟨⟨546268263109337993858373697419,546268263109337993862057016484⟩,⟨(-743257259994341460092718072668),(-743257259994341460088239135160)⟩⟩⟩

def p5_96 : PointBox := ⟨⟨948083950851368188060310410503,948083950851368188060647142065⟩,⟨⟨436203869402967493521958801137,436203869402967493537332379453⟩,⟨1033894719700549152245997057821,1033894719700549152282802874017⟩⟩,⟨⟨(-1193838789465689458307856094915),(-1193838789465689458306712187930)⟩,⟨103684842842719288010557236318,103684842842719288010860960699⟩⟩,⟨⟨(-986728803715969188108025421594),(-986728803715969188093411566347)⟩,⟨(-162376931604376459133376524088),(-162376931604376459118968147670)⟩⟩,⟨⟨545419027700179331055255373015,545419027700179331058961819188⟩,⟨(-743116155973269477099768793247),(-743116155973269477095265399473)⟩⟩⟩

def p5_97 : PointBox := ⟨⟨947134416483731155834070984054,947134416483731155834414147456⟩,⟨⟨436946475207176601587552381871,436946475207176601602957353037⟩,⟨1034617612074930782607704691008,1034617612074930782644555997044⟩⟩,⟨⟨(-1194673513679578182342176234444),(-1194673513679578182341008716009)⟩,⟨104542330164643102145118566384,104542330164643102145428835874⟩⟩,⟨⟨(-986240035653558530984584887130),(-986240035653558530969943166009)⟩,⟨(-165319666325781088675750669969),(-165319666325781088661318310801)⟩⟩,⟨⟨544564859303607610420565045430,544564859303607610424295905755⟩,⟨(-742973030174991767351119332284),(-742973030174991767346590020360)⟩⟩⟩

def p5_98 : PointBox := ⟨⟨946180293785040865196204336473,946180293785040865196553681531⟩,⟨⟨437694467244448954399288176624,437694467244448954414724560136⟩,⟨1035344699013599143885590130207,1035344699013599143922486400921⟩⟩,⟨⟨(-1195513081359107060946586744566),(-1195513081359107060945396388870)⟩,⟨105406036972784881113200985773,105406036972784881113517607435⟩⟩,⟨⟨(-985740065925751722911310854163),(-985740065925751722896642394420)⟩,⟨(-168275139069009974557792552991),(-168275139069009974543337342215)⟩⟩,⟨⟨543705878271653730342308583502,543705878271653730346063214357⟩,⟨(-742827880902644306747406269792),(-742827880902644306742851811867)⟩⟩⟩

def p5_99 : PointBox := ⟨⟨945221726442666199799148887156,945221726442666199799504741770⟩,⟨⟨438447763891099321690016614184,438447763891099321705484880343⟩,⟨1036075880850178455843435425705,1036075880850178455880377837962⟩⟩,⟨⟨(-1196357377419458322373533552451),(-1196357377419458322372319164368)⟩,⟨106275869016231345026765571426,106275869016231345027088876130⟩⟩,⟨⟨(-985228848519098345051248055614),(-985228848519098345036551463321)⟩,⟨(-171242856918855353347136144384),(-171242856918855353332656727768)⟩⟩,⟨⟨542842206009502395676212361469,542842206009502395679991819406⟩,⟨(-742680707155753103880854890781),(-742680707155753103876274092379)⟩⟩⟩

def p5_100 : PointBox := ⟨⟨944258858813323033477845498646,944258858813323033478207511274⟩,⟨⟨439206282191930806270825865638,439206282191930806286325948060⟩,⟨1036811057015487264247942667522,1036811057015487264284930388423⟩⟩,⟨⟨(-1197206285733343997059187026462),(-1197206285733343997057949727510)⟩,⟨107151730506571975344959881785,107151730506571975345289584014⟩⟩,⟨⟨(-984706342764817327040005277124),(-984706342764817327025282126068)⟩,⟨(-174222324972255179167614353194),(-174222324972255179153112300023)⟩⟩,⟨⟨541973964962109641920628416167,541973964962109641924431756143⟩,⟨(-742531508645583229295436737068),(-742531508645583229290830717922)⟩⟩⟩

def p5_101 : PointBox := ⟨⟨943291835901334639824868466953,943291835901334639825237063329⟩,⟨⟨439969937852858185011788508001,439969937852858185027320950117⟩,⟨1037550126046546757007287934480,1037550126046546757044322427390⟩⟩,⟨⟨(-1198059689141407825118529979531),(-1198059689141407825117268235673)⟩,⟨108033524109381182733145967730,108033524109381182733482489491⟩⟩,⟨⟨(-984172513417402787251995708619),(-984172513417402787237244176470)⟩,⟨(-177213046454464324568766401983),(-177213046454464324554239935469)⟩⟩,⟨⟨541101278600393055544995356747,541101278600393055548823927035⟩,⟨(-742380285810262460394645334916),(-742380285810262460390012563840)⟩⟩⟩

def p5_102 : PointBox := ⟨⟨942320803336794574473243070550,942320803336794574473617963575⟩,⟨⟨440738645233884364849943504660,440738645233884364865508284611⟩,⟨1038292985595911054925008656552,1038292985595911054962089271030⟩⟩,⟨⟨(-1198917469462998948102096294602),(-1198917469462998948100811008529)⟩,⟨108921150936108217033986807888,108921150936108217034329921867⟩⟩,⟨⟨(-983627330729919386637592996007),(-983627330729919386622814378376)⟩,⟨(-180214522836351301361125426177),(-180214522836351301346575839817)⟩⟩,⟨⟨540224271406992821070091476465,540224271406992821073944519561⟩,⟨(-742227039829666387770803977640),(-742227039829666387766145356719)⟩⟩⟩

def p5_103 : PointBox := ⟨⟨941345907353635318676548926146,941345907353635318676930474126⟩,⟨⟨441512317342443963171637454397,441512317342443963187235058640⟩,⟨1039039532441322727878741065440,1039039532441322727915869063069⟩⟩,⟨⟨(-1199779507507321138725898373204),(-1199779507507321138724588235657)⟩,⟨109814510536390995951257537257,109814510536390995951607606579⟩⟩,⟨⟨(-983070770525926849918137735217),(-983070770525926849903330502852)⟩,⟨(-183226253952757744839884817049),(-183226253952757744825310622365)⟩⟩,⟨⟨539343068861602040689988771370,539343068861602040693867440427⟩,⟨(-742071772640051758496093710679),(-742071772640051758491407934923)⟩⟩⟩

def p5_104 : PointBox := ⟨⟨940367294767605986967921832910,940367294767605986968309612683⟩,⟨⟨442290865827128108047754489534,442290865827128108063384781290⟩,⟨1039789662495696618365839686391,1039789662495696618403014002957⟩⟩,⟨⟨(-1200645683084961127294627868483),(-1200645683084961127293294251636)⟩,⟨110713500890810128503028058046,110713500890810128503384729718⟩⟩,⟨⟨(-982502814267975763897159407553),(-982502814267975763882325456538)⟩,⟨(-186247738121856179818719877237),(-186247738121856179804122956807)⟩⟩,⟨⟨538457797425865093891098532388,538457797425865093895001662649⟩,⟨(-741914486948424771983105997844),(-741914486948424771978394438425)⟩⟩⟩

def p5_105 : PointBox := ⟨⟨939385112954162415374170531859,939385112954162415374565034023⟩,⟨⟨443074200971804630957757539662,443074200971804630973421106381⟩,⟨1040543270817434879709023741695,1040543270817434879746246029501⟩⟩,⟨⟨(-1201515875019799381871128851746),(-1201515875019799381869769986812)⟩,⟨111618018404099498394547246541,111618018404099498394911007424⟩⟩,⟨⟨(-981923449122619276622842767689),(-981923449122619276607979987353)⟩,⟨(-189278472265439930487958921193),(-189278472265439930473337213814)⟩⟩,⟨⟨537568584527843132389635765281,537568584527843132393564905952⟩,⟨(-741755186246630994754400391730),(-741755186246630994749661286976)⟩⟩⟩

def p5_106 : PointBox := ⟨⟨938399509826272959856402914524,938399509826272959856803813070⟩,⟨⟨443862231690147892427852072702,443862231690147892443548848061⟩,⟨1041300251621075955846920455097,1041300251621075955884189930163⟩⟩,⟨⟨(-1202389961161306490973716162947),(-1202389961161306490972333090092)⟩,⟨112527957898829850737602246241,112527957898829850737972831931⟩⟩,⟨⟨(-981332668021887890736961983663),(-981332668021887890722071847545)⟩,⟨(-192317952030077451085934419049),(-192317952030077451071289389603)⟩⟩,⟨⟨536675558546046139486553385122,536675558546046139490507656847⟩,⟨(-741593874825153522212630528319),(-741593874825153522207864918961)⟩⟩⟩

def p5_107 : PointBox := ⟨⟨937410633812143347342273215183,937410633812143347342680900619⟩,⟨⟨444654865520592539034277558834,444654865520592539050008046560⟩,⟨1042060498288280043617804269170,1042060498288280043655122283624⟩⟩,⟨⟨(-1203267818397228082789565276691),(-1203267818397228082788156565244)⟩,⟨113443212609581892545426593664,113443212609581892545804401688⟩⟩,⟨⟨(-980730469721177167093183106626),(-980730469721177167078263940915)⟩,⟨(-195365671909061843419333584672),(-195365671909061843404663601547)⟩⟩,⟨⟨535778848793031322324049450086,535778848793031322328030108856⟩,⟨(-741430557786605988625101107708),(-741430557786605988620307571240)⟩⟩⟩

def p5_108 : PointBox := ⟨⟨936418633832863933905356814974,936418633832863933905770835560⟩,⟨⟨445452008621725538088075402083,445452008621725538103839427521⟩,⟨1042823903379153386860895635668,1042823903379153386898261019335⟩⟩,⟨⟨(-1204149322666660993670236338995),(-1204149322666660993668803466500)⟩,⟨114363674177625472702368831454,114363674177625472702753479768⟩⟩,⟨⟨(-980116858853500828054973233323),(-980116858853500828040027068675)⟩,⟨(-198421125365084892973307400819),(-198421125365084892958614474660)⟩⟩,⟨⟨534878585498567950200567881318,534878585498567950204573667971⟩,⟨(-741265241058907011370925022262),(-741265241058907011366105036038)⟩⟩⟩

def p5_109 : PointBox := ⟨⟨935423659279982736332344591857,935423659279982736332765460014⟩,⟨⟨446253565768130873625491428762,446253565768130873641289589074⟩,⟨1043590358643913554598627426874,1043590358643913554636041893985⟩⟩,⟨⟨(-1205034348973523171129092551314),(-1205034348973523171127633660345)⟩,⟨115289232646121450186880799232,115289232646121450187272800818⟩⟩,⟨⟨(-979491845980064471135280068835),(-979491845980064471120304693208)⟩,⟨(-201483804953563600192237678488),(-201483804953563600177519648031)⟩⟩,⟨⟨533974899792369101726676040474,533974899792369101730708578910⟩,⟨(-741097931408122652378903571358),(-741097931408122652374055289330)⟩⟩⟩

def p5_110 : PointBox := ⟨⟨934425859993007614497016659716,934425859993007614497444008437⟩,⟨⟨447059440346701313681525590545,447059440346701313697357771667⟩,⟨1044359755034897653125842990952,1044359755034897653163305615304⟩⟩,⟨⟨(-1205922771400419562805656779168),(-1205922771400419562804173056866)⟩,⟨116219776455862889756617500998,116219776455862889757016551448⟩⟩,⟨⟨(-978855447637117870077279590731),(-978855447637117870062276665518)⟩,⟨(-204553202446545909850904722711),(-204553202446545909836163233578)⟩⟩,⟨⟨533067923686391137832441337912,533067923686391137836499618474⟩,⟨(-740928636450963488933801681538),(-740928636450963488928926292262)⟩⟩⟩

def p5_111 : PointBox := ⟨⟨933425386236840992629569409569,933425386236840992630003663455⟩,⟨⟨447869534353431673826865771984,447869534353431673842732496123⟩,⟨1045131982718915214128195187313,1045131982718915214165707417795⟩⟩,⟨⟨(-1206814463122906003026477748670),(-1206814463122906003024967635249)⟩,⟨117155192441572241628094195834,117155192441572241628500729364⟩⟩,⟨⟨(-978207686379046649279126238335),(-978207686379046649264093935466)⟩,⟨(-207628808957121151519682569142),(-207628808957121151504915837285)⟩⟩,⟨⟨532157790056702076102928980288,532157790056702076107014368435⟩,⟨(-740757364666922907961973523208),(-740757364666922907957069479264)⟩⟩⟩

def p5_112 : PointBox := ⟨⟨932422388679150517729278127749,932422388679150517729718744997⟩,⟨⟨448683748390708005205949964942,448683748390708005221850968124⟩,⟨1045906931089947288102777004574,1045906931089947288140337377493⟩⟩,⟨⟨(-1207709296424152862814848734848),(-1207709296424152862813314029264)⟩,⟨118095365828771165444791875624,118095365828771165445205422622⟩⟩,⟨⟨(-977548590817666965741067408275),(-977548590817666965726008165023)⟩,⟨(-210710115064259600080450315882),(-210710115064259600065660746882)⟩⟩,⟨⟨531244632624920404242950670623,531244632624920404247061625718⟩,⟨(-740584125410043272827070801136),(-740584125410043272822139900899)⟩⟩⟩

def p5_113 : PointBox := ⟨⟨931417018367679063016093867131,931417018367679063016541443011⟩,⟨⟨449501981665107126433714920299,449501981665107126449650858409⟩,⟨1046684488782193054489859297343,1046684488782193054527469772852⟩⟩,⟨⟨(-1208607142710009977633962746392),(-1208607142710009977632401289629)⟩,⟨119040180231239648573646562725,119040180231239648574067719771⟩⟩,⟨⟨(-976878195657689717495195276014),(-976878195657689717480106508543)⟩,⟨(-213796610938004549071115783846),(-213796610938004549056300850888)⟩⟩,⟨⟨530328585939226236261374729430,530328585939226236265513134195⟩,⟨(-740408928920296659864130755097),(-740408928920296659859170856280)⟩⟩⟩

def p5_114 : PointBox := ⟨⟨930409426707497493451202092874,930409426707497493451656217557⟩,⟨⟨450324131985720897301243561747,450324131985720897317214269814⟩,⟨1047464543683465037186852022083,1047464543683465037224511523683⟩⟩,⟨⟨(-1209507872524474109952574890566),(-1209507872524474109950988025546)⟩,⟨119989517649081044050784110568,119989517649081044051212530488⟩⟩,⟨⟨(-976196541728323715734240145522),(-976196541728323715719123711896)⟩,⟨(-216887786464939363195135927294),(-216887786464939363180297464985)⟩⟩,⟨⟨529409785354947083811772869346,529409785354947083815937575953⟩,⟨(-740231786334566923633910117508),(-740231786334566923628922564992)⟩⟩⟩

def p5_115 : PointBox := ⟨⟨929399765438203618976376617549,929399765438203618976837751364⟩,⟨⟨451150095763019597920118386583,451150095763019597936124406334⟩,⟨1048246982948933786655616450460,1048246982948933786693326529376⟩⟩,⟨⟨(-1210411355565559941074181452000),(-1210411355565559941072567482896)⟩,⟨120943258467409613867571990010,120943258467409613868008145802⟩⟩,⟨⟨(-975503676010990206492753277806),(-975503676010990206477607186982)⟩,⟨(-219983131373851141365015943659),(-219983131373851141350152007219)⟩⟩,⟨⟨528488367014720886608690893089,528488367014720886612883382490⟩,⟨(-740052709697219925454005530549),(-740052709697219925448988645316)⟩⟩⟩

def p5_116 : PointBox := ⟨⟨928388186611070769225910162083,928388186611070769226377741692⟩,⟨⟨451979768008268729320448315954,451979768008268729336489347832⟩,⟨1049031693015222657814243045470,1049031693015222657852002148022⟩⟩,⟨⟨(-1211317460701575318756978617960),(-1211317460701575318755339429644)⟩,⟨121901281455677108307178435792,121901281455677108307621833216⟩⟩,⟨⟨(-974799651663124103601133941926),(-974799651663124103585960736215)⟩,⟨(-223082135361511879755725403601),(-223082135361511879740838496840)⟩⟩,⟨⟨527564467828239319523464988280,527564467828239319527683641852⟩,⟨(-739871711970248849409407426690),(-739871711970248849404363093226)⟩⟩⟩

def p5_117 : PointBox := ⟨⟨927374842566149431051707954835,927374842566149431052182589967⟩,⟨⟨452813042333513490231993015435,452813042333513490248069718566⟩,⟨1049818559614853076496686692755,1049818559614853076534496820286⟩⟩,⟨⟨(-1212226055987801214171849334328),(-1212226055987801214170182702098)⟩,⟨122863463767654841275379320541,122863463767654841275830576608⟩⟩,⟨⟨(-974084528038040294528541470577),(-974084528038040294513338494331)⟩,⟨(-226184288218497376987041606089),(-226184288218497376972129131710)⟩⟩,⟨⟨526638225451574769403382700866,526638225451574769407629456101⟩,⟨(-739688807042981633998269613371),(-739688807042981633993195628464)⟩⟩⟩

def p5_118 : PointBox := ⟨⟨926359885909325397270714484903,926359885909325397271195720926⟩,⟨⟨453649810952145109451411122843,453649810952145109467523277972⟩,⟨1050607467791040446651413738491,1050607467791040446689273655536⟩⟩,⟨⟨(-1213137008683576563910434950783),(-1213137008683576563908742382902)⟩,⟨123829680942087634589921279433,123829680942087634590380001198⟩⟩,⟨⟨(-973358370700846401406198311994),(-973358370700846401390967629460)⟩,⟨(-229289079954963572052427931338),(-229289079954963572037491921865)⟩⟩,⟨⟨525709778266094751394570470008,525709778266094751398844032487⟩,⟨(-739504009741337666048010873462),(-739504009741337666042908747410)⟩⟩⟩

def p5_119 : PointBox := ⟨⟨925343469489337881593076679966,925343469489337881593565014744⟩,⟨⟨454489964680063123467989783562,454489964680063123484137953149⟩,⟨1051398301912840605826748269729,1051398301912840605864659636048⟩⟩,⟨⟨(-1214050185269787890288616861435),(-1214050185269787890286896518418)⟩,⟨124799806904035900580697762836,124799806904035900581164464363⟩⟩,⟨⟨(-972621251440386417688924061255),(-972621251440386417673663509008)⟩,⟨(-232396000926299551141863485650),(-232396000926299551126901826617)⟩⟩,⟨⟨524779265356967912111878436085,524779265356967912116180408769⟩,⟨(-739317335836621016745233997682),(-739317335836621016740101912609)⟩⟩⟩

def p5_120 : PointBox := ⟨⟨924325746374761060718409845238,924325746374761060718904618291⟩,⟨⟨455333392937447584529642603935,455333392937447584545826388681⟩,⟨1052190945690646488060025804551,1052190945690646488097986743569⟩⟩,⟨⟨(-1214965451466763306327689531123),(-1214965451466763306325943652234)⟩,⟨125773713966922011697676925220,125773713966922011698151014460⟩⟩,⟨⟨(-971873248277202693244856974884),(-971873248277202693229569536470)⟩,⟨(-235504541958576103095658031923),(-235504541958576103080673654694)⟩⟩,⟨⟨523846826491266144907368155896,523846826491266144911696609571⟩,⟨(-739128802053837647745165566809),(-739128802053837647740005759866)⟩⟩⟩

def p5_121 : PointBox := ⟨⟨923306869830952510095249554487,923306869830952510095751465099⟩,⟨⟨456179983751155064733289859942,456179983751155064749509983746⟩,⟨1052985282192034401264046593275,1052985282192034401302059376557⟩⟩,⟨⟨(-1215882672252570220783821380932),(-1215882672252570220782047410900)⟩,⟨126751272835296967724022540952,126751272835296967724504727291⟩⟩,⟨⟨(-971114445467506803806823588099),(-971114445467506803791506201575)⟩,⟨(-238614194473708445756415272123),(-238614194473708445741405181084)⟩⟩,⟨⟨522912602095667720251320410949,522912602095667720255677567159⟩,⟨(-738938426079524178529338455319),(-738938426079524178524148399209)⟩⟩⟩

def p5_122 : PointBox := ⟨⟨922286993296972004824483034176,922286993296972004824991581269⟩,⟨⟨457029623757752186681283032136,457029623757752186697539218282⟩,⟨1053781193857959070812435063523,1053781193857959070850498288847⟩⟩,⟨⟨(-1216801711881715763695126878138),(-1216801711881715763693326499121)⟩,⟨127732352608343215258257379090,127732352608343215258747221035⟩⟩,⟨⟨(-970344933503152911294474566056),(-970344933503152911279129509854)⟩,⟨(-241724450614251587686873175204),(-241724450614251587671839608240)⟩⟩,⟨⟨521976733233766711355416600036,521976733233766711359801010153⟩,⟨(-738746226569075984611451440550),(-738746226569075984606232819103)⟩⟩⟩

def p5_123 : PointBox := ⟨⟨921266270362474161650434869774,921266270362474161650950590212⟩,⟨⟨457882198207200260430815971498,457882198207200260447108804141⟩,⟨1054578562519296342499848974100,1054578562519296342537964415025⟩⟩,⟨⟨(-1217722433904248654396085025364),(-1217722433904248654394256247712)⟩,⟨128716820784129299983480359574,128716820784129299983978414270⟩⟩,⟨⟨(-969564809107610296127029705855),(-969564809107610296111654636124)⟩,⟨(-244834803367746732171288874992),(-244834803367746732156229540364)⟩⟩,⟨⟨521039361582994371127171293041,521039361582994371131584687721⟩,⟨(-738552223153562589978826539879),(-738552223153562589973577390129)⟩⟩⟩

def p5_124 : PointBox := ⟨⟨920244854744578401922737220773,920244854744578401923259428621⟩,⟨⟨458737590967204439560113333540,458737590967204439576442370992⟩,⟨1055377269413732176638489234121,1055377269413732176676654906791⟩⟩,⟨⟨(-1218644701185260932093447334512),(-1218644701185260932091592502510)⟩,⟨129704543264631839518489725777,129704543264631839518995370475⟩⟩,⟨⟨(-968774175227934817881866720604),(-968774175227934817866464744425)⟩,⟨(-247944746690537173542897586701),(-247944746690537173527815531399)⟩⟩,⟨⟨520100629411158490830544661946,520100629411158490834985017093⟩,⟨(-738356436446018526407703907351),(-738356436446018526402426570747)⟩⟩⟩

def p5_125 : PointBox := ⟨⟨919222900264719718827474182727,919222900264719718828003595303⟩,⟨⟨459595684528240625879431011632,459595684528240625895796983431⟩,⟨1056177195202996301003355024552,1056177195202996301041573254048⟩⟩,⟨⟨(-1219568375924787664200382409364),(-1219568375924787664198498887004)⟩,⟨130695384361540092993956440692,130695384361540092994470409756⟩⟩,⟨⟨(-967973141022742133097726730902),(-967973141022742133082294695875)⟩,⟨(-251053775630972279952361303152),(-251053775630972279937253443336)⟩⟩,⟨⟨519160679552607142915070781567,519160679552607142919540386494⟩,⟨(-738158888047198057091176844174),(-738158888047198057085868718076)⟩⟩⟩

def p5_126 : PointBox := ⟨⟨918200560825483735076915499758,918200560825483735077451567756⟩,⟨⟨460456360009273152335538827389,460456360009273152351941395983⟩,⟨1056978219990438623919581816706,1056978219990438623957851025707⟩⟩,⟨⟨(-1220493319678102439991182482222),(-1220493319678102439989272134790)⟩,⟨131689206802858172580512192109,131689206802858172581033992492⟩⟩,⟨⟨(-967161821846188565254899202554),(-967161821846188565239439610011)⟩,⟨(-254161386451918401829774968343),(-254161386451918401814643755394)⟩⟩,⟨⟨518219655384023579834117274376,518219655384023579838614518092⟩,⟨(-737959600550782402432922868123),(-737959600550782402427585818602)⟩⟩⟩

def p5_127 : PointBox := ⟨⟨917177990387429539612933928649,917177990387429539613477229557⟩,⟨⟨461319497164176056718222787024,461319497164176056734662559407⟩,⟨1057780223338946240269331202258,1057780223338946240307653284003⟩⟩,⟨⟨(-1221419393376406147083581379440),(-1221419393376406147081642059954)⟩,⟨132685871740319691694728080002,132685871740319691695258314136⟩⟩,⟨⟨(-966340339227968578576010267764),(-966340339227968578560520584530)⟩,⟨(-257267076752495891459636630114),(-257267076752495891444479586635)⟩⟩,⟨⟨517277700799859426765511541419,517277700799859426770038288444⟩,⟨(-737758597548028361930177896676),(-737758597548028361924809808872)⟩⟩⟩

def p5_128 : PointBox := ⟨⟨916155342945903793719656577457,916155342945903793720206302198⟩,⟨⟨462184974388870524614324398342,462184974388870524630800806133⟩,⟨1058583084289198592866026825753,1058583084289198592904399384616⟩⟩,⟨⟨(-1222346457347906216105767396526),(-1222346457347906216103801905521)⟩,⟨133685238757629374220795011290,133685238757629374221332929262⟩⟩,⟨⟨(-965508820849340850877855540773),(-965508820849340850862339434821)⟩,⟨(-260370345588961866092946716375),(-260370345588961866077767432637)⟩⟩,⟨⟨516334960187413668434242171144,516334960187413668438795998079⟩,⟨(-737555903631847497814204925257),(-737555903631847497808808592863)⟩⟩⟩

def p5_129 : PointBox := ⟨⟨915132772507849598255675024099,915132772507849598256232005378⟩,⟨⟨463052668729190828422527734057,463052668729190828439041594137⟩,⟨1059386681378258079791554819577,1059386681378258079829980535144⟩⟩,⟨⟨(-1223274371339283204997465676590),(-1223274371339283204995470949397)⟩,⟨134687165879545858525756681197,134687165879545858526303137571⟩⟩,⟨⟨(-964667400515197967882586583363),(-964667400515197967867040375521)⟩,⟨(-263470693594658894518484960936),(-263470693594658894503279838078)⟩⟩,⟨⟨515391578401565288172829825085,515391578401565288177413390437⟩,⟨(-737351544400305333531406358896),(-737351544400305333525978758945)⟩⟩⟩

def p5_130 : PointBox := ⟨⟨914110433068613614505116399127,914110433068613614505680038084⟩,⟨⟨463922455889490819911046920564,463922455889490819927597831511⟩,⟨1060190892658493125217701280517,1060190892658493125256178393374⟩⟩,⟨⟨(-1224202994537541279075218971239),(-1224202994537541279073197064020)⟩,⟨135691509581819619049428338037,135691509581819619049982785582⟩⟩,⟨⟨(-963816218122197768803044417202),(-963816218122197768787470838225)⟩,⟨(-266567623098950434507135624673),(-266567623098950434491907333566)⟩⟩,⟨⟨514447700739167770393874424731,514447700739167770398485948272⟩,⟨(-737145546459530323204155889234),(-737145546459530323198699077233)⟩⟩⟩

def p5_131 : PointBox := ⟨⟨913088478588754931409853413642,913088478588754931410424329557⟩,⟨⟨464794210242002746558696181039,464794210242002746575284773483⟩,⟨1060995595716830457244567369174,1060995595716830457283097896797⟩⟩,⟨⟨(-1225132185592238826617452961692),(-1225132185592238826615401564538)⟩,⟨136698124801999596572022898889,136698124801999596572585987104⟩⟩,⟨⟨(-962955419622977357319128214596),(-962955419622977357303524535274)⟩,⟨(-269660638245064595377605664477),(-269660638245064595362351535834)⟩⟩,⟨⟨513503472913114025242915331331,513503472913114025247556816339⟩,⟨(-736937937426022666854380655812),(-736937937426022666848892359718)⟩⟩⟩

def p5_132 : PointBox := ⟨⟨912067062970859171682155897433,912067062970859171682733271600⟩,⟨⟨465667804836959856574517389649,465667804836959856591143062453⟩,⟨1061800667694333061702300338683,1061800667694333061740881821495⟩⟩,⟨⟨(-1226061802638095132659680174175),(-1226061802638095132657602141910)⟩,⟨137706864951121775680115400429,137706864951121775680686361572⟩⟩,⟨⟨(-962085156986473749960509113034),(-962085156986473749944879055038)⟩,⟨(-272749245106768645305234929974),(-272749245106768645289958600649)⟩⟩,⟨⟨512559041026080635799990485910,512559041026080635804659457812⟩,⟨(-736728745928353380326334221358),(-736728745928353380320817287870)⟩⟩⟩

def p5_133 : PointBox := ⟨⟨911046340036361328508107821098,911046340036361328508692487944⟩,⟨⟨466543111413493933868648415995,466543111413493933885311977460⟩,⟨1062605985306100006001337451209,1062605985306100006039972573643⟩⟩,⟨⟨(-1226991703317968716308049540606),(-1226991703317968716305941783346)⟩,⟨138717581926292574264511397392,138717581926292574265091096328⟩⟩,⟨⟨(-961205588154378062147554456534),(-961205588154378062131894320413)⟩,⟨(-275832951803797625954538312355),(-275832951803797625939236164562)⟩⟩,⟨⟨511614551543960663257259962594,511614551543960663261959099570⟩,⟨(-736518001608244378404609982449),(-736518001608244378399061368872)⟩⟩⟩

def p5_134 : PointBox := ⟨⟨910026463502380823237341474926,910026463502380823237932784438⟩,⟨⟨467420000411318562194610949068,467420000411318562211311930594⟩,⟨1063411424861484052311110074349,1063411424861484052349796886967⟩⟩,⟨⟨(-1227921744806202619561517069632),(-1227921744806202619559381843273)⟩,⟨139730126124179514915373717225,139730126124179514915961549567⟩⟩,⟨⟨(-960316876993753027503980477295),(-960316876993753027488293231034)⟩,⟨(-278911268615961476457911020060),(-278911268615961476442585951428)⟩⟩,⟨⟨510670151268994573472344142906,510670151268994573477071487715⟩,⟨(-736305735121020694459697338162),(-736305735121020694454119297656)⟩⟩⟩

def p5_135 : PointBox := ⟨⟨909007586958572272614181307061,909007586958572272614779921765⟩,⟨⟨468298340983208557069187525326,468298340983208557085926582257⟩,⟨1064216862284622704934326037342,1064216862284622704973066687398⟩⟩,⟨⟨(-1228851783832331618768440973494),(-1228851783832331618766275798517)⟩,⟨140744346455421231678771680952,140744346455421231679368345360⟩⟩,⟨⟨(-959419193245846505380862505663),(-959419193245846505365145215925)⟩,⟨(-281983708095856203438931868658),(-281983708095856203423581010445)⟩⟩,⟨⟨509725987312609168639678204150,509725987312609168644435904612⟩,⟨(-736091978135426339911437588055),(-736091978135426339905827685076)⟩⟩⟩

def p5_136 : PointBox := ⟨⟨907989863843995451739514747523,907989863843995451740119722406⟩,⟨⟨469178001008285624791618190397,469178001008285624808394586629⟩,⟨1065022173135278063066603339598,1065022173135278063105394936187⟩⟩,⟨⟨(-1229781676705146013827854412791),(-1229781676705146013825662622249)⟩,⟨141760090359968427678870647253,141760090359968427679475240974⟩⟩,⟨⟨(-958512712471136451717823975671),(-958512712471136451702080942777)⟩,⟨(-285049785180105862294979626367),(-285049785180105862279607174596)⟩⟩,⟨⟨508782207067974719997064250617,508782207067974720001849413393⟩,⟨(-735876763332795701698934265830),(-735876763332795701693295819276)⟩⟩⟩

def p5_137 : PointBox := ⟨⟨906973447424007936061877101207,906973447424007936062489388697⟩,⟨⟨470058847106119909843200767176,470058847106119909860015401940⟩,⟨1065827232629980577537270960289,1065827232629980577576116556316⟩⟩,⟨⟨(-1230711279337106335481451348812),(-1230711279337106335479229407477)⟩,⟨142777203823366939492230976450,142777203823366939492844490380⟩⟩,⟨⟨(-957597615990645606372456696358),(-957597615990645606356683676896)⟩,⟨(-288109017299063435775313203648),(-288109017299063435759915010141)⟩⟩,⟨⟨507838958182290800958398634615,507838958182290800963214321774⟩,⟨(-735660124405572785576494258160),(-735660124405572785570823789761)⟩⟩⟩

def p5_138 : PointBox := ⟨⟨905958490767183902280883921429,905958490767183902281502819325⟩,⟨⟨470940744651656675090110869877,470940744651656675106963204534⟩,⟨1066631915663471538969951848712,1066631915663471539008849298481⟩⟩,⟨⟨(-1231640447269102997936776902332),(-1231640447269102997934527272772)⟩,⟨143795531393993582814219216124,143795531393993582814840986239⟩⟩,⟨⟨(-956674090823566882899148477051),(-956674090823566882883348681415)⟩,⟨(-291160924484900107342109898783),(-291160924484900107326689092625)⟩⟩,⟨⟨506896388528811614310175741653,506896388528811614315019812789⟩,⟨(-735442096055171037184564637948),(-735442096055171037178864604845)⟩⟩⟩

def p5_139 : PointBox := ⟨⟨904945146722262564106681907637,904945146722262564107308122606⟩,⟨⟨471823557790976923499853412608,471823557790976923516744127869⟩,⟨1067436096830438855438134708741,1067436096830438855477086293178⟩⟩,⟨⟨(-1232569035695554613028231779083),(-1232569035695554613025951807444)⟩,⟨144814916201254950840186381414,144814916201254950840817157106⟩⟩,⟨⟨(-955742329621243131553132670592),(-955742329621243131537302955836)⟩,⟨(-294205029478013927072511750703),(-294205029478013927057065258714)⟩⟩,⟨⟨505954646178621891609963080587,505954646178621891614837832252⟩,⟨(-735222713989166911212110529350),(-735222713989166911206378328042)⟩⟩⟩

def p5_140 : PointBox := ⟨⟨903933567895129714356215850433,903933567895129714356848421678⟩,⟨⟨472707149457900315504793016435,472707149457900315521721334560⟩,⟨1068239650447540410482660751627,1068239650447540410521663491505⟩⟩,⟨⟨(-1233496899489838373576760929272),(-1233496899489838373574454030560)⟩,⟨145835199974758811883802739420,145835199974758811884441591492⟩⟩,⟨⟨(-954802530597547580211302684483),(-954802530597547580195447432704)⟩,⟨(-297240857831690455004819088203),(-297240857831690454989351179907)⟩⟩,⟨⟨505013879372174717170461838604,505013879372174717175364302194⟩,⟨(-735002014917820811284921687307),(-735002014917820811279160716043)⟩⟩⟩

def p5_141 : PointBox := ⟨⟨902923906625835839881390604117,902923906625835839882030491917⟩,⟨⟨473591381391438262720822206978,473591381391438262737789023299⟩,⟨1069042450575709027668594302429,1069042450575709027707651275986⟩⟩,⟨⟨(-1234423893230045607972226414112),(-1234423893230045607969889003746)⟩,⟨146856223064467206090387510101,146856223064467206091035446786⟩⟩,⟨⟨(-953854897455713838198365359704),(-953854897455713838182480277357)⟩,⟨(-300267938014949638778204760379),(-300267938014949638762711240036)⟩⟩,⟨⟨504074236490602892503519163628,504074236490602892508452441790⟩,⟨(-734780036549919489169689770915),(-734780036549919489163896508237)⟩⟩⟩

def p5_142 : PointBox := ⟨⟨901916314965654270316499235698,901916314965654270317145684386⟩,⟨⟨474476114154104586499271871249,474476114154104586516276574022⟩,⟨1069844371042732806055018273167,1069844371042732806094127131477⟩⟩,⟨⟨(-1235349871225055305697138018403),(-1235349871225055305694772773504)⟩,⟨147877824461839772724878516961,147877824461839772725534811842⟩⟩,⟨⟨(-952899639311666872031840848580),(-952899639311666872015929394755)⟩,⟨(-303285801513514936962435010775),(-303285801513514936946919244728)⟩⟩,⟨⟨503135866026815709347264609191,503135866026815709352226371518⟩,⟨(-734556817587934471135995509762),(-734556817587934471130172623922)⟩⟩⟩

def p5_143 : PointBox := ⟨⟨900910944654182815603315238952,900910944654182815603969000487⟩,⟨⟨475361207151090618827633105084,475361207151090618844676401296⟩,⟨1070645285466104332400595914031,1070645285466104332439759076438⟩⟩,⟨⟨(-1236274687540918114961982203902),(-1236274687540918114959586290609)⟩,⟨148899841821975249505372175201,148899841821975249506037630226⟩⟩,⟨⟨(-951936970613908827291605659136),(-951936970613908827275664474584)⟩,⟨(-306293982928842534300680304091),(-306293982928842534285139008556)⟩⟩,⟨⟨502198916556393239931252648979,502198916556393239936245345659⟩,⟨(-734332397722491571501781385635),(-734332397722491571495926099881)⟩⟩⟩

def p5_144 : PointBox := ⟨⟨899907947096492340703024511573,899907947096492340703684467610⟩,⟨⟨476246518650311093500762860404,476246518650311093517843804118⟩,⟨1071445067276132020999579209855,1071445067276132021038793156749⟩⟩,⟨⟨(-1237198196027543019256502711150),(-1237198196027543019254080148260)⟩,⟨149922111486758473930806537602,149922111486758473931480051756⟩⟩,⟨⟨(-950967111060015974713579586675),(-950967111060015974697613776827)⟩,⟨(-309292020075150407754301182955),(-309292020075150407738739326277)⟩⟩,⟨⟨501263536708290481488658391228,501263536708290481493678525628⟩,⟨(-734106817626147058109928484413),(-734106817626147058104044791250)⟩⟩⟩

def p5_145 : PointBox := ⟨⟨898907473340325718835577561159,898907473340325718836244820838⟩,⟨⟨477131905803326627389767756860,477131905803326627406887363073⟩,⟨1072243589739306581106137339582,1072243589739306581145405621701⟩⟩,⟨⟨(-1238120250345678609864621259904),(-1238120250345678609862167896992)⟩,⟨150944468509019583666371237497,150944468509019583667053979775⟩⟩,⟨⟨(-949990285509805398838366184561),(-949990285509805398822370767110)⟩,⟨(-312279454074388990190548193851),(-312279454074388990174960910178)⟩⟩,⟨⟨500329875135363907755311441210,500329875135363907760362604691⟩,⟨(-733880118946466551326797944059),(-733880118946466551320881768674)⟩⟩⟩

def p5_146 : PointBox := ⟨⟨897909674053350597000250150192,897909674053350597000923903804⟩,⟨⟨478017224667148025202094042323,478017224667148025219251623739⟩,⟨1073040725981915365328377737980,1073040725981915365367697798400⟩⟩,⟨⟨(-1239040703994180586668458644298),(-1239040703994180586665977378402)⟩,⟨151966746677711458988968643010,151966746677711458989659822522⟩⟩,⟨⟨(-949006723895232321852753791416),(-949006723895232321836732477159)⟩,⟨(-315255829449097239129351082680),(-315255829449097239113741978248)⟩⟩,⟨⟨499398080484733182873957966566,499398080484733182879037633992⟩,⟨(-733652344298403266674521500666),(-733652344298403266668575727128)⟩⟩⟩

def p5_147 : PointBox := ⟨⟨896914699500469399427238261705,896914699500469399427919306957⟩,⟨⟨478902330226927056545735863430,478902330226927056562932153666⟩,⟨1073836349013897110524124445951,1073836349013897110563498845070⟩⟩,⟨⟨(-1239959410337556840303615720992),(-1239959410337556840301103535096)⟩,⟨152988778544110775279498719484,152988778544110775280199191867⟩⟩,⟨⟨(-948016661127081161492211333150),(-948016661127081161476160543061)⟩,⟨(-318220694213090048397258997543),(-318220694213090048381624574950)⟩⟩,⟨⟨498468301367990982336866840832,498468301367990982341977618850⟩,⟨(-733423537255972750939846515740),(-733423537255972750933868191142)⟩⟩⟩

def p5_148 : PointBox := ⟨⟨895922699521189985990322524036,895922699521189985991009750132⟩,⟨⟨479787076419537751606985748743,479787076419537751624219777266⟩,⟨1074630331752929345973897355637,1074630331752929346013322554530⟩⟩,⟨⟨(-1240876222633781195344647413584),(-1240876222633781195342108328470)⟩,⟨154010395449047337837637829458,154010395449047337838346488414⟩⟩,⟨⟨(-947020336998515557983075507350),(-947020336998515557967000323165)⟩,⟨(-321173599959925137957934311602),(-321173599959925137942279509444)⟩⟩,⟨⟨497540686331274040958613592101,497540686331274040963751978261⟩,⟨(-733193742343221812050607071322),(-733193742343221812044600187336)⟩⟩⟩

def p5_149 : PointBox := ⟨⟨894933823507060373476193194972,894933823507060373476887695447⟩,⟨⟨480671316158051641580820247441,480671316158051641598093004304⟩,⟨1075422547048740512304360574059,1075422547048740512343840076059⟩⟩,⟨⟨(-1241790994062366627115137053639),(-1241790994062366627112566953313)⟩,⟨155031427551165655183766653578,155031427551165655184484662580⟩⟩,⟨⟨(-946017996085554669066539131621),(-946017996085554669050434624882)⟩,⟨(-324114101949099818638662242376),(-324114101949099818622982249195)⟩⟩,⟨⟨496615383825208709000709103768,496615383825208709005878657303⟩,⟨(-732963005024489903660570684169),(-732963005024489903654531206008)⟩⟩⟩

def p5_150 : PointBox := ⟨⟨893948220379170917958426213579,893948220379170917959127123679⟩,⟨⟨481554901357109732444744775602,481554901357109732462055495167⟩,⟨1076212867707638609146526307406,1076212867707638609186057341513⟩⟩,⟨⟨(-1242703577752688504344308821852),(-1242703577752688504341710830201)⟩,⟨156051703856221970835373084765,156051703856221970836099585911⟩⟩,⟨⟨(-945009887644545022351353031159),(-945009887644545022335223169401)⟩,⟨(-327041759189930350899832400293),(-327041759189930350884131066836)⟩⟩,⟨⟨495692542174744444119758071499,495692542174744444124956066585⟩,⟨(-732731371693961795694517964649),(-732731371693961795688448998316)⟩⟩⟩

def p5_151 : PointBox := ⟨⟨892966038565727346364675317744,892966038565727346365383481821⟩,⟨⟨482437682959193346062503567411,482437682959193346079853010720⟩,⟨1077001166517247970190559260614,1077001166517247970230144532362⟩⟩,⟨⟨(-1243613826812548156640605772914),(-1243613826812548156637976684981)⟩,⟨157071052247419217673181879336,157071052247419217673917783544⟩⟩,⟨⟨(-943996265506699128897788276898),(-943996265506699128881629255887)⟩,⟨(-329956134523068997064874222059),(-329956134523068997049147832385)⟩⟩,⟨⟨494772309548888798451607465495,494772309548888798456836669414⟩,⟨(-732498889664510941516250230922),(-732498889664510941510148642926)⟩⟩⟩

def p5_152 : PointBox := ⟨⟨891987425979698014656049047501,891987425979698014656763196090⟩,⟨⟨483319510961795291298985913315,483319510961795291316372934549⟩,⟨1077787316271445551491776828737,1077787316271445551531412244393⟩⟩,⟨⟨(-1244521594356966820023780746956),(-1244521594356966820021125203817)⟩,⟨158089299516781583855931658210,158089299516781583856675680548⟩⟩,⟨⟨(-942977387969773899472424779617),(-942977387969773899456242413043)⟩,⟨(-332856794699616301327412177049),(-332856794699616301311666375511)⟩⟩,⟨⟨493854833930357576570188446452,493854833930357576575444814249⟩,⟨(-732265607155833540308320954235),(-732265607155833540302191344409)⟩⟩⟩

def p5_153 : PointBox := ⟨⟨891012529996538758859355344251,891012529996538758860076720670⟩,⟨⟨484200234445492140211014246462,484200234445492140228439958443⟩,⟨1078571189795487912931895031646,1078571189795487912971584577522⟩⟩,⟨⟨(-1245426733537199775946073878670),(-1245426733537199775943387186277)⟩,⟨159106271397569585251408954628,159106271397569585252162424254⟩⟩,⟨⟨(-941953517686963663887810638565),(-941953517686963663871599299508)⟩,⟨(-335743310457788618094009814514),(-335743310457788618078239111756)⟩⟩,⟨⟨492940263085153940989766628597,492940263085153940995054219122⟩,⟨(-732031573281873889089005840491),(-732031573281873889082843610152)⟩⟩⟩

def p5_154 : PointBox := ⟨⟨890041497431998693507730697966,890041497431998693508458382239⟩,⟨⟨485079701602917680873883526346,485079701602917680891347083100⟩,⟨1079352659971319873980849651451,1079352659971319874020590339137⟩⟩,⟨⟨(-1246329097569960269726008046044),(-1246329097569960269723293558985)⟩,⟨160121792597735727013959087418,160121792597735727014721077738⟩⟩,⟨⟨(-940924921553084272934179580540),(-940924921553084272917943494340)⟩,⟨(-338615256597103443449575007432),(-338615256597103443433783499487)⟩⟩,⟨⟨492028744532090327057597482346,492028744532090327062913365720⟩,⟨(-731796838037542221913546825946),(-731796838037542221907355306192)⟩⟩⟩

def p5_155 : PointBox := ⟨⟨889074474520010299854754142421,889074474520010299855489025619⟩,⟨⟨485957759768636899468004010410,485957759768636899485506200505⟩,⟨1080131599763055633663849996259,1080131599763055633703644677894⟩⟩,⟨⟨(-1247228539766842573492884328918),(-1247228539766842573490138652604)⟩,⟨161135686834420006783464685366,161135686834420006784236163300⟩⟩,⟨⟨(-939891870588126360432506996588),(-939891870588126360416242132184)⟩,⟨(-341472212050047683332259869549),(-341472212050047683316443620753)⟩⟩,⟨⟨491120425512267098280552925524,491120425512267098285900031243⟩,⟨(-731561452284726843568800987612),(-731561452284726843562576862890)⟩⟩⟩

def p5_156 : PointBox := ⟨⟨888111606890667133533451678773,888111606890667133534192493528⟩,⟨⟨486834255449919110375939543611,486834255449919110393479188784⟩,⟨1080907882242622961233846404524,1080907882242622961273690945670⟩⟩,⟨⟨(-1248124913563933346962550807244),(-1248124913563933346959778609425)⟩,⟨162147776869483664576010549018,162147776869483664576790216523⟩⟩,⟨⟨(-938854639818257358827559280660),(-938854639818257358811271452281)⟩,⟨(-344313759951196611902083282043),(-344313759951196611886247930426)⟩⟩,⟨⟨490215452958521926142271640787,490215452958521926147645896820⟩,⟨(-731325467737602980809490461844),(-731325467737602980803238354389)⟩⟩⟩

def p5_157 : PointBox := ⟨⟨887153039548292468136396741392,887153039548292468137144720649⟩,⟨⟨487709034358408104753972510154,487709034358408104771550702342⟩,⟨1081681380615560888788768397615,1081681380615560888828666754792⟩⟩,⟨⟨(-1249018072551600246991502119858),(-1249018072551600246988698720577)⟩,⟨163157884546078720390020584221,163157884546078720390809770827⟩⟩,⟨⟨(-937813508154353294566180884256),(-937813508154353294549864493808)⟩,⟨(-347139487703753931059963126705),(-347139487703753931044103213340)⟩⟩,⟨⟨489313973464863915122133624698,489313973464863915127539075470⟩,⟨(-731088936947241395220293020073),(-731088936947241395214008351353)⟩⟩⟩

def p5_158 : PointBox := ⟨⟨886198916849602177498530957329,886198916849602177499285125322⟩,⟨⟨488581941442686425905302096841,488581941442686425922917907465⟩,⟨1082451968246961170253397920130,1082451968246961170293346883021⟩⟩,⟨⟨(-1249907870504446544229556737080),(-1249907870504446544226725726856)⟩,⟨164165830826249960511620038825,164165830826249960512417747178⟩⟩,⟨⟨(-936768758268142738469705140461),(-936768758268142738453364673909)⟩,⟨(-349948987043486033553090269400),(-349948987043486033537210138152)⟩⟩,⟨⟨488416133255906513779006764108,488416133255906513784440271265⟩,⟨(-730851913285520427423694446128),(-730851913285520427417380776747)⟩⟩⟩

def p5_159 : PointBox := ⟨⟨885249382481965145272292077873,885249382481965145273053372872⟩,⟨⟨489452820921730104389577332455,489452820921730104407231578133⟩,⟨1083219518687543613052859074599,1083219518687543613092861644774⟩⟩,⟨⟨(-1250794161411420322641686173696),(-1250794161411420322638823965132)⟩,⟨165171435829565138156948551632,165171435829565138157755805782⟩⟩,⟨⟨(-935720676466046550742842905171),(-935720676466046550726474101344)⟩,⟨(-352741854100026293982964147898),(-352741854100026293967059640529)⟩⟩,⟨⟨487522078156313256295156429999,487522078156313256300621088056⟩,⟨(-730614450928345771877271424735),(-730614450928345771870925254191)⟩⟩⟩

def p5_160 : PointBox := ⟨⟨884304579441764475697420307174,884304579441764475698187259503⟩,⟨⟨490321516319249397785783225288,490321516319249397803474506510⟩,⟨1083983905699855239712244730889,1083983905699855239752296066465⟩⟩,⟨⟨(-1251676799506066665512157169435),(-1251676799506066665509269226917)⟩,⟨166174518872768244164706545888,166174518872768244165521817186⟩⟩,⟨⟨(-934669552560798239628154770826),(-934669552560798239611764378605)⟩,⟨(-355517689455527960674423368210),(-355517689455527960658501024129)⟩⟩,⟨⟨486631953560270365704068133888,486631953560270365709559175208⟩,⟨(-730376604838182914189209035073),(-730376604838182914182835764652)⟩⟩⟩

def p5_161 : PointBox := ⟨⟨883364650012862764287489700135,883364650012862764288263735817⟩,⟨⟨491187870498910280046552035199,491187870498910280064281608887⟩,⟨1084745003284583096784564802675,1084745003284583096824669491659⟩⟩,⟨⟨(-1252555639296911070079940115288),(-1252555639296911070077021009461)⟩,⟨167174898510449779716097531452,167174898510449779716922364914⟩⟩,⟨⟨(-933615679740930846611927980445),(-933615679740930846595509500412)⟩,⟨(-358276098200646993102682623945),(-358276098200646993086736110794)⟩⟩,⟨⟨485745904401000220095348128374,485745904401000220100870246051⟩,⟨(-730138430745907797988849502123),(-730138430745907797982443822415)⟩⟩⟩

def p5_162 : PointBox := ⟨⟨882429735745174671484207453754,882429735745174671484987541691⟩,⟨⟨492051725700430614139934779841,492051725700430614157701633585⟩,⟨1085502685706970398183614103398,1085502685706970398223768712573⟩⟩,⟨⟨(-1253430535597962182467034946278),(-1253430535597962182464088504877)⟩,⟨168172392576727026317712072966,168172392576727026318545399522⟩⟩,⟨⟨(-932559354438217279240972577199),(-932559354438217279224530754051)⟩,⟨(-361016689987838980723739855081),(-361016689987838980707773762524)⟩⟩,⟨⟨484864075120329636377893254003,484864075120329636383443100172⟩,⟨(-729899985131981925168673460638),(-729899985131981925162239162324)⟩⟩⟩

def p5_163 : PointBox := ⟨⟨881499977433350026171052104563,881499977433350026171839229691⟩,⟨⟨492912923576544119900993225432,492912923576544119918798203540⟩,⟨1086256827523325569410389926973,1086256827523325569450597606843⟩⟩,⟨⟨(-1254301343559321805318671926420),(-1254301343559321805315694369933)⟩,⟨169166818227926359380394407093,169166818227926359381237307956⟩⟩,⟨⟨(-931500876193151934879949788496),(-931500876193151934863480132320)⟩,⟨(-363739079081957085911020171263),(-363739079081957085895030120177)⟩⟩,⟨⟨483986609638326862697725782568,483986609638326862703306616267⟩,⟨(-729661325206958731004774801699),(-729661325206958730998308200179)⟩⟩⟩

def p5_164 : PointBox := ⟨⟨880575515095570669292471375430,880575515095570669293264109295⟩,⟨⟨493771305230824417475113230525,493771305230824417492954934415⟩,⟨1087007303607613648527624736103,1087007303607613648567880728174⟩⟩,⟨⟨(-1255167918697890002824829498600),(-1255167918697890002821826175030)⟩,⟨170157991986258691546916559365,170157991986258691547767532243⟩⟩,⟨⟨(-930440547518562295113628633726),(-930440547518562295097137714135)⟩,⟨(-366442884408140772556963965732),(-366442884408140772540956314487)⟩⟩,⟨⟨483113651323021090391198213583,483113651323021090396805364661⟩,⟨(-729422508891328713493837673093),(-729422508891328713487344050253)⟩⟩⟩

def p5_165 : PointBox := ⟨⟨879656487952464230695980643111,879656487952464230696780362246⟩,⟨⟨494626711256360586224877515538,494626711256360586242757144954⟩,⟨1087753989178119399255771955710,1087753989178119399296080691870⟩⟩,⟨⟨(-1256030116928153011767072431716),(-1256030116928153011764038071948)⟩,⟨171145729784478161383862787928,171145729784478161384723337187⟩⟩,⟨⟨(-929378673761439921096795943460),(-929378673761439921080277467788)⟩,⟨(-369127729596987909039955099103),(-369127729596987909023923719039)⟩⟩,⟨⟨482245342960218199481282780702,482245342960218199486920800964⟩,⟨(-729183594794711433438503474596),(-729183594794711433431977685050)⟩⟩⟩

def p5_166 : PointBox := ⟨⟨878743034406138014704827723745,878743034406138014705633341475⟩,⟨⟨495478981775274830322170468487,495478981775274830340086925442⟩,⟨1088496759824171401418297279307,1088496759824171401458655100315⟩⟩,⟨⟨(-1256887794593041563143385804248),(-1256887794593041563140324477002)⟩,⟨172129847011513203116324226357,172129847011513203117193209575⟩⟩,⟨⟨(-928315562963080945221639193289),(-928315562963080945205098166210)⟩,⟨(-371793243027005665973378190303),(-371793243027005665957327917954)⟩⟩,⟨⟨481381826723426338301933386463,481381826723426338307598715425⟩,⟨(-728944642194403137584928810772),(-728944642194403137578374878249)⟩⟩⟩

def p5_167 : PointBox := ⟨⟨877835292019336151840917068589,877835292019336151841729616689⟩,⟨⟨496327956479071986317502793727,496327956479071986335456950560⟩,⟨1089235491532916304318541210328,1089235491532916304358951417438⟩⟩,⟨⟨(-1257740808494847126957178009088),(-1257740808494847126954085740845)⟩,⟨173110158559058144741535740305,173110158559058144742414296607⟩⟩,⟨⟨(-927251525717626734381079131672),(-927251525717626734364510832788)⟩,⟨(-374439057864338461743403824319),(-374439057864338461727330058311)⟩⟩,⟨⟨480523244143904808002711482524,480523244143904808008407545467⟩,⟨(-728705711013289390677529653541),(-728705711013289390670943707693)⟩⟩⟩

def p5_168 : PointBox := ⟨⟨876933397494723155554297645643,876933397494723155555115502212⟩,⟨⟨497173474669809745660833249395,497173474669809745678823488530⟩,⟨1089970060716132359631508645878,1089970060716132359671965791176⟩⟩,⟨⟨(-1258589015926183513083244434958),(-1258589015926183513080127349937)⟩,⟨174086478869112486138862373774,174086478869112486139748773600⟩⟩,⟨⟨(-926186875029095895352420176649),(-926186875029095895335832072885)⟩,⟨(-377064812099774038616813582236),(-377064812099774038600723544722)⟩⟩,⟨⟨479669736080849576616895449248,479669736080849576622616898327⟩,⟨(-728466861797132732852885003028),(-728466861797132732846273081947)⟩⟩⟩

def p5_169 : PointBox := ⟨⟨876037486654297003779350396985,876037486654297003780175122708⟩,⟨⟨498015375302077597363424505597,498015375302077597381452186802⟩,⟨1090700344237071292168431760771,1090700344237071292208940887331⟩⟩,⟨⟨(-1259432274700981193890754877059),(-1259432274700981193887606980588)⟩,⟨175058621982454006762036038825,175058621982454006762931997004⟩⟩,⟨⟨(-925121926166999204028108572288),(-925121926166999204011493505640)⟩,⟨(-379670148583031575492435895345),(-379670148583031575476322620907)⟩⟩,⟨⟨478821442691728585277209997383,478821442691728585282962012650⟩,⟨(-728228155691246005553047400467),(-728228155691246005546403653031)⟩⟩⟩

def p5_170 : PointBox := ⟨⟨875147694418934845631889417574,875147694418934845632719871133⟩,⟨⟨498853497025771623688681444693,498853497025771623706745383911⟩,⟨1091426219437317519528012955224,1091426219437317519568570178776⟩⟩,⟨⟨(-1260270443185501659634945702278),(-1260270443185501659631771303185)⟩,⟨176026401588030845252428989268,176026401588030845253333289727⟩⟩,⟨⟨(-924056996520629368116997486709),(-924056996520629368100360717640)⟩,⟨(-382254715054338556536039421993),(-382254715054338556519907989856)⟩⟩,⟨⟨477978503402779831274363658655,477978503402779831280142467929⟩,⟨(-727989654416562611301676438300),(-727989654416562611295005119751)⟩⟩⟩

def p5_171 : PointBox := ⟨⟨874264154788074413588489041389,874264154788074413589326300408⟩,⟨⟨499687678229651405919262305489,499687678229651405937363402403⟩,⟨1092147564163653695272851463705,1092147564163653695313460234229⟩⟩,⟨⟨(-1261103380329359075626831881276),(-1261103380329359075623626814662)⟩,⟨176989631073256681978471384673,176989631073256681979385223894⟩⟩,⟨⟨(-922992405452117778386683090194),(-922992405452117778370019671579)⟩,⟨(-384818164173305914367373784840),(-384818164173305914351219375343)⟩⟩,⟨⟨477141056879685019246914221998,477141056879685019252723414609⟩,⟨(-727751420245115589459998313214),(-727751420245115589453295370174)⟩⟩⟩

def p5_172 : PointBox := ⟨⟨873387000819534201052646558597,873387000819534201053489030753⟩,⟨⟨500517757085664418872951007478,500517757085664418891087633127⟩,⟨1092864256794921524930131692677,1092864256794921524970786606064⟩⟩,⟨⟨(-1261930945696536480930470356082),(-1261930945696536480927240675986)⟩,⟨177948123575192141246463407106,177948123575192141247385068222⟩⟩,⟨⟨(-921928474148350567484426336216),(-921928474148350567467743607571)⟩,⟨(-387360153545113748582426777077),(-387360153545113748566256481986)⟩⟩,⟨⟨476309240998431363172568702052,476309240998431363178402987976⟩,⟨(-727513515974938000670036180567),(-727513515974938000663307576210)⟩⟩⟩

def p5_173 : PointBox := ⟨⟨872516364609475444314791330322,872516364609475444315640538279⟩,⟨⟨501343571594022412961115716862,501343571594022412979289183695⟩,⟨1093576176268866789857425915988,1093576176268866789898131896399⟩⟩,⟨⟨(-1262752999496383751873647111131),(-1262752999496383751870386940689)⟩,⟨178901692032594513931666201580,178901692032594513932597370652⟩⟩,⟨⟨(-920865525471836378943096825684),(-920865525471836378926387783235)⟩,⟨(-389880345744022681659462962464),(-389880345744022681643269969170)⟩⟩,⟨⟨475483192816373898338077966773,475483192816373898343942421717⟩,⟨(-727276004904397716311200263902),(-727276004904397716304440269229)⟩⟩⟩

def p5_174 : PointBox := ⟨⟨871652377272508926557972887712,871652377272508926558827635844⟩,⟨⟨502164959629013402256113330165,502164959629013402274322367179⟩,⟨1094283202108957510862321450852,1094283202108957510903074388256⟩⟩,⟨⟨(-1263569402614584550017759022578),(-1263569402614584550014472911902)⟩,⟨179850149238816884763957680084,179850149238816884764897066540⟩⟩,⟨⟨(-919803883810618253338189809496),(-919803883810618253321459967990)⟩,⟨(-392378408334228651224162965335),(-392378408334228651207952594216)⟩⟩,⟨⟨474663048543510424467713711861,474663048543510424473604351129⟩,⟨(-727038950805980305158302659244),(-727038950805980305151515761475)⟩⟩⟩

def p5_175 : PointBox := ⟨⟨870795168921949599751349443660,870795168921949599752210855057⟩,⟨⟨502981758985531997335616776350,502981758985531997353862310488⟩,⟨1094985214451164191420462249189,1094985214451164191461265742194⟩⟩,⟨⟨(-1264380016644079483419655474111),(-1264380016644079483416339067353)⟩,⟨180793307895536732714143027441,180793307895536732715091885174⟩⟩,⟨⟨(-918743874927321965007227038483),(-918743874927321964990471225113)⟩,⟨(-394854013888081646799831851535),(-394854013888081646783599065960)⟩⟩,⟨⟨473848943513980949089540208566,473848943513980949095460785269⟩,⟨(-726802417899534296757280596863),(-726802417899534296750462560138)⟩⟩⟩

def p5_176 : PointBox := ⟨⟨869944868650221998012812284438,869944868650221998013678524362⟩,⟨⟨503793807426309943702512299591,503793807426309943720792430895⟩,⟨1095682094070691099381466831641,1095682094070691099422314613480⟩⟩,⟨⟨(-1265184703915932732008989606930),(-1265184703915932732005649935016)⟩,⟨181730980667293059135352017564,181730980667293059136308342723⟩⟩,⟨⟨(-917685825807432992668150291522),(-917685825807432992651376971691)⟩,⟨(-397306840001691577160005462789),(-397306840001691577143758438622)⟩⟩,⟨⟨473041012157803234446925220359,473041012157803234452869592762⟩,⟨(-726566470824993679058934206436),(-726566470824993679052091943902)⟩⟩⟩

def p5_177 : PointBox := ⟨⟨869101604509419393313397415706,869101604509419393314270239686⟩,⟨⟨504600942729827851458678019474,504600942729827851476994270267⟩,⟨1096373722408647576143520262358,1096373722408647576184418039248⟩⟩,⟨⟨(-1265983327530129422651444653227),(-1265983327530129422648074917133)⟩,⟨182662980236810087812032278138,182662980236810087812998025080⟩⟩,⟨⟨(-916630064506894082171850478309),(-916630064506894082155051554299)⟩,⟨(-399736569307947097911524344835),(-399736569307947097895255212766)⟩⟩,⟨⟨472239387972855772281580353483,472239387972855772287554396613⟩,⟨(-726331174614593055811034339426),(-726331174614593055804161225441)⟩⟩⟩

def p5_178 : PointBox := ⟨⟨868265503492019621243149884740,868265503492019621244028044553⟩,⟨⟨505403002738888230778654788116,505403002738888230797005801075⟩,⟨1097059981598648403351368030997,1097059981598648403392311471280⟩⟩,⟨⟨(-1266775751386291086895942352267),(-1266775751386291086892547339001)⟩,⟨183589119361084575172111512148,183589119361084575173085316579⟩⟩,⟨⟨(-915576919999115061080515211891),(-915576919999115061063696444802)⟩,⟨(-402142889486975834708072908038),(-402142889486975834691787221885)⟩⟩,⟨⟨471444203497119219116050139192,471444203497119219122049659866⟩,⟨(-726096594664591446354878007647),(-726096594664591446347978756484)⟩⟩⟩

def p5_179 : PointBox := ⟨⟨867436691511760480964122612345,867436691511760480965007274808⟩,⟨⟨506199825409829081740816492722,506199825409829081759203220733⟩,⟨1097740754493332309141278509293,1097740754493332309182271355539⟩⟩,⟨⟨(-1267561840214296594412760972862),(-1267561840214296594409336141417)⟩,⟨184509210928212768960625504601,184509210928212768961608676316⟩⟩,⟨⟨(-914526722021486194453479466149),(-914526722021486194436635465014)⟩,⟨(-404525493274077002339665782166),(-404525493274077002323358295881)⟩⟩,⟨⟨470655590281187020767485246055,470655590281187020773514156222⟩,⟨(-725862796706521256066875141637),(-725862796706521256059945340733)⟩⟩⟩

def p5_180 : PointBox := ⟨⟨866615293384677589444954966706,866615293384677589445844375547⟩,⟨⟨506991248862356427400840888208,506991248862356427419261465804⟩,⟨1098415924690787758711178730974,1098415924690787758752214922866⟩⟩,⟨⟨(-1268341459604796027591926889843),(-1268341459604796027588479013968)⟩,⟨185423068014932061008456750857,185423068014932061009447351767⟩⟩,⟨⟨(-913479800921485930904174429159),(-913479800921485930887313304878)⟩,⟨(-406884078465159940746335857012),(-406884078465159940730014396481)⟩⟩,⟨⟨469873678861055639279087068944,469873678861055639285139447745⟩,⟨(-725629846777979479004201428247),(-725629846777979478997247731953)⟩⟩⟩

def p5_181 : PointBox := ⟨⟨865801432810307545606412492265,865801432810307545607308316212⟩,⟨⟨507777111429973326820148044801,507777111429973326838603900011⟩,⟨1099085376560875247401559232922,1099085376560875247442644194876⟩⟩,⟨⟨(-1269114476039605047535157075132),(-1269114476039605047531679662516)⟩,⟨186330503944851395726206621656,186330503944851395727206523143⟩⟩,⟨⟨(-912436487502473379506069247490),(-912436487502473379489183282018)⟩,⟨(-409218347919724562726718594403),(-409218347919724562710375661607)⟩⟩,⟨⟨469098598731204468834433322374,469098598731204468840514776438⟩,⟨(-725397811192978714647329411276),(-725397811192978714640345500781)⟩⟩⟩

def p5_182 : PointBox := ⟨⟨864995232353059235112250714018,864995232353059235113151652970⟩,⟨⟨508557251710982061287882378305,508557251710982061306372067393⟩,⟨1099748995271435398378544297228,1099748995271435398419673477094⟩⟩,⟨⟨(-1269880756921967398560346958659),(-1269880756921967398556845032340)⟩,⟨187231332347343521993236858014,187231332347343521994244621888⟩⟩,⟨⟨(-911397112869255283386580420487),(-911397112869255283369675617829)⟩,⟨(-411528009561422131795648339200),(-411528009561422131779289718056)⟩⟩,⟨⟨468330478317975190123374663877,468330478317975190129480792517⟩,⟨(-725166756511876087287341441691),(-725166756511876087280332256875)⟩⟩⟩

def p5_183 : PointBox := ⟨⟨864196813423756081218355266595,864196813423756081219262530344⟩,⟨⟨509331508620035353406038109580,509331508620035353424562611050⟩,⟨1100406666814372261236714865115,1100406666814372261277892148003⟩⟩,⟨⟨(-1270640170606673307141002870067),(-1270640170606673307137471706028)⟩,⟨188125367217071213589370685740,188125367217071213590387677214⟩⟩,⟨⟨(-910362008273516616842870959507),(-910362008273516616825941713610)⟩,⟨(-413812776376237159416434864734),(-413812776376237159400055102980)⟩⟩,⟨⟨467569444953259965679756942237,467569444953259965685891814534⟩,⟨(-724936749510898648907021846594),(-724936749510898648899982800325)⟩⟩⟩

def p5_184 : PointBox := ⟨⟨863406296261352021349311365169,863406296261352021350222967903⟩,⟨⟨510099721440211656259032622563,510099721440211656277589807415⟩,⟨1101058278031601312186891375726,1101058278031601312228109872081⟩⟩,⟨⟨(-1271392586430021651692896355995),(-1271392586430021651689343667186)⟩,⟨189012422974118633635254378212,189012422974118633636278380692⟩⟩,⟨⟨(-909331504959203231593772878032),(-909331504959203231576828368963)⟩,⟨(-416072366408333525906127745543),(-416072366408333525889735697178)⟩⟩,⟨⟨466815624848507522558610653574,466815624848507522564767530142⟩,⟨(-724707857151284323693563551217),(-724707857151284323686502208158)⟩⟩⟩

def p5_185 : PointBox := ⟨⟨862623799914823962909052755614,862623799914823962909970586098⟩,⟨⟨510861729875588739782760981229,510861729875588739801352479206⟩,⟨1101703716640851770740969584071,1101703716640851770782235466822⟩⟩,⟨⟨(-1272137874739613911541525752310),(-1272137874739613911537944163953)⟩,⟨189892314524698083077232586684,189892314524698083078265730211⟩⟩,⟨⟨(-908305934007944216462247136690),(-908305934007944216445278607984)⟩,⟨(-418306502753610185991093756878),(-418306502753610185974680922511)⟩⟩,⟨⟨466069143069055804031830484086,466069143069055804038015736625⟩,⟨(-724480146548057913960126476088),(-724480146548057913953035661379)⟩⟩⟩

def p5_186 : PointBox := ⟨⟨861849442225243445255165736515,861849442225243445256088445054⟩,⟨⟨511617374104289004909740952084,511617374104289004928365234705⟩,⟨1102342871261312971709616421842,1102342871261312971750924925114⟩⟩,⟨⟨(-1272875906923968046475274916107),(-1272875906923968046471669679998)⟩,⟨190764857322401453489243824348,190764857322401453490284598550⟩⟩,⟨⟨(-907285626184600815531822281782),(-907285626184600815514835969739)⟩,⟨(-420514913551014015672763767433),(-420514913551014015656336150854)⟩⟩,⟨⟨465330123508799499446537409154,465330123508799499452746436078⟩,⟨(-724253684938462132625546733106),(-724253684938462132618431604554)⟩⟩⟩

def p5_187 : PointBox := ⟨⟨861083339808030207778582267016,861083339808030207779511104089⟩,⟨⟨512366494831969174323850590924,512366494831969174342508660533⟩,⟨1102975631439114664624285708515,1102975631439114664665640853237⟩⟩,⟨⟨(-1273606555441940612206129790326),(-1273606555441940612202496007713)⟩,⟨191629867429964801785055630809,191629867429964801786105454038⟩⟩,⟨⟨(-906270911783027874860289146327),(-906270911783027874843279240186)⟩,⟨(-422697331971659489244630253132),(-422697331971659489228182206120)⟩⟩,⟨⟨464598688865200381716620329593,464598688865200381722857349960⟩,⟨(-724028539650064055911574161621),(-724028539650064055904429965712)⟩⟩⟩

def p5_188 : PointBox := ⟨⟨860325608035390336636058697946,860325608035390336636991745435⟩,⟨⟨513108933345726242938125350818,513108933345726242956815103242⟩,⟨1103601887672631255098431636932,1103601887672631255139826705982⟩⟩,⟨⟨(-1274329693851945581492704817586),(-1274329693851945581489049984581)⟩,⟨192487161581513580256822163886,192487161581513580257878873736⟩⟩,⟨⟨(-905262120472132859430720514993),(-905262120472132859413695887857)⟩,⟨(-424853496205806941573698125146),(-424853496205806941557238198496)⟩⟩,⟨⟨463874960614647995831455505818,463874960614647995837713966683⟩,⟨(-723804778068557800991707618956),(-723804778068557800984541700693)⟩⟩⟩

def p5_189 : PointBox := ⟨⟨859576361018941634885920225374,859576361018941634886859295921⟩,⟨⟨513844531568390822737194411267,513844531568390822755917391310⟩,⟨1104221531437600153848321998835,1104221531437600153889762917130⟩⟩,⟨⟨(-1275045196840958515277823459552),(-1275045196840958515274140470150)⟩,⟨193336557245255191095055788157,193336557245255191096121442027⟩⟩,⟨⟨(-904259581142316502482583408906),(-904259581142316502465535636181)⟩,⟨(-426983149447753168817843362543),(-426983149447753168801363381601)⟩⟩,⟨⟨463159058988177850006923227875,463159058988177850013209265638⟩,⟨(-723582467605284626416896137753),(-723582467605284626409701591265)⟩⟩⟩

def p5_190 : PointBox := ⟨⟨858835711592528832582445103338,858835711592528832583388799057⟩,⟨⟨514573132113178286623191216219,514573132113178286641945811729⟩,⟨1104834455212044558777760100899,1104834455212044558819241893005⟩⟩,⟨⟨(-1275752940253294912579601176750),(-1275752940253294912575895507286)⟩,⟨194177872686584691610541892181,194177872686584691611614908427⟩⟩,⟨⟨(-903263621752378121037035113736),(-903263621752378121019970657351)⟩,⟨(-429086039878690048391605567566),(-429086039878690048375111749616)⟩⟩,⟨⟨462451102947553864428533573741,462451102947553864434842389810⟩,⟨(-723361675664492027726000557826),(-723361675664492027718782754276)⟩⟩⟩

def p5_191 : PointBox := ⟨⟨858103771295231224795011183014,858103771295231224795960793662⟩,⟨⟨515294578338667405584251517043,515294578338667405603038753334⟩,⟨1105440552500991163349465754979,1105440552500991163390992573812⟩⟩,⟨⟨(-1276452801119151761655430702064),(-1276452801119151761651697284106)⟩,⟨195010927031568656172161107581,195010927031568656173242956307⟩⟩,⟨⟨(-902274569176967556685474703871),(-902274569176967556668387554783)⟩,⟨(-431161920647588714120566487594),(-431161920647588714104052994840)⟩⟩,⟨⟨461751210161721431711761330993,461751210161721431718097290165⟩,⟨(-723142469610353756224843691133),(-723142469610353756217597715530)⟩⟩⟩

def p5_192 : PointBox := ⟨⟨857380650354565296539242080072,857380650354565296540195389312⟩,⟨⟨516008714404075484073310451334,516008714404075484092127889147⟩,⟨1106039717860973460058384156311,1106039717860973460099948213674⟩⟩,⟨⟨(-1277144657682901517714634530271),(-1277144657682901517710882079576)⟩,⟨195835540330771404787772309341,195835540330771404788860466336⟩⟩,⟨⟨(-901292749054664581947393033113),(-901292749054664581930293454649)⟩,⟨(-433210549850168603147509727743),(-433210549850168603130986448520)⟩⟩,⟨⟨461059496983637039009701936598,461059496983637039016057424296⟩,⟨(-722924916733773025013407513437),(-722924916733773025006141891972)⟩⟩⟩

def p5_193 : PointBox := ⟨⟨856666457669884864243027218877,856666457669884864243986327880⟩,⟨⟨516715385324798331135451197241,516715385324798331154300654770⟩,⟨1106631846924311490809764482907,1106631846924311490851372693880⟩⟩,⟨⟨(-1277828389431127943751801207834),(-1277828389431127943748021458110)⟩,⟨196651533623387037666530192441,196651533623387037667627055782⟩⟩,⟨⟨(-900318485636765452142725433513),(-900318485636765452125603642123)⟩,⟨(-435231690506012395391221385902),(-435231690506012395374678835711)⟩⟩,⟨⟨460376078427479994919557831439,460376078427479994925939990717⟩,⟨(-722709084218991482511193903896),(-722709084218991482503900605330)⟩⟩⟩

def p5_194 : PointBox := ⟨⟨855961300795981233625079797344,855961300795981233626043263286⟩,⟨⟨517414437028182760735002915181,517414437028182760753882699784⟩,⟨1107216836423159085993602829656,1107216836423159086035250020094⟩⟩,⟨⟨(-1278503877120393470452517459555),(-1278503877120393470448716099794)⟩,⟨197458729001639971373342247173,197458729001639971374446167138⟩⟩,⟨⟨(-899352101636855083198240121466),(-899352101636855083181102789437)⟩,⟨(-437225110533889492438225290580),(-437225110533889492421669885543)⟩⟩,⟨⟨459701068146251395772463317394,459701068146251395778867163260⟩,⟨(-722495039110026829556769295232),(-722495039110026829549453892047)⟩⟩⟩

def p5_195 : PointBox := ⟨⟨855265285926885843741903021681,855265285926885843742872170363⟩,⟨⟨518105716409498695073094354652,518105716409498695092005511988⟩,⟨1107794584213309830626348667021,1107794584213309830668039111666⟩⟩,⟨⟨(-1279171002804727958113890677075),(-1279171002804727958110062481572)⟩,⟨198256949675415956663866999529,198256949675415956664979494428⟩⟩,⟨⟨(-898393918081242099561435361586),(-898393918081242099544276296655)⟩,⟨(-439190582725352229008943931229),(-439190582725352228992369658674)⟩⟩,⟨⟨459034578409765056334816279267,459034578409765056341246311625⟩,⟨(-722282848276962231249542015355),(-722282848276962231242199443138)⟩⟩⟩

def p5_196 : PointBox := ⟨⟨854578517879877836465420836761,854578517879877836466393593725⟩,⟨⟨518789071388077350598832265508,518789071388077350617772456069⟩,⟨1108364989297753198677213496356,1108364989297753198718939835507⟩⟩,⟨⟨(-1279829649862828977633222275726),(-1279829649862828977629375449018)⟩,⟨199046020037084872095256289593,199046020037084872096374974975⟩⟩,⟨⟨(-897444254160332725875678439836),(-897444254160332725858507251883)⟩,⟨(-441127884716670475032624755458),(-441127884716670475016040866510)⟩⟩,⟨⟨458376720083034720207602718622,458376720083034720214051765712⟩,⟨(-722072578382110928697179006828),(-722072578382110928689817285068)⟩⟩⟩

def p5_197 : PointBox := ⟨⟨853901100079698959792458673339,853901100079698959793436989697⟩,⟨⟨519464350963581419028104582206,519464350963581419047075465765⟩,⟨1108927951849972505171803875202,1108927951849972505213572522232⟩⟩,⟨⟨(-1280479703024963968345260447532),(-1280479703024963968341387286396)⟩,⟨199825765726475932343265248714,199825765726475932344392364135⟩⟩,⟨⟨(-896503427081018193724908690130),(-896503427081018193707716272528)⟩,⟨(-443036798959171668454426212356),(-443036798959171668437823880397)⟩⟩,⟨⟨457727602605061456087146773831,457727602605061456093621487812⟩,⟨(-721864295846079688398747005382),(-721864295846079688391358658024)⟩⟩⟩

def p5_198 : PointBox := ⟨⟨853233134542978182163600934208,853233134542978182164583323980⟩,⟨⟨520131405272372616096220962106,520131405272372616115220767560⟩,⟨1109483373236976539421373846956,1109483373236976539463179435296⟩⟩,⟨⟨(-1281121048399564877311712557054),(-1281121048399564877307818956624)⟩,⟨200596013695965327094045037034,200596013695965327095178866410⟩⟩,⟨⟨(-895571751920149003025178993505),(-895571751920149003007972220502)⟩,⟨(-444917112688054616859039563477),(-444917112688054616842425395482)⟩⟩,⟨⟨457087333968024738351428788700,457087333968024738357924004119⟩,⟨(-721658066813754937827216166601),(-721658066813754937819806960760)⟩⟩⟩

def p5_199 : PointBox := ⟨⟨852574721862868363387189470611,852574721862868363388177293875⟩,⟨⟨520790085643941460061623724120,520790085643941460080653516317⟩,⟨1110031156042056961300583738673,1110031156042056961342430659554⟩⟩,⟨⟨(-1281753573499506137055337575703),(-1281753573499506137051418159882)⟩,⟨201356592275635716662999779136,201356592275635716664141887003⟩⟩,⟨⟨(-894649541479168018954799907298),(-894649541479168018937572411806)⟩,⟨(-446768617889746618619376077577),(-446768617889746618602743894213)⟩⟩,⟨⟨456456020696880304961922796345,456456020696880304968443142299⟩,⟨(-721453957120235624602197035565),(-721453957120235624594761764091)⟩⟩⟩

def p5_200 : PointBox := ⟨⟨851925961193897295829338732729,851925961193897295830329649653⟩,⟨⟨521440244657363661198147209401,521440244657363661217204343390⟩,⟨1110571204087263765420903950559,1110571204087263765462783878447⟩⟩,⟨⟨(-1282377167268057096141248195895),(-1282377167268057096137312268786)⟩,⟨202107331238466455336447166704,202107331238466455337594839792⟩⟩,⟨⟨(-893737106139973002088183272016),(-893737106139973002070945903743)⟩,⟨(-448591111267874580469196079881),(-448591111267874580452556323761)⟩⟩,⟨⟨455833767829367483220434267269,455833767829367483226971615305⟩,⟨(-721252032256737003219584798189),(-721252032256737003212132542373)⟩⟩⟩

def p5_201 : PointBox := ⟨⟨851286950237035397247415030749,851286950237035397248411248355⟩,⟨⟨522081736197747053683029747232,522081736197747053702116128587⟩,⟨1111103422455591344841414431175,1111103422455591344883334667157⟩⟩,⟨⟨(-1282991720104500278888346039543),(-1282991720104500278884384857389)⟩,⟨202848061865512894012562816512,202848061865512894013718601888⟩⟩,⟨⟨(-892834753722077764025358634869),(-892834753722077764008101077533)⟩,⟨(-450384394207921847173878572529),(-450384394207921847157221252680)⟩⟩,⟨⟨455220678896428275284616880724,455220678896428275291178785783⟩,⟨(-721052357336489697415672032565),(-721052357336489697408194309274)⟩⟩⟩

def p5_202 : PointBox := ⟨⟨850657785224982304017543311257,850657785224982304018543304234⟩,⟨⟨522714415512632583395826377759,522714415512632583414940161287⟩,⟨1111627717512867916138842515392,1111627717512867916180797514160⟩⟩,⟨⟨(-1283597123889407116282441029254),(-1283597123889407116278460678294)⟩,⟨203578617011032631177906388042,203578617011032631179068507550⟩⟩,⟨⟨(-891942789341139715656772777011),(-891942789341139715639502088812)⟩,⟨(-452148272740643409464223496206),(-452148272740643409447555393238)⟩⟩,⟨⟨454616855903040101309121096170,454616855903040101315702225623⟩,⟨(-720854997060658507704045931821),(-720854997060658507696548687959)⟩⟩⟩

def p5_203 : PointBox := ⟨⟨850038560907674580541049838191,850038560907674580542054997111⟩,⟨⟨523338139268312480143641104966,523338139268312480162783371594⟩,⟨1112143996929341300732070828288,1112143996929341300774065085228⟩⟩,⟨⟨(-1284193272009563059293056763639),(-1284193272009563059289051732424)⟩,⟨204298831167516136696432676098,204298831167516136697602736107⟩⟩,⟨⟨(-891061515268920132610642448826),(-891061515268920132593352105822)⟩,⟨(-453882557504313017849957052113),(-453882557504313017833271837437)⟩⟩,⟨⟨454022399309463709414550322376,454022399309463709421155421576⟩,⟨(-720660015684305532280717055857),(-720660015684305532273194956062)⟩⟩⟩

def p5_204 : PointBox := ⟨⟨849429370538016727315527111867,849429370538016727316535213803⟩,⟨⟨523952765606028391638918166279,523952765606028391658086349495⟩,⟨1112652169700954292828085987722,1112652169700954292870111526726⟩⟩,⟨⟨(-1284780059382534257694781732356),(-1284780059382534257690760906638)⟩,⟨205008540530578767369556498112,205008540530578767370731898966⟩⟩,⟨⟨(-890191230794742004700325697996),(-890191230794742004683026009946)⟩,⟨(-455587063705876501698898063388),(-455587063705876501682205653172)⟩⟩,⟨⟨453437408012907379156178789855,453437408012907379162800093023⟩,⟨(-720467476982422245221058982540),(-720467476982422245213520692492)⟩⟩⟩

def p5_205 : PointBox := ⟨⟨848830305857837636528192182334,848830305857837636529205309160⟩,⟨⟨524558154198011940056657679895,524558154198011940075853550473⟩,⟨1113152146170303081726870026227,1113152146170303081768933727807⟩⟩,⟨⟨(-1285357382480868261586364705338),(-1285357382480868261582319812328)⟩,⟨205707583063670827763842496652,205707583063670827765025652574⟩⟩,⟨⟨(-889332232088508865587690726977),(-889332232088508865570371941730)⟩,⟨(-457261611081086274525302087167),(-457261611081086274508593038659)⟩⟩,⟨⟨452861979329608169515911419397,452861979329608169522556070804⟩,⟨(-720277444216055228597546966335),(-720277444216055228589984467030)⟩⟩⟩

def p5_206 : PointBox := ⟨⟨848241457084074610077698750121,848241457084074610078715339829⟩,⟨⟨525154166303329881027511383572,525154166303329881046733025717⟩,⟨1113643838047272434992610842192,1113643838047272435034706992344⟩⟩,⟨⟨(-1285925139355921478508002657995),(-1285925139355921478503939964278)⟩,⟨206395798562562005366207689236,206395798562562005367396763115⟩⟩,⟨⟨(-888484812065346517625643475772),(-888484812065346517608312823045)⟩,⟨(-458906023853692597356757808536),(-458906023853692597340039064172)⟩⟩,⟨⟨452296208977330594407462192162,452296208977330594414124701606⟩,⟨(-720089980098550284764013851532),(-720089980098550284756433259020)⟩⟩⟩

def p5_207 : PointBox := ⟨⟨847662912895187020660439417660,847662912895187020661460888721⟩,⟨⟨525740664823495800277859733367,525740664823495800297108242194⟩,⟨1114127158429341588666712201657,1114127158429341588708845391497⟩⟩,⟨⟨(-1286483229661306395802631534899),(-1286483229661306395798545404249)⟩,⟨207073028719556226634402107581,207073028719556226635598744492⟩⟩,⟨⟨(-887649260251928077113995324998),(-887649260251928077096646136578)⟩,⟨(-460520130693767672035751884253),(-460520130693767672019016978357)⟩⟩,⟨⟨451740191058282748980384784278,451740191058282748987070004315⟩,⟨(-719905146761939661545382992757),(-719905146761939661537778853623)⟩⟩⟩

def p5_208 : PointBox := ⟨⟨847094760417801661974033308521,847094760417801661975057102410⟩,⟨⟨526317514357810075559659359460,526317514357810075578931790369⟩,⟨1114602021821555030766316746294,1114602021821555030808477786039⟩⟩,⟨⟨(-1287031554675951855073471985088),(-1287031554675951855069372690676)⟩,⟨207739117187392740831290938288,207739117187392740832492124058⟩⟩,⟨⟨(-886825862654541269119400657215),(-886825862654541269102044811964)⟩,⟨(-462103764675239045159543523782),(-462103764675239045142803881136)⟩⟩,⟨⟨451194018042449559330000213752,451194018042449559336699172379⟩,⟨(-719723005723497106434013260967),(-719723005723497106426395580532)⟩⟩⟩

def p5_209 : PointBox := ⟨⟨846537085213591799199107328882,846537085213591799200135853585⟩,⟨⟨526884581258389661726611375868,526884581258389661745909821116⟩,⟨1115068344156152604283573435874,1115068344156152604325770344368⟩⟩,⟨⟨(-1287570017326769942685787233852),(-1287570017326769942681665174666)⟩,⟨208393909642789042479200571170,208393909642789042480409113038⟩⟩,⟨⟨(-886014901628955400640942527495),(-886014901628955400623568735078)⟩,⟨(-463656763232709120980538417413),(-463656763232709120963783114919)⟩⟩,⟨⟨450657780751342487241436019349,450657780751342487248157013706⟩,⟨(-719543617852485426147819719203),(-719543617852485426140179193139)⟩⟩⟩

def p5_210 : PointBox := ⟨⟨845989971266391895726137516200,845989971266391895727169177905⟩,⟨⟨527441733684849125466230850088,527441733684849125485553329382⟩,⟨1115526042811853595284848800263,1115526042811853595327075713117⟩⟩,⟨⟨(-1288098522210923336677123547251),(-1288098522210923336672985149965)⟩,⟨209037253849581091604173767745,209037253849581091605387775639⟩⟩,⟨⟨(-885216655752143938255897581473),(-885216655752143938238513220104)⟩,⟨(-465178968117637807993937067634),(-465178968117637807977173187555)⟩⟩,⟨⟨450131568342164690969917920960,450131568342164690976655321099⟩,⟨(-719367043337121165100541950124),(-719367043337121165092884843881)⟩⟩⟩

def p5_211 : PointBox := ⟨⟨845453500969549956602075789110,845453500969549956603112029374⟩,⟨⟨527988841658594263896327368128,527988841658594263915674986676⟩,⟨1115975036632789710018859861487,1115975036632789710061121449322⟩⟩,⟨⟨(-1288616975617687225617257459488),(-1288616975617687225613096982736)⟩,⟨209668999721416184359883512442,209668999721416184361104664328⟩⟩,⟨⟨(-884431399695917113403079588402),(-884431399695917113385677868649)⟩,⟨(-466670225353965459252702555928),(-466670225353965459235923517728)⟩⟩,⟨⟨449615468292390323413174201604,449615468292390323419932950307⟩,⟨(-719193341651780930549881291711),(-719193341651780930542202052777)⟩⟩⟩

def p5_212 : PointBox := ⟨⟨844927755113519393387349196499,844927755113519393388387655849⟩,⟨⟨528525777116689588534619310119,528525777116689588553989289626⟩,⟨1116415245947082081700733902085,1116415245947082081743021616676⟩⟩,⟨⟨(-1289125285549900188343168971110),(-1289125285549900188338995934148)⟩,⟨210288999383953765768482317976,210288999383953765769707812655⟩⟩,⟨⟨(-883659404102517477033883353674),(-883659404102517477016475229036)⟩,⟨(-468130385193253310896165198506),(-468130385193253310879381529892)⟩⟩,⟨⟨449109566384756340968224501555,449109566384756340974996281498⟩,⟨(-719022571524473783528971372765),(-719022571524473783521279265749)⟩⟩⟩

def p5_213 : PointBox := ⟨⟨844412812873692279042714019447,844412812873692279043756898876⟩,⟨⟨529052413965260943553206698865,529052413965260943572600913174⟩,⟨1116846592585057682374736889767,1116846592585057682417058042111⟩⟩,⟨⟨(-1289623361744998694544333250212),(-1289623361744998694540138856522)⟩,⟨210897107236529461769903669090,210897107236529461771136082235⟩⟩,⟨⟨(-882900935462229827297426393718),(-882900935462229827280001522809)⟩,⟨(-469559302069418577286777198293),(-469559302069418577269978894876)⟩⟩,⟨⟨448613946692664900457625888222,448613946692664900464418296326⟩,⟨(-718854790904603983263712434448),(-718854790904603983255998941884)⟩⟩⟩

def p5_214 : PointBox := ⟨⟨843908751798475825113056466370,843908751798475825114102143320⟩,⟨⟨529568628132394555182581407224,529568628132394555201997816089⟩,⟨1117268999897100747513339904497,1117268999897100747555688492190⟩⟩,⟨⟨(-1290111115695630154358031988070),(-1290111115695630154353822811058)⟩,⟨211493180013237640048423233761,211493180013237640049660626406⟩⟩,⟨⟨(-882156255993055440965777868810),(-882156255993055440948343763939)⟩,⟨(-470956834553141224946829923902),(-470956834553141224930024194110)⟩⟩,⟨⟨448128691565994138306030213492,448128691565994138312837491799⟩,⟨(-718690056931048218789903031591),(-718690056931048218782174555477)⟩⟩⟩

def p5_215 : PointBox := ⟨⟨843415647797613876846785928135,843415647797613876847835864240⟩,⟨⟨530074297620493878023147464330,530074297620493878042587180813⟩,⟨1117682392771135050335877886949,1117682392771135050378258649985⟩⟩,⟨⟨(-1290588460669839709937263881559),(-1290588460669839709933034087382)⟩,⟨212077076843387888656411090397,212077076843387888657655169579⟩⟩,⟨⟨(-881425623522499053115930284554),(-881425623522499053098480049818)⟩,⟨(-472322845306019221701455673129),(-472322845306019221684635835751)⟩⟩,⟨⟨447653881617314856161277377987,447653881617314856168104548693⟩,⟨(-718528425900571285094177934404),(-718528425900571285086428835171)⟩⟩⟩

def p5_216 : PointBox := ⟨⟨842933575130755184990729614832,842933575130755184991781151732⟩,⟨⟨530569302558055714189160815142,530569302558055714208620720126⟩,⟨1118086697649733088792571296283,1118086697649733088834974597483⟩⟩,⟨⟨(-1291055311730826222872368941308),(-1291055311730826222868129294497)⟩,⟨212648659311290928665027239989,212648659311290928666274830647⟩⟩,⟨⟨(-880709291371515551755532937204),(-880709291371515551738078925577)⟩,⟨(-473657201034548742688643245508),(-473657201034548742671821172925)⟩⟩,⟨⟨447189595708510380869945916369,447189595708510380876783579955⟩,⟨(-718369953236603962518642625491),(-718369953236603962510883367918)⟩⟩⟩

def p5_217 : PointBox := ⟨⟨842462606396270175836717068660,842462606396270175837772697096⟩,⟨⟨531053525250827232924573502688,531053525250827232944055759235⟩,⟨1118481842546848470338147424869,1118481842546848470380581594450⟩⟩,⟨⟨(-1291511585756263167897564168383),(-1291511585756263167893304683632)⟩,⟨213207791515329652256514814586,213207791515329652257768845699⟩⟩,⟨⟨(-880007508240661886121233361773),(-880007508240661886103763862762)⟩,⟨(-474959772444005411911030092755),(-474959772444005411894194464041)⟩⟩,⟨⟨446735910937796624585478638498,446735910937796624592335423669⟩,⟨(-718214693458406637623844805154),(-718214693458406637616065723107)⟩⟩⟩

def p5_218 : PointBox := ⟨⟨842002812520317903673183190005,842002812520317903674241264202⟩,⟨⟨531526850232305711807079149489,531526850232305711826581664803⟩,⟨1118867757064167997610263892028,1118867757064167997652722811006⟩⟩,⟨⟨(-1291957201457180395027368031252),(-1291957201457180395023095404940)⟩,⟨213754340126271201080524266533,213754340126271201081782757454⟩⟩,⟨⟨(-879320518098498230719910481513),(-879320518098498230702433115557)⟩,⟨(-476230434192302167588134864755),(-476230434192302167571292989733)⟩⟩,⟨⟨446292902627139143225605930608,446292902627139143232475972298⟩,⟨(-718062700150641961452711172405),(-718062700150641961444918781420)⟩⟩⟩

def p5_219 : PointBox := ⟨⟨841554262746164832118500593834,841554262746164832119562590080⟩,⟨⟨531989164313543056048886099321,531989164313543056068409989648⟩,⟨1119244372407080171543303147155,1119244372407080171585791606219⟩⟩,⟨⟨(-1292392079396402968699276446354),(-1292392079396402968694984774698)⟩,⟨214288174444776271504435939173,214288174444776271505700619272⟩⟩,⟨⟨(-878648560072281003171388104643),(-878648560072281003153895895582)⟩,⟨(-477469064843898762624583714895),(-477469064843898762607728836858)⟩⟩,⟨⟨445860644310063778885883806539,445860644310063778892772186779⟩,⟨(-717914025933379577458093940415),(-717914025933379577450282535640)⟩⟩⟩

def p5_220 : PointBox := ⟨⟨841117024623757052888316875978,841117024623757052889380312909⟩,⟨⟨532440356632217429802320225341,532440356632217429821862521549⟩,⟨1119611621400257036919932106796,1119611621400257036962441043745⟩⟩,⟨⟨(-1292816142006543533221033161264),(-1292816142006543533216732533746)⟩,⟨214809166458062153701087763029,214809166458062153702355648714⟩⟩,⟨⟨(-877991868340988903806269350195),(-877991868340988903788773826191)⟩,⟨(-478675546823837249028981261313),(-478675546823837249012124453839)⟩⟩,⟨⟨445439207719857274504581371847,445439207719857274511479277591⟩,⟨(-717768722432555666547036776867),(-717768722432555666539216160538)⟩⟩⟩

def p5_221 : PointBox := ⟨⟨840691163999547512382363512879,840691163999547512383430696338⟩,⟨⟨532880318700934652814106386713,532880318700934652833669054972⟩,⟨1119969438502846498540831539872,1119969438502846498583368648402⟩⟩,⟨⟨(-1293229313607544888431108021600),(-1293229313607544888426789177025)⟩,⟨215317190895676380369943832285,215317190895676380371217643107⟩⟩,⟨⟨(-877350672030721729950258558308),(-877350672030721729932748858565)⟩,⟨(-479849766371977048177222984443),(-479849766371977048160353748613)⟩⟩,⟨⟨445028662778154067368881919669,445028662778154067375797349488⟩,⟨(-717626840250909751077141029952),(-717626840250909751069302243018)⟩⟩⟩

def p5_222 : PointBox := ⟨⟨840276745006579778073025763983,840276745006579778074095028955⟩,⟨⟨533308944454722377210256016307,533308944454722377229836917363⟩,⟨1120317759823272433749419508501,1120317759823272433791978569444⟩⟩,⟨⟨(-1293631520423769687598997874518),(-1293631520423769687594667614332)⟩,⟨215812125284338278240483451753,215812125284338278241761170966⟩⟩,⟨⟨(-876725195112510318972472296749),(-876725195112510318954956131126)⟩,⟨(-480991613497502378572659342684),(-480991613497502378555785071940)⟩⟩,⟨⟨444629077583905302225444446233,444629077583905302232371443616⟩,⟨(-717488428939420873553809765538),(-717488428939420873545959420007)⟩⟩⟩

def p5_223 : PointBox := ⟨⟨839873830054829838043947329939,839873830054829838045020163465⟩,⟨⟨533726130297680462535800269068,533726130297680462555400519276⟩,⟨1120656523133640118675396584948,1120656523133640118717982426195⟩⟩,⟨⟨(-1294022690600634390864295064158),(-1294022690600634390859947431274)⟩,⟨216293850001806181246175000737,216293850001806181247458374990⟩⟩,⟨⟨(-876115656302574592489090789354),(-876115656302574592471561120563)⟩,⟨(-482100981933773900456955149169),(-482100981933773900440069029637)⟩⟩,⟨⟨444240518402725955041553639924,444240518402725955048497332441⟩,⟨(-717353536969264919582159826670),(-717353536969264919574292168253)⟩⟩⟩

def p5_224 : PointBox := ⟨⟨839482479821807388168165549231,839482479821807388169239076250⟩,⟨⟨534131775148751412258444400118,534131775148751412278060592879⟩,⟨1120985667883744670975227916483,1120985667883744671017830054074⟩⟩,⟨⟨(-1294402754220784821610917731759),(-1294402754220784821606564447266)⟩,⟨216762248329728578197098990405,216762248329728578198384547740⟩⟩,⟨⟨(-875522268965065310502503657022),(-875522268965065310484973857625)⟩,⟨(-483177769093595443590082309412),(-483177769093595443573197187831)⟩⟩,⟨⟨443863049656615825050778259349,443863049656615825057728416591⟩,⟨(-717222211704314488700831606003),(-717222211704314488692958010695)⟩⟩⟩

def p5_225 : PointBox := ⟨⟨839102753243418022337325625925,839102753243418022338402536963⟩,⟨⟨534525780486575221545919945364,534525780486575221565554438702⟩,⟨1121305135214680390787809808827,1121305135214680390830437294158⟩⟩,⟨⟨(-1294771643319810879795675491804),(-1294771643319810879791305716958)⟩,⟨217217206505438029657376000581,217217206505438029658666929390⟩⟩,⟨⟨(-874945241017323799539187630845),(-874945241017323799521645027119)⟩,⟨(-484221876024965612145233387531),(-484221876024965612128337021325)⟩⟩,⟨⟨443496733914050035762206550198,443496733914050035769172540320⟩,⟨(-717094499374202331463095044875),(-717094499374202331455205029008)⟩⟩⟩

def p5_226 : PointBox := ⟨⟨838734707505087701862548552681,838734707505087701863627170269⟩,⟨⟨534908050393393513952681203923,534908050393393513972331821427⟩,⟨1121614867972049053854444804179,1121614867972049053897091344569⟩⟩,⟨⟨(-1295129291901498165124895105158),(-1295129291901498165120515716737)⟩,⟨217658613772647298214371356394,217658613772647298215665612987⟩⟩,⟨⟨(-874384774837692593753070148879),(-874384774837692593735522508236)⟩,⟨(-485233207367382910426347550356),(-485233207367382910409447386177)⟩⟩,⟨⟨443141631880434585229620449263,443141631880434585236596250270⟩,⟨(-716970445047968966944435184030),(-716970445047968966936535427605)⟩⟩⟩

def p5_227 : PointBox := ⟨⟨838378398033150840669176875209,838378398033150840670258690499⟩,⟨⟨535278491597968413346798576705,535278491597968413366466428970⟩,⟨1121914810718765376062230981841,1121914810718765376104901419171⟩⟩,⟨⟨(-1295475635952614453856939371031),(-1295475635952614453852544386508)⟩,⟨218086362431007792999309010818,218086362431007793000608350754⟩⟩,⟨⟨(-873841067175908623122708830605),(-873841067175908623105149086806)⟩,⟨(-486211671308771806558696602726),(-486211671308771806541785800388)⟩⟩,⟨⟨442797802388922402138850234518,442797802388922402145840995420⟩,⟨(-716850092608314672173905374104),(-716850092608314672165990100156)⟩⟩⟩

def p5_228 : PointBox := ⟨⟨838033878486503303208125646926,838033878486503303209208076013⟩,⟨⟨535637013517482206552690243428,535637013517482206572372199140⟩,⟨1122204909747458026875346394300,1122204909747458026918031231212⟩⟩,⟨⟨(-1295810613457229155687699605151),(-1295810613457229155683299597381)⟩,⟨218500347884491132698742825040,218500347884491132700044109355⟩⟩,⟨⟨(-873314309066109298834321894098),(-873314309066109298816762058737)⟩,⟨(-487157179543095850040125176804),(-487157179543095850023215269044)⟩⟩,⟨⟨442465302391585297211773857439,442465302391585297218770345508⟩,⟨(-716733484726475594250417653296),(-716733484726475594242497118691)⟩⟩⟩

def p5_229 : PointBox := ⟨⟨837701200748521572111618776183,837701200748521572112704210923⟩,⟨⟨535983528298384501295112457679,535983528298384501314810559698⟩,⟨1122485113092464720060390843464,1122485113092464720103098090603⟩⟩,⟨⟨(-1296134164410564051469121944163),(-1296134164410564051464707267424)⟩,⟨218900468688555380823744483130,218900468688555380825050551006⟩⟩,⟨⟨(-872804685742480583164466238947),(-872804685742480583146895024185)⟩,⟨(-488069647228722584755456409470),(-488069647228722584738536491244)⟩⟩,⟨⟨442144186950937149035017742927,442144186950937149042028289086⟩,⟨(-716620662837743277572543449114),(-716620662837743277564608329992)⟩⟩⟩

def p5_230 : PointBox := ⟨⟨837380414919249302536970910221,837380414919249302538057665013⟩,⟨⟨536317950856154272556688050701,536317950856154272576400092454⟩,⟨1122755370541420053659913835139,1122755370541420053702637144653⟩⟩,⟨⟨(-1296446230832373778265219116143),(-1296446230832373778260796702477)⟩,⟨219286626596058302046002412605,219286626596058302047311199792⟩⟩,⟨⟨(-872312376557574890018949381930),(-872312376557574890001374592474)⟩,⟨(-488948992947603553495029832237),(-488948992947603553478107384174)⟩⟩,⟨⟨441834509231803629652594726295,441834509231803629659613260560⟩,⟨(-716511667117646423150143137241),(-716511667117646423142200162601)⟩⟩⟩

def p5_231 : PointBox := ⟨⟨837071569307852439874556166876,837071569307852439875645732747⟩,⟨⟨536640198913944917793337399722,536640198913944917813064482693⟩,⟨1123015633646434907218175110848,1123015633646434907260919323716⟩⟩,⟨⟨(-1296746756779854685347477933442),(-1296746756779854685343041793185)⟩,⟨219658726601880828260775825726,219658726601880828262089091095⟩⟩,⟨⟨(-871837554903325443024085500615),(-871837554903325443006500062188)⟩,⟨(-489795138665331174990953269334),(-489795138665331174974021444912)⟩⟩,⟨⟨441536320493533758024151096046,441536320493533758031182773085⟩,⟨(-716406536458813204861570989946),(-716406536458813204853614377590)⟩⟩⟩

def p5_232 : PointBox := ⟨⟨836774710425344037051517410428,836774710425344037052606876031⟩,⟨⟨536950193040081206915212369150,536950193040081206934950996424⟩,⟨1123265855734866332740466379039,1123265855734866332783220811256⟩⟩,⟨⟨(-1297035688360080833083813583447),(-1297035688360080833079375651782)⟩,⟨220016676986224806917459006772,220016676986224806918773202588⟩⟩,⟨⟨(-871380388134782520886966842000),(-871380388134782520869384301445)⟩,⟨(-490608009692132691859709994007),(-490608009692132691842781801435)⟩⟩,⟨⟨441249670082548568615241662055,441249670082548568622276065943⟩,⟨(-716305308448531959264210419055),(-716305308448531959256251738677)⟩⟩⟩

def p5_233 : PointBox := ⟨⟨836489882977579867046938120502,836489882977579867048030196649⟩,⟨⟨537247856684377815798481645482,537247856684377815818234187747⟩,⟨1123505991919676996723640445477,1123505991919676996766414238821⟩⟩,⟨⟨(-1297312973741966046228601928102),(-1297312973741966046224151245584)⟩,⟨220360389356550031218784726945,220360389356550031220103083863⟩⟩,⟨⟨(-870941037496595844741904497360),(-870941037496595844724312062559)⟩,⟨(-491387534644859739545592993754),(-491387534644859739528656081824)⟩⟩,⟨⟨440974605425222197782093940278,440974605425222197789140542464⟩,⟨(-716208019347027541664532884246),(-716208019347027541656561543446)⟩⟩⟩

def p5_234 : PointBox := ⟨⟨836217129858525885453502947834,836217129858525885454595948124⟩,⟨⟨537533116213249971548357834946,537533116213249971568122065844⟩,⟨1123735999109383343812651516786,1123735999109383343855438297505⟩⟩,⟨⟨(-1297578563167751063852689867756),(-1297578563167751063848233388994)⟩,⟨220689778688116521108884551448,220689778688116521110204994856⟩⟩,⟨⟨(-870519658052266209390315733561),(-870519658052266209372721212122)⟩,⟨(-492133645410030374377235947476),(-492133645410030374360297797981)⟩⟩,⟨⟨440711172021090722031714803436,440711172021090722038767514388⟩,⟨(-716114704066470102120612585875),(-716114704066470102112635331542)⟩⟩⟩

def p5_235 : PointBox := ⟨⟨835956492143798556980983314348,835956492143798556982078722520⟩,⟨⟨537805900943587612928200482370,537805900943587612947977487938⟩,⟨1123955836017591758224144686242,1123955836017591758266949269188⟩⟩,⟨⟨(-1297832408964014950073357213967),(-1297832408964014950068888972442)⟩,⟨221004763363099034557919233352,221004763363099034559243516288⟩⟩,⟨⟨(-870116398616188329648044421933),(-870116398616188329630440766284)⟩,⟨(-492846277107978625215764410559),(-492846277107978625198818203908)⟩⟩,⟨⟨440459413436384129428796349936,440459413436384129435860303737⟩,⟨(-716025396150732481410415028557),(-716025396150732481402426102349)⟩⟩⟩

def p5_236 : PointBox := ⟨⟨835708009084479018704651136310,835708009084479018705746287900⟩,⟨⟨538066143175365379387081577636,538066143175365379406868098410⟩,⟨1124165463172122097071896934517,1124165463172122097114709479205⟩⟩,⟨⟨(-1298074465552210042897063778852),(-1298074465552210042892594728988)⟩,⟨221305265208241839448750088941,221305265208241839450074949400⟩⟩,⟨⟨(-869731401688505764278067489532),(-869731401688505764260467090900)⟩,⟨(-493525368058164799972315703854),(-493525368058164799955373333378)⟩⟩,⟨⟨440219371297876868096803574636,440219371297876868103869207577⟩,⟨(-715940127755911859285035234408),(-715940127755911859277045251485)⟩⟩⟩

def p5_237 : PointBox := ⟨⟨835471718101202011622850191989,835471718101202011623947543496⟩,⟨⟨538313778222961685984252468909,538313778222961686004050605920⟩,⟨1124364842923718060194751250647,1124364842923718060237580008097⟩⟩,⟨⟨(-1298304689458719822949314947874),(-1298304689458719822944835152313)⟩,⟨221591209531022866253761058825,221591209531022866255089427159⟩⟩,⟨⟨(-869364803392797692969220664116),(-869364803392797692951611912894)⟩,⟨(-494170859745697887640160420633),(-494170859745697887623210675630)⟩⟩,⟨⟨439991085287052493594943619022,439991085287052493602019514091⟩,⟨(-715858929631630706079451670064),(-715858929631630706071451030346)⟩⟩⟩

def p5_238 : PointBox := ⟨⟨835247654778520470708923238364,835247654778520470710021107998⟩,⟨⟨538548744445161118193138956572,538548744445161118212946472247⟩,⟨1124553939454343944119956188157,1124553939454343944162794781475⟩⟩,⟨⟨(-1298523039324439179742854460266),(-1298523039324439179738370871080)⟩,⟨221862525154297489467698701566,221862525154297489469028500800⟩⟩,⟨⟨(-869016733416616256201901119594),(-869016733416616256184291800977)⟩,⟨(-494782696789119450601073951487),(-494782696789119450584124290828)⟩⟩,⟨⟨439774593134578029583223966148,439774593134578029590304036139⟩,⟨(-715781831103131494521488542302),(-715781831103131494513483986823)⟩⟩⟩

def p5_239 : PointBox := ⟨⟨835035852859546622129469293763,835035852859546622130569152676⟩,⟨⟨538770983273815388984051374959,538770983273815389003869335514⟩,⟨1124732718785067403513473929145,1124732718785067403556327128300⟩⟩,⟨⟨(-1298729475913876640568317883515),(-1298729475913876640563824580137)⟩,⟨222119144449393350181542147353,222119144449393350182875117742⟩⟩,⟨⟨(-868687314954892123223348520337),(-868687314954892123205731639497)⟩,⟨(-495360826909496403051666724812),(-495360826909496403034710380710)⟩⟩,⟨⟨439569930615083763214036184219,439569930615083763221125522932⟩,⟨(-715708860054179021918587321541),(-715708860054179021910573137590)⟩⟩⟩

def p5_240 : PointBox := ⟨⟨834836344240870394660011735654,834836344240870394661110501335⟩,⟨⟨538980439241139139595308433002,538980439241139139615133123000⟩,⟨1124901148783527912022731481275,1124901148783527912065587943609⟩⟩,⟨⟨(-1298923962123778206250160540432),(-1298923962123778206245670206261)⟩,⟨222361003367628831928412585828,222361003367628831929744948470⟩⟩,⟨⟨(-868376664656224929263767071032),(-868376664656224929246156979864)⟩,⟨(-495905200900868021716742446107),(-495905200900868021699793197142)⟩⟩,⟨⟨439377131542244317676690842588,439377131542244317683778384798⟩,⟨(-715640042910783574371736206342),(-715640042910783574363724677160)⟩⟩⟩

def p5_241 : PointBox := ⟨⟨834649158967755910566594085602,834649158967755910567694624492⟩,⟨⟨539177060005617933816463214170,539177060005617933836297161481⟩,⟨1125059199170990675979916675472,1125059199170990676022786107388⟩⟩,⟨⟨(-1299106462991272509097608564782),(-1299106462991272509093109576644)⟩,⟨222588041470229035630740899050,222588041470229035632076086286⟩⟩,⟨⟨(-868084892572074219015474445347),(-868084892572074218997857605187)⟩,⟨(-496415772602090436878648352622),(-496415772602090436861693132986)⟩⟩,⟨⟨439196227764156978800863064667,439196227764156978807958857160⟩,⟨(-715575404625757534834259924676),(-715575404625757534826239821797)⟩⟩⟩

def p5_242 : PointBox := ⟨⟨834474325229616779344144217986,834474325229616779345244861521⟩,⟨⟨539360796376506892185232067446,539360796376506892205073035402⟩,⟨1125206841528985809206463969466,1125206841528985809249340025267⟩⟩,⟨⟨(-1299276945701537071625706869295),(-1299276945701537071621206138245)⟩,⟨222800201956614365697017794330,222800201956614365698353738855⟩⟩,⟨⟨(-867812102108865548652808086168),(-867812102108865548635192219421)⟩,⟨(-496892498870119707493750645144),(-496892498870119707476796852219)⟩⟩,⟨⟨439027249159013400094493942019,439027249159013400101591933326⟩,⟨(-715514968664117396270812328144),(-715514968664117396262790350191)⟩⟩⟩

def p5_243 : PointBox := ⟨⟨834311869355770875715687658728,834311869355770875716789857066⟩,⟨⟨539531602336899535953735671704,539531602336899535973584699143⟩,⟨1125344049305532625366202019429,1125344049305532625409089394486⟩⟩,⟨⟨(-1299435379594985500286602630247),(-1299435379594985500282094317156)⟩,⟨222997431691038136569399309452,222997431691038136570737728027⟩⟩,⟨⟨(-867558389983025432608031308413),(-867558389983025432590409513667)⟩,⟨(-497335339554772396166590761745),(-497335339554772396149631718496)⟩⟩,⟨⟨438870223631060970515937670766,438870223631060970523042883631⟩,⟨(-715458756989342490456228915152),(-715458756989342490448199429155)⟩⟩⟩

def p5_244 : PointBox := ⟨⟨834161815811475241207264238598,834161815811475241208365273929⟩,⟨⟨539689435065347559676892404264,539689435065347559696746145310⟩,⟨1125470797820948946206406157692,1125470797820948946249294782235⟩⟩,⟨⟨(-1299581736173975496823038523260),(-1299581736173975496818533837328)⟩,⟨223179681227550935771161619700,223179681227550935772499167770⟩⟩,⟨⟨(-867323846178957873187973924761),(-867323846178957873170358844532)⟩,⟨(-497744257475000330415984021331),(-497744257475000330399031859671)⟩⟩,⟨⟨438725177106850301095033487129,438725177106850301102136137010⟩,⟨(-715406790050501082664095632733),(-715406790050501082656069492561)⟩⟩⟩

def p5_245 : PointBox := ⟨⟨834024187194241706427753798690,834024187194241706428856165695⟩,⟨⟨539834254956013424439264721626,539834254956013424459125311423⟩,⟨1125587064273245359874637115185,1125587064273245359917535384521⟩⟩,⟨⟨(-1299715989109037611251031320676),(-1299715989109037611246520148558)⟩,⟨223346904833270834155478611549,223346904833270834156818275079⟩⟩,⟨⟨(-867108553909974280108806073231),(-867108553909974280091185906025)⟩,⟨(-498119218396713968435527060446),(-498119218396713968418570387891)⟩⟩,⟨⟨438592133531765469627942575105,438592133531765469635051397013⟩,⟨(-715359086770253813216164158275),(-715359086770253813208131597868)⟩⟩⟩

def p5_246 : PointBox := ⟨⟨833899004230433788907376904671,833899004230433788908478953794⟩,⟨⟨539966025637338859648699505838,539966025637338859668564717873⟩,⟨1125692827743104393601040291130,1125692827743104393643941915179⟩⟩,⟨⟨(-1299838114244624695236729470392),(-1299838114244624695232218655118)⟩,⟨223499060509939914977272413429,223499060509939914978612143435⟩⟩,⟨⟨(-866912589582187672272301225478),(-866912589582187672254683603836)⟩,⟨(-498460191012186482889768459043),(-498460191012186482872814585735)⟩⟩,⟨⟨438471114866833856454871819041,438471114866833856461980820643⟩,⟨(-715315664533743789182271373137),(-715315664533743789174239023310)⟩⟩⟩

def p5_247 : PointBox := ⟨⟨833786285772145378989503141712,833786285772145378990606296459⟩,⟨⟨540084713989213578528570707885,540084713989213578548441548979⟩,⟨1125788069198444589706328661714,1125788069198444589749238241232⟩⟩,⟨⟨(-1299948089604382043120102597322),(-1299948089604382043115586405525)⟩,⟨223636110013748998915386172490,223636110013748998916727654838⟩⟩,⟨⟨(-866736022761381154683815033131),(-866736022761381154666193176894)⟩,⟨(-498767146921068337691623180407),(-498767146921068337674665546629)⟩⟩,⟨⟨438362141085812608138832355865,438362141085812608145946467880⟩,⟨(-715276539178381944027424115264),(-715276539178381944019386445974)⟩⟩⟩

def p5_248 : PointBox := ⟨⟨833686048794361683834223919320,833686048794361683835325113976⟩,⟨⟨540190290158629749442231146237,540190290158629749462103894346⟩,⟨1125872771498569493472577535961,1125872771498569493515483754737⟩⟩,⟨⟨(-1300045895395938230443016704654),(-1300045895395938230438507781594)⟩,⟨223758018873413870538971101108,223758018873413870540310562442⟩⟩,⟨⟨(-866578916142859778343442524352),(-866578916142859778325830708088)⟩,⟨(-499040060613039762693371292140),(-499040060613039762676423599313)⟩⟩,⟨⟨438265230172548979025208584662,438265230172548979032316775432⟩,⟨(-715241724984535590289809330658),(-715241724984535590281778581825)⟩⟩⟩

def p5_249 : PointBox := ⟨⟨833598308392402857085047937688,833598308392402857086150007374⟩,⟨⟨540282727573809020455723697067,540282727573809020475600844195⟩,⟨1125946919397901576251734831346,1125946919397901576294647294939⟩⟩,⟨⟨(-1300131514015216676972971210186),(-1300131514015216676968458042152)⟩,⟨223864756406487761175745998648,223864756406487761177086842034⟩⟩,⟨⟨(-866441325524294019205334347451),(-866441325524294019187719168825)⟩,⟨(-499278909452126132334515157171),(-499278909452126132317564473267)⟩⟩,⟨⟨438180398118612022479033256727,438180398118612022486145477228⟩,⟨(-715211234667127391036680363631),(-715211234667127391028645416622)⟩⟩⟩

def p5_250 : PointBox := ⟨⟨833523077779650699178724156614,833523077779650699179825479951⟩,⟨⟨540362002956790166529320832631,540362002956790166549200175346⟩,⟨1126010499549301127659347936275,1126010499549301127702260446799⟩⟩,⟨⟨(-1300204930050267973305933105292),(-1300204930050267973301422426277)⟩,⟨223956295733896311900996029921,223956295733896311902336237536⟩⟩,⟨⟨(-866323299781562252826904553887),(-866323299781562252809293512723)⟩,⟨(-499483673662698829084609538995),(-499483673662698829067663045957)⟩⟩,⟨⟨438107658921193333352960214465,438107658921193333360070567154⟩,⟨(-715185079368151270480153895092),(-715185079368151270472121273943)⟩⟩⟩

def p5_251 : PointBox := ⟨⟨833460368285558770648725120653,833460368285558770649827085556⟩,⟨⟨540428096334466715837101338080,540428096334466715856983843182⟩,⟨1126063500506970157196607538170,1126063500506970157239524570219⟩⟩,⟨⟨(-1300266130284623017632784323383),(-1300266130284623017628270543397)⟩,⟨224032613792682726591216956676,224032613792682726592558172166⟩⟩,⟨⟨(-866224880847598753012443322326),(-866224880847598752994829802869)⟩,⟨(-499654336317181723578589298184),(-499654336317181723561640594941)⟩⟩,⟨⟨438047024581274780195997660063,438047024581274780203110950975⟩,⟨(-715163268650111073341552846227),(-715163268650111073333517160028)⟩⟩⟩

def p5_252 : PointBox := ⟨⟨833410189353946218092043254935,833410189353946218093143120302⟩,⟨⟨540480991048065212333061129749,540480991048065212352943411297⟩,⟨1126105912728941348567309437155,1126105912728941348610220818038⟩⟩,⟨⟨(-1300315103700167012629059099898),(-1300315103700167012624553541801)⟩,⟨224093691346952326812103205620,224093691346952326813442047184⟩⟩,⟨⟨(-866146103694252904447724411912),(-866146103694252904430121166228)⟩,⟨(-499790883325480933260773499248),(-499790883325480933243834821557)⟩⟩,⟨⟨437998505102061409117380772854,437998505102061409124487118965⟩,⟨(-715145810490387066929870054458),(-715145810490387066921842263131)⟩⟩⟩

def p5_253 : PointBox := ⟨⟨833372548541575569742801960210,833372548541575569743902229691⟩,⟨⟨540520673761056084174748561955,540520673761056084194632762101⟩,⟨1126137728579152109723799552918,1126137728579152109766713715301⟩⟩,⟨⟨(-1300351841479534372159689816699),(-1300351841479534372155182319441)⟩,⟨224139512997007235846366978033,224139512997007235847706447695⟩⟩,⟨⟨(-866086996317164489846584107242),(-866086996317164489828979285151)⟩,⟨(-499893303426153032743584047824),(-499893303426153032726643957907)⟩⟩,⟨⟨437962108487677950299844767797,437962108487677950306952945109⟩,⟨(-715132711276534660049545860778),(-715132711276534660041516154465)⟩⟩⟩

def p5_254 : PointBox := ⟨⟨833347451517014714831470009390,833347451517014714832569096682⟩,⟨⟨540547134465490410323712650277,540547134465490410343596599222⟩,⟨1126158942329103758717134550744,1126158942329103758760045417408⟩⟩,⟨⟨(-1300376337008024584073382078092),(-1300376337008024584068879234950)⟩,⟨224170067186663446498859472661,224170067186663446500197593832⟩⟩,⟨⟨(-866047579723659090278514376450),(-866047579723659090260915312833)⟩,⟨(-499961588179324384570289106695),(-499961588179324384553354627572)⟩⟩,⟨⟨437937840742127612128348354754,437937840742127612135452587940⟩,⟨(-715123975802518989376182826077),(-715123975802518989368157592166)⟩⟩⟩

def p5_255 : PointBox := ⟨⟨833334902059783238111366637638,833334902059783238112465888317⟩,⟨⟨540560366486757208890486673710,540560366486757208910371292585⟩,⟨1126169550159105880179481653731,1126169550159105880222393549411⟩⟩,⟨⟨(-1300388585875039069302844489499),(-1300388585875039069298340882461)⟩,⟨224185346208744064509748789598,224185346208744064511087155059⟩⟩,⟨⟨(-866027867923666821886981771508),(-866027867923666821869382047953)⟩,⟨(-499995731961371741283336895461),(-499995731961371741266401816199)⟩⟩,⟨⟨437925705868512105966363175730,437925705868512105973468121377⟩,⟨(-715119607265888297440173929404),(-715119607265888297432147943564)⟩⟩⟩

def row5_0 : Fin 16 → PointBox := ![p5_0,p5_1,p5_2,p5_3,p5_4,p5_5,p5_6,p5_7,p5_8,p5_9,p5_10,p5_11,p5_12,p5_13,p5_14,p5_15]
def row5_1 : Fin 16 → PointBox := ![p5_16,p5_17,p5_18,p5_19,p5_20,p5_21,p5_22,p5_23,p5_24,p5_25,p5_26,p5_27,p5_28,p5_29,p5_30,p5_31]
def row5_2 : Fin 16 → PointBox := ![p5_32,p5_33,p5_34,p5_35,p5_36,p5_37,p5_38,p5_39,p5_40,p5_41,p5_42,p5_43,p5_44,p5_45,p5_46,p5_47]
def row5_3 : Fin 16 → PointBox := ![p5_48,p5_49,p5_50,p5_51,p5_52,p5_53,p5_54,p5_55,p5_56,p5_57,p5_58,p5_59,p5_60,p5_61,p5_62,p5_63]
def row5_4 : Fin 16 → PointBox := ![p5_64,p5_65,p5_66,p5_67,p5_68,p5_69,p5_70,p5_71,p5_72,p5_73,p5_74,p5_75,p5_76,p5_77,p5_78,p5_79]
def row5_5 : Fin 16 → PointBox := ![p5_80,p5_81,p5_82,p5_83,p5_84,p5_85,p5_86,p5_87,p5_88,p5_89,p5_90,p5_91,p5_92,p5_93,p5_94,p5_95]
def row5_6 : Fin 16 → PointBox := ![p5_96,p5_97,p5_98,p5_99,p5_100,p5_101,p5_102,p5_103,p5_104,p5_105,p5_106,p5_107,p5_108,p5_109,p5_110,p5_111]
def row5_7 : Fin 16 → PointBox := ![p5_112,p5_113,p5_114,p5_115,p5_116,p5_117,p5_118,p5_119,p5_120,p5_121,p5_122,p5_123,p5_124,p5_125,p5_126,p5_127]
def row5_8 : Fin 16 → PointBox := ![p5_128,p5_129,p5_130,p5_131,p5_132,p5_133,p5_134,p5_135,p5_136,p5_137,p5_138,p5_139,p5_140,p5_141,p5_142,p5_143]
def row5_9 : Fin 16 → PointBox := ![p5_144,p5_145,p5_146,p5_147,p5_148,p5_149,p5_150,p5_151,p5_152,p5_153,p5_154,p5_155,p5_156,p5_157,p5_158,p5_159]
def row5_10 : Fin 16 → PointBox := ![p5_160,p5_161,p5_162,p5_163,p5_164,p5_165,p5_166,p5_167,p5_168,p5_169,p5_170,p5_171,p5_172,p5_173,p5_174,p5_175]
def row5_11 : Fin 16 → PointBox := ![p5_176,p5_177,p5_178,p5_179,p5_180,p5_181,p5_182,p5_183,p5_184,p5_185,p5_186,p5_187,p5_188,p5_189,p5_190,p5_191]
def row5_12 : Fin 16 → PointBox := ![p5_192,p5_193,p5_194,p5_195,p5_196,p5_197,p5_198,p5_199,p5_200,p5_201,p5_202,p5_203,p5_204,p5_205,p5_206,p5_207]
def row5_13 : Fin 16 → PointBox := ![p5_208,p5_209,p5_210,p5_211,p5_212,p5_213,p5_214,p5_215,p5_216,p5_217,p5_218,p5_219,p5_220,p5_221,p5_222,p5_223]
def row5_14 : Fin 16 → PointBox := ![p5_224,p5_225,p5_226,p5_227,p5_228,p5_229,p5_230,p5_231,p5_232,p5_233,p5_234,p5_235,p5_236,p5_237,p5_238,p5_239]
def row5_15 : Fin 16 → PointBox := ![p5_240,p5_241,p5_242,p5_243,p5_244,p5_245,p5_246,p5_247,p5_248,p5_249,p5_250,p5_251,p5_252,p5_253,p5_254,p5_255]
def row5 : Fin 16 → Fin 16 → PointBox := ![row5_0,row5_1,row5_2,row5_3,row5_4,row5_5,row5_6,row5_7,row5_8,row5_9,row5_10,row5_11,row5_12,row5_13,row5_14,row5_15]
end SharpPlanar.IntegerGrid

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Amplitudes
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
noncomputable def amp1_11 : Fin 16 → Fin 16 → CBox := ![amp1_11_0,amp1_11_1,amp1_11_2,amp1_11_3,amp1_11_4,amp1_11_5,amp1_11_6,amp1_11_7,amp1_11_8,amp1_11_9,amp1_11_10,amp1_11_11,amp1_11_12,amp1_11_13,amp1_11_14,amp1_11_15]
noncomputable def amp1_15 : Fin 16 → Fin 16 → CBox := ![amp1_15_0,amp1_15_1,amp1_15_2,amp1_15_3,amp1_15_4,amp1_15_5,amp1_15_6,amp1_15_7,amp1_15_8,amp1_15_9,amp1_15_10,amp1_15_11,amp1_15_12,amp1_15_13,amp1_15_14,amp1_15_15]
noncomputable def amp1_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![amp1_10,amp1_11,amp1_12,amp1_13,amp1_14,amp1_15]
noncomputable def amp4_01 : Fin 16 → Fin 16 → CBox := ![amp4_01_0,amp4_01_1,amp4_01_2,amp4_01_3,amp4_01_4,amp4_01_5,amp4_01_6,amp4_01_7,amp4_01_8,amp4_01_9,amp4_01_10,amp4_01_11,amp4_01_12,amp4_01_13,amp4_01_14,amp4_01_15]
noncomputable def amp4_05 : Fin 16 → Fin 16 → CBox := ![amp4_05_0,amp4_05_1,amp4_05_2,amp4_05_3,amp4_05_4,amp4_05_5,amp4_05_6,amp4_05_7,amp4_05_8,amp4_05_9,amp4_05_10,amp4_05_11,amp4_05_12,amp4_05_13,amp4_05_14,amp4_05_15]
noncomputable def amp4_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![amp4_00,amp4_01,amp4_02,amp4_03,amp4_04,amp4_05]
noncomputable def amp7_12 : Fin 16 → Fin 16 → CBox := ![amp7_12_0,amp7_12_1,amp7_12_2,amp7_12_3,amp7_12_4,amp7_12_5,amp7_12_6,amp7_12_7,amp7_12_8,amp7_12_9,amp7_12_10,amp7_12_11,amp7_12_12,amp7_12_13,amp7_12_14,amp7_12_15]
noncomputable def amp7_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![amp7_10,amp7_11,amp7_12,amp7_13,amp7_14,amp7_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_AtomKernels
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
open IntegerIntervals IntegerBasis IntegerGrid
noncomputable def atomPoint0 : PointBox := ⟨⟨0,0⟩,⟨⟨2886751345948128822491487805010,2886751345948128822591487805032⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨2933333333333333333333333333333,2933333333333333333333333333334⟩⟩,⟨⟨999999999999999999999999999989,1000000000000000000000000000015⟩,⟨(-15),15⟩⟩,⟨⟨99875126068614995128859923084,99875126068614995129850328303⟩,⟨(-2),2⟩⟩⟩
noncomputable def atomPoint1 : PointBox := ⟨⟨166666666666666666666666666666,166666666666666666666666666667⟩,⟨⟨2459717123174736984844818011358,2459717123174736984930025111996⟩,⟨1024882134656140410352007504727,1024882134656140410387510463337⟩⟩,⟨⟨(-1183431952662721893491124260363),(-1183431952662721893491124260348)⟩,⟨2440236686390532544378698224848,2440236686390532544378698224864⟩⟩,⟨⟨866025403784438646763098939526,866025403784438646763954632529⟩,⟨(-500000000000000000001210408427),(-499999999999999999999469888220)⟩⟩,⟨⟨88011921021907828079523012267,88011921021907828081313061486⟩,⟨(-117881300351469008776578899699),(-117881300351469008774941580239)⟩⟩⟩
noncomputable def atomPoint2 : PointBox := ⟨⟨333333333333333333333333333333,333333333333333333333333333334⟩,⟨⟨1703656532034961272290058376722,1703656532034961272349074770188⟩,⟨1419713776695801060241715313933,1419713776695801060290895641830⟩⟩,⟨⟨(-1639344262295081967213114754110),(-1639344262295081967213114754090)⟩,⟨1567213114754098360655737704910,1567213114754098360655737704927⟩⟩,⟨⟨499999999999999999997708137538,500000000000000000000931269165⟩,⟨(-866025403784438646766051325440),(-866025403784438646762180554973)⟩⟩,⟨⟨81619205305569481307151807559,81619205305569481310396378569⟩,⟨(-280396055793447804630865756591),(-280396055793447804627615754177)⟩⟩⟩
noncomputable def atomPoint3 : PointBox := ⟨⟨500000000000000000000000000000,500000000000000000000000000000⟩,⟨⟨1126537110613903930728385484882,1126537110613903930767409875134⟩,⟨1408171388267379913410481856103,1408171388267379913459262343918⟩⟩,⟨⟨(-1626016260162601626016260162603),(-1626016260162601626016260162601)⟩,⟨900813008130081300813008130080,900813008130081300813008130083⟩⟩,⟨⟨(-4444983321),2088366603⟩,⟨(-1000000000000000000003266674962),(-999999999999999999996733325039)⟩⟩,⟨⟨142697957066396950735325887717,142697957066396950739297566444⟩,⟨(-471767338116830861279282785979),(-471767338116830861275221116079)⟩⟩⟩
noncomputable def atomPoint4 : PointBox := ⟨⟨666666666666666666666666666666,666666666666666666666666666667⟩,⟨⟨764140062162739982424217360149,764140062162739982450687948391⟩,⟨1273566770271233304040362266913,1273566770271233304084479913987⟩⟩,⟨⟨(-1470588235294117647058823529418),(-1470588235294117647058823529408)⟩,⟨482352941176470588235294117645,482352941176470588235294117651⟩⟩,⟨⟨(-500000000000000000006328835244),(-499999999999999999996392351351)⟩,⟨(-866025403784438646767669145432),(-866025403784438646758206118258)⟩⟩,⟨⟨276546840654658619933702465609,276546840654658619937500463543⟩,⟨(-626318886933968865987490837754),(-626318886933968865983439240032)⟩⟩⟩
noncomputable def atomPoint5 : PointBox := ⟨⟨833333333333333333333333333333,833333333333333333333333333334⟩,⟨⟨540562020567660013574478860754,540562020567660013593204478445⟩,⟨1126170876182625028280164293239,1126170876182625028319175996763⟩⟩,⟨⟨(-1300390117035110533159947984400),(-1300390117035110533159947984390)⟩,⟨224187256176853055916775032508,224187256176853055916775032512⟩⟩,⟨⟨(-866025403784438646770926677365),(-866025403784438646758483511404)⟩,⟨(-500000000000000000004285885012),(-499999999999999999992312631744)⟩⟩,⟨⟨437924188962394509423764780759,437924188962394509426958319345⟩,⟨(-715119061161322533370337011021),(-715119061161322533366664758504)⟩⟩⟩
noncomputable def atomPoint6 : PointBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨⟨398172599441121216895377628277,398172599441121216909170731728⟩,⟨995431498602803042238444070694,995431498602803042272926829319⟩⟩,⟨⟨(-1149425287356321839080459770116),(-1149425287356321839080459770114)⟩,⟨59770114942528735632183908045,59770114942528735632183908047⟩⟩,⟨⟨(-1000000000000000000006553197785),(-999999999999999999993446802219)⟩,⟨(-4196581061),8909814505⟩⟩,⟨⟨591041363234240777970266834369,591041363234240777972775244344⟩,⟨(-749036735415657815476580310485),(-749036735415657815473358766432)⟩⟩⟩
noncomputable def atomPoints : Fin 7 → PointBox := ![atomPoint0,atomPoint1,atomPoint2,atomPoint3,atomPoint4,atomPoint5,atomPoint6]
lemma atomKernel0_0_eq (j : Fin 7) : atomKernel0_0 j = kernel0Box (atomPoints j) 0 := by
  fin_cases j <;> decide +kernel
lemma atomKernel1_0_eq (j : Fin 7) : atomKernel1_0 j = kernel0Box (atomPoints j) 1 := by
  fin_cases j <;> decide +kernel
lemma atomKernel1_1_eq (j : Fin 7) : atomKernel1_1 j = (kernel0Box (atomPoints j) 1).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel3_0_eq (j : Fin 7) : atomKernel3_0 j = kernel0Box (atomPoints j) 3 := by
  fin_cases j <;> decide +kernel
lemma atomKernel3_1_eq (j : Fin 7) : atomKernel3_1 j = (kernel0Box (atomPoints j) 3).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel4_0_eq (j : Fin 7) : atomKernel4_0 j = kernel0Box (atomPoints j) 4 := by
  fin_cases j <;> decide +kernel
lemma atomKernel4_1_eq (j : Fin 7) : atomKernel4_1 j = (kernel0Box (atomPoints j) 4).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel7_0_eq (j : Fin 7) : atomKernel7_0 j = kernel0Box (atomPoints j) 7 := by
  fin_cases j <;> decide +kernel
lemma atomKernel7_1_eq (j : Fin 7) : atomKernel7_1 j = (kernel0Box (atomPoints j) 7).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel9_0_eq (j : Fin 7) : atomKernel9_0 j = kernel0Box (atomPoints j) 9 := by
  fin_cases j <;> decide +kernel
lemma atomKernel9_1_eq (j : Fin 7) : atomKernel9_1 j = (kernel0Box (atomPoints j) 9).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel12_0_eq (j : Fin 7) : atomKernel12_0 j = kernel0Box (atomPoints j) 12 := by
  fin_cases j <;> decide +kernel
lemma atomKernel12_1_eq (j : Fin 7) : atomKernel12_1 j = (kernel0Box (atomPoints j) 12).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel13_0_eq (j : Fin 7) : atomKernel13_0 j = kernel0Box (atomPoints j) 13 := by
  fin_cases j <;> decide +kernel
lemma atomKernel13_1_eq (j : Fin 7) : atomKernel13_1 j = (kernel0Box (atomPoints j) 13).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel15_0_eq (j : Fin 7) : atomKernel15_0 j = kernel0Box (atomPoints j) 15 := by
  fin_cases j <;> decide +kernel
lemma atomKernel15_1_eq (j : Fin 7) : atomKernel15_1 j = (kernel0Box (atomPoints j) 15).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel16_0_eq (j : Fin 7) : atomKernel16_0 j = kernel0Box (atomPoints j) 16 := by
  fin_cases j <;> decide +kernel
lemma atomKernel16_1_eq (j : Fin 7) : atomKernel16_1 j = (kernel0Box (atomPoints j) 16).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel19_0_eq (j : Fin 7) : atomKernel19_0 j = kernel0Box (atomPoints j) 19 := by
  fin_cases j <;> decide +kernel
lemma atomKernel19_1_eq (j : Fin 7) : atomKernel19_1 j = (kernel0Box (atomPoints j) 19).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel21_0_eq (j : Fin 7) : atomKernel21_0 j = kernel0Box (atomPoints j) 21 := by
  fin_cases j <;> decide +kernel
lemma atomKernel21_1_eq (j : Fin 7) : atomKernel21_1 j = (kernel0Box (atomPoints j) 21).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel24_0_eq (j : Fin 7) : atomKernel24_0 j = kernel0Box (atomPoints j) 24 := by
  fin_cases j <;> decide +kernel
lemma atomKernel24_1_eq (j : Fin 7) : atomKernel24_1 j = (kernel0Box (atomPoints j) 24).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel25_0_eq (j : Fin 7) : atomKernel25_0 j = kernel0Box (atomPoints j) 25 := by
  fin_cases j <;> decide +kernel
lemma atomKernel25_1_eq (j : Fin 7) : atomKernel25_1 j = (kernel0Box (atomPoints j) 25).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel27_0_eq (j : Fin 7) : atomKernel27_0 j = kernel0Box (atomPoints j) 27 := by
  fin_cases j <;> decide +kernel
lemma atomKernel27_1_eq (j : Fin 7) : atomKernel27_1 j = (kernel0Box (atomPoints j) 27).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel28_0_eq (j : Fin 7) : atomKernel28_0 j = kernel0Box (atomPoints j) 28 := by
  fin_cases j <;> decide +kernel
lemma atomKernel28_1_eq (j : Fin 7) : atomKernel28_1 j = (kernel0Box (atomPoints j) 28).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel31_0_eq (j : Fin 7) : atomKernel31_0 j = kernel0Box (atomPoints j) 31 := by
  fin_cases j <;> decide +kernel
lemma atomKernel31_1_eq (j : Fin 7) : atomKernel31_1 j = (kernel0Box (atomPoints j) 31).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel33_0_eq (j : Fin 7) : atomKernel33_0 j = kernel0Box (atomPoints j) 33 := by
  fin_cases j <;> decide +kernel
lemma atomKernel33_1_eq (j : Fin 7) : atomKernel33_1 j = (kernel0Box (atomPoints j) 33).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel36_0_eq (j : Fin 7) : atomKernel36_0 j = kernel0Box (atomPoints j) 36 := by
  fin_cases j <;> decide +kernel
lemma atomKernel36_1_eq (j : Fin 7) : atomKernel36_1 j = (kernel0Box (atomPoints j) 36).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel37_0_eq (j : Fin 7) : atomKernel37_0 j = kernel0Box (atomPoints j) 37 := by
  fin_cases j <;> decide +kernel
lemma atomKernel37_1_eq (j : Fin 7) : atomKernel37_1 j = (kernel0Box (atomPoints j) 37).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel39_0_eq (j : Fin 7) : atomKernel39_0 j = kernel0Box (atomPoints j) 39 := by
  fin_cases j <;> decide +kernel
lemma atomKernel39_1_eq (j : Fin 7) : atomKernel39_1 j = (kernel0Box (atomPoints j) 39).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel40_0_eq (j : Fin 7) : atomKernel40_0 j = kernel0Box (atomPoints j) 40 := by
  fin_cases j <;> decide +kernel
lemma atomKernel40_1_eq (j : Fin 7) : atomKernel40_1 j = (kernel0Box (atomPoints j) 40).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel43_0_eq (j : Fin 7) : atomKernel43_0 j = kernel0Box (atomPoints j) 43 := by
  fin_cases j <;> decide +kernel
lemma atomKernel43_1_eq (j : Fin 7) : atomKernel43_1 j = (kernel0Box (atomPoints j) 43).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel45_0_eq (j : Fin 7) : atomKernel45_0 j = kernel0Box (atomPoints j) 45 := by
  fin_cases j <;> decide +kernel
lemma atomKernel45_1_eq (j : Fin 7) : atomKernel45_1 j = (kernel0Box (atomPoints j) 45).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel48_0_eq (j : Fin 7) : atomKernel48_0 j = kernel0Box (atomPoints j) 48 := by
  fin_cases j <;> decide +kernel
lemma atomKernel48_1_eq (j : Fin 7) : atomKernel48_1 j = (kernel0Box (atomPoints j) 48).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel49_0_eq (j : Fin 7) : atomKernel49_0 j = kernel0Box (atomPoints j) 49 := by
  fin_cases j <;> decide +kernel
lemma atomKernel49_1_eq (j : Fin 7) : atomKernel49_1 j = (kernel0Box (atomPoints j) 49).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel51_0_eq (j : Fin 7) : atomKernel51_0 j = kernel0Box (atomPoints j) 51 := by
  fin_cases j <;> decide +kernel
lemma atomKernel51_1_eq (j : Fin 7) : atomKernel51_1 j = (kernel0Box (atomPoints j) 51).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel52_0_eq (j : Fin 7) : atomKernel52_0 j = kernel0Box (atomPoints j) 52 := by
  fin_cases j <;> decide +kernel
lemma atomKernel52_1_eq (j : Fin 7) : atomKernel52_1 j = (kernel0Box (atomPoints j) 52).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel55_0_eq (j : Fin 7) : atomKernel55_0 j = kernel0Box (atomPoints j) 55 := by
  fin_cases j <;> decide +kernel
lemma atomKernel55_1_eq (j : Fin 7) : atomKernel55_1 j = (kernel0Box (atomPoints j) 55).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel57_0_eq (j : Fin 7) : atomKernel57_0 j = kernel0Box (atomPoints j) 57 := by
  fin_cases j <;> decide +kernel
lemma atomKernel57_1_eq (j : Fin 7) : atomKernel57_1 j = (kernel0Box (atomPoints j) 57).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel60_0_eq (j : Fin 7) : atomKernel60_0 j = kernel0Box (atomPoints j) 60 := by
  fin_cases j <;> decide +kernel
lemma atomKernel60_1_eq (j : Fin 7) : atomKernel60_1 j = (kernel0Box (atomPoints j) 60).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel61_0_eq (j : Fin 7) : atomKernel61_0 j = kernel0Box (atomPoints j) 61 := by
  fin_cases j <;> decide +kernel
lemma atomKernel61_1_eq (j : Fin 7) : atomKernel61_1 j = (kernel0Box (atomPoints j) 61).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel63_0_eq (j : Fin 7) : atomKernel63_0 j = kernel0Box (atomPoints j) 63 := by
  fin_cases j <;> decide +kernel
lemma atomKernel63_1_eq (j : Fin 7) : atomKernel63_1 j = (kernel0Box (atomPoints j) 63).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel64_0_eq (j : Fin 7) : atomKernel64_0 j = kernel0Box (atomPoints j) 64 := by
  fin_cases j <;> decide +kernel
lemma atomKernel64_1_eq (j : Fin 7) : atomKernel64_1 j = (kernel0Box (atomPoints j) 64).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel67_0_eq (j : Fin 7) : atomKernel67_0 j = kernel0Box (atomPoints j) 67 := by
  fin_cases j <;> decide +kernel
lemma atomKernel67_1_eq (j : Fin 7) : atomKernel67_1 j = (kernel0Box (atomPoints j) 67).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel69_0_eq (j : Fin 7) : atomKernel69_0 j = kernel0Box (atomPoints j) 69 := by
  fin_cases j <;> decide +kernel
lemma atomKernel69_1_eq (j : Fin 7) : atomKernel69_1 j = (kernel0Box (atomPoints j) 69).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel72_0_eq (j : Fin 7) : atomKernel72_0 j = kernel0Box (atomPoints j) 72 := by
  fin_cases j <;> decide +kernel
lemma atomKernel72_1_eq (j : Fin 7) : atomKernel72_1 j = (kernel0Box (atomPoints j) 72).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel73_0_eq (j : Fin 7) : atomKernel73_0 j = kernel0Box (atomPoints j) 73 := by
  fin_cases j <;> decide +kernel
lemma atomKernel73_1_eq (j : Fin 7) : atomKernel73_1 j = (kernel0Box (atomPoints j) 73).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel75_0_eq (j : Fin 7) : atomKernel75_0 j = kernel0Box (atomPoints j) 75 := by
  fin_cases j <;> decide +kernel
lemma atomKernel75_1_eq (j : Fin 7) : atomKernel75_1 j = (kernel0Box (atomPoints j) 75).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel76_0_eq (j : Fin 7) : atomKernel76_0 j = kernel0Box (atomPoints j) 76 := by
  fin_cases j <;> decide +kernel
lemma atomKernel76_1_eq (j : Fin 7) : atomKernel76_1 j = (kernel0Box (atomPoints j) 76).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel79_0_eq (j : Fin 7) : atomKernel79_0 j = kernel0Box (atomPoints j) 79 := by
  fin_cases j <;> decide +kernel
lemma atomKernel79_1_eq (j : Fin 7) : atomKernel79_1 j = (kernel0Box (atomPoints j) 79).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel81_0_eq (j : Fin 7) : atomKernel81_0 j = kernel0Box (atomPoints j) 81 := by
  fin_cases j <;> decide +kernel
lemma atomKernel81_1_eq (j : Fin 7) : atomKernel81_1 j = (kernel0Box (atomPoints j) 81).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel84_0_eq (j : Fin 7) : atomKernel84_0 j = kernel0Box (atomPoints j) 84 := by
  fin_cases j <;> decide +kernel
lemma atomKernel84_1_eq (j : Fin 7) : atomKernel84_1 j = (kernel0Box (atomPoints j) 84).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel85_0_eq (j : Fin 7) : atomKernel85_0 j = kernel0Box (atomPoints j) 85 := by
  fin_cases j <;> decide +kernel
lemma atomKernel85_1_eq (j : Fin 7) : atomKernel85_1 j = (kernel0Box (atomPoints j) 85).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel87_0_eq (j : Fin 7) : atomKernel87_0 j = kernel0Box (atomPoints j) 87 := by
  fin_cases j <;> decide +kernel
lemma atomKernel87_1_eq (j : Fin 7) : atomKernel87_1 j = (kernel0Box (atomPoints j) 87).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel88_0_eq (j : Fin 7) : atomKernel88_0 j = kernel0Box (atomPoints j) 88 := by
  fin_cases j <;> decide +kernel
lemma atomKernel88_1_eq (j : Fin 7) : atomKernel88_1 j = (kernel0Box (atomPoints j) 88).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel91_0_eq (j : Fin 7) : atomKernel91_0 j = kernel0Box (atomPoints j) 91 := by
  fin_cases j <;> decide +kernel
lemma atomKernel91_1_eq (j : Fin 7) : atomKernel91_1 j = (kernel0Box (atomPoints j) 91).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel93_0_eq (j : Fin 7) : atomKernel93_0 j = kernel0Box (atomPoints j) 93 := by
  fin_cases j <;> decide +kernel
lemma atomKernel93_1_eq (j : Fin 7) : atomKernel93_1 j = (kernel0Box (atomPoints j) 93).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel96_0_eq (j : Fin 7) : atomKernel96_0 j = kernel0Box (atomPoints j) 96 := by
  fin_cases j <;> decide +kernel
lemma atomKernel96_1_eq (j : Fin 7) : atomKernel96_1 j = (kernel0Box (atomPoints j) 96).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel97_0_eq (j : Fin 7) : atomKernel97_0 j = kernel0Box (atomPoints j) 97 := by
  fin_cases j <;> decide +kernel
lemma atomKernel97_1_eq (j : Fin 7) : atomKernel97_1 j = (kernel0Box (atomPoints j) 97).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel99_0_eq (j : Fin 7) : atomKernel99_0 j = kernel0Box (atomPoints j) 99 := by
  fin_cases j <;> decide +kernel
lemma atomKernel99_1_eq (j : Fin 7) : atomKernel99_1 j = (kernel0Box (atomPoints j) 99).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel100_0_eq (j : Fin 7) : atomKernel100_0 j = kernel0Box (atomPoints j) 100 := by
  fin_cases j <;> decide +kernel
lemma atomKernel100_1_eq (j : Fin 7) : atomKernel100_1 j = (kernel0Box (atomPoints j) 100).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers90
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
noncomputable def power82 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power82_r0,power82_r1,power82_r2,power82_r3,power82_r4,power82_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers100
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
noncomputable def power93_r2 : Fin 16 → Fin 16 → CBox := ![power93_r2_0,power93_r2_1,power93_r2_2,power93_r2_3,power93_r2_4,power93_r2_5,power93_r2_6,power93_r2_7,power93_r2_8,power93_r2_9,power93_r2_10,power93_r2_11,power93_r2_12,power93_r2_13,power93_r2_14,power93_r2_15]
noncomputable def power96_r3 : Fin 16 → Fin 16 → CBox := ![power96_r3_0,power96_r3_1,power96_r3_2,power96_r3_3,power96_r3_4,power96_r3_5,power96_r3_6,power96_r3_7,power96_r3_8,power96_r3_9,power96_r3_10,power96_r3_11,power96_r3_12,power96_r3_13,power96_r3_14,power96_r3_15]
noncomputable def power96 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power96_r0,power96_r1,power96_r2,power96_r3,power96_r4,power96_r5]
noncomputable def power99_r5 : Fin 16 → Fin 16 → CBox := ![power99_r5_0,power99_r5_1,power99_r5_2,power99_r5_3,power99_r5_4,power99_r5_5,power99_r5_6,power99_r5_7,power99_r5_8,power99_r5_9,power99_r5_10,power99_r5_11,power99_r5_12,power99_r5_13,power99_r5_14,power99_r5_15]
noncomputable def power99 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power99_r0,power99_r1,power99_r2,power99_r3,power99_r4,power99_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns100
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
noncomputable def column100_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_0 j i k).mul (power100 j i k)
lemma column100_0_r0_0_eq : ∀ k : Fin 16, column100_0Expr 0 0 k = column100_0_r0_0 k := by decide +kernel
lemma column100_0_r0_1_eq : ∀ k : Fin 16, column100_0Expr 0 1 k = column100_0_r0_1 k := by decide +kernel
lemma column100_0_r0_2_eq : ∀ k : Fin 16, column100_0Expr 0 2 k = column100_0_r0_2 k := by decide +kernel
lemma column100_0_r0_3_eq : ∀ k : Fin 16, column100_0Expr 0 3 k = column100_0_r0_3 k := by decide +kernel
lemma column100_0_r0_4_eq : ∀ k : Fin 16, column100_0Expr 0 4 k = column100_0_r0_4 k := by decide +kernel
lemma column100_0_r0_5_eq : ∀ k : Fin 16, column100_0Expr 0 5 k = column100_0_r0_5 k := by decide +kernel
lemma column100_0_r0_6_eq : ∀ k : Fin 16, column100_0Expr 0 6 k = column100_0_r0_6 k := by decide +kernel
lemma column100_0_r0_7_eq : ∀ k : Fin 16, column100_0Expr 0 7 k = column100_0_r0_7 k := by decide +kernel
lemma column100_0_r0_8_eq : ∀ k : Fin 16, column100_0Expr 0 8 k = column100_0_r0_8 k := by decide +kernel
lemma column100_0_r0_9_eq : ∀ k : Fin 16, column100_0Expr 0 9 k = column100_0_r0_9 k := by decide +kernel
lemma column100_0_r0_10_eq : ∀ k : Fin 16, column100_0Expr 0 10 k = column100_0_r0_10 k := by decide +kernel
lemma column100_0_r0_11_eq : ∀ k : Fin 16, column100_0Expr 0 11 k = column100_0_r0_11 k := by decide +kernel
lemma column100_0_r0_12_eq : ∀ k : Fin 16, column100_0Expr 0 12 k = column100_0_r0_12 k := by decide +kernel
lemma column100_0_r0_13_eq : ∀ k : Fin 16, column100_0Expr 0 13 k = column100_0_r0_13 k := by decide +kernel
lemma column100_0_r0_14_eq : ∀ k : Fin 16, column100_0Expr 0 14 k = column100_0_r0_14 k := by decide +kernel
lemma column100_0_r0_15_eq : ∀ k : Fin 16, column100_0Expr 0 15 k = column100_0_r0_15 k := by decide +kernel
lemma column100_0_r0_eq (i k : Fin 16) : column100_0Expr 0 i k = column100_0_r0 i k := by
  fin_cases i
  · exact column100_0_r0_0_eq k
  · exact column100_0_r0_1_eq k
  · exact column100_0_r0_2_eq k
  · exact column100_0_r0_3_eq k
  · exact column100_0_r0_4_eq k
  · exact column100_0_r0_5_eq k
  · exact column100_0_r0_6_eq k
  · exact column100_0_r0_7_eq k
  · exact column100_0_r0_8_eq k
  · exact column100_0_r0_9_eq k
  · exact column100_0_r0_10_eq k
  · exact column100_0_r0_11_eq k
  · exact column100_0_r0_12_eq k
  · exact column100_0_r0_13_eq k
  · exact column100_0_r0_14_eq k
  · exact column100_0_r0_15_eq k
lemma column100_0_r1_0_eq : ∀ k : Fin 16, column100_0Expr 1 0 k = column100_0_r1_0 k := by decide +kernel
lemma column100_0_r1_1_eq : ∀ k : Fin 16, column100_0Expr 1 1 k = column100_0_r1_1 k := by decide +kernel
lemma column100_0_r1_2_eq : ∀ k : Fin 16, column100_0Expr 1 2 k = column100_0_r1_2 k := by decide +kernel
lemma column100_0_r1_3_eq : ∀ k : Fin 16, column100_0Expr 1 3 k = column100_0_r1_3 k := by decide +kernel
lemma column100_0_r1_4_eq : ∀ k : Fin 16, column100_0Expr 1 4 k = column100_0_r1_4 k := by decide +kernel
lemma column100_0_r1_5_eq : ∀ k : Fin 16, column100_0Expr 1 5 k = column100_0_r1_5 k := by decide +kernel
lemma column100_0_r1_6_eq : ∀ k : Fin 16, column100_0Expr 1 6 k = column100_0_r1_6 k := by decide +kernel
lemma column100_0_r1_7_eq : ∀ k : Fin 16, column100_0Expr 1 7 k = column100_0_r1_7 k := by decide +kernel
lemma column100_0_r1_8_eq : ∀ k : Fin 16, column100_0Expr 1 8 k = column100_0_r1_8 k := by decide +kernel
lemma column100_0_r1_9_eq : ∀ k : Fin 16, column100_0Expr 1 9 k = column100_0_r1_9 k := by decide +kernel
lemma column100_0_r1_10_eq : ∀ k : Fin 16, column100_0Expr 1 10 k = column100_0_r1_10 k := by decide +kernel
lemma column100_0_r1_11_eq : ∀ k : Fin 16, column100_0Expr 1 11 k = column100_0_r1_11 k := by decide +kernel
lemma column100_0_r1_12_eq : ∀ k : Fin 16, column100_0Expr 1 12 k = column100_0_r1_12 k := by decide +kernel
lemma column100_0_r1_13_eq : ∀ k : Fin 16, column100_0Expr 1 13 k = column100_0_r1_13 k := by decide +kernel
lemma column100_0_r1_14_eq : ∀ k : Fin 16, column100_0Expr 1 14 k = column100_0_r1_14 k := by decide +kernel
lemma column100_0_r1_15_eq : ∀ k : Fin 16, column100_0Expr 1 15 k = column100_0_r1_15 k := by decide +kernel
lemma column100_0_r1_eq (i k : Fin 16) : column100_0Expr 1 i k = column100_0_r1 i k := by
  fin_cases i
  · exact column100_0_r1_0_eq k
  · exact column100_0_r1_1_eq k
  · exact column100_0_r1_2_eq k
  · exact column100_0_r1_3_eq k
  · exact column100_0_r1_4_eq k
  · exact column100_0_r1_5_eq k
  · exact column100_0_r1_6_eq k
  · exact column100_0_r1_7_eq k
  · exact column100_0_r1_8_eq k
  · exact column100_0_r1_9_eq k
  · exact column100_0_r1_10_eq k
  · exact column100_0_r1_11_eq k
  · exact column100_0_r1_12_eq k
  · exact column100_0_r1_13_eq k
  · exact column100_0_r1_14_eq k
  · exact column100_0_r1_15_eq k
lemma column100_0_r2_0_eq : ∀ k : Fin 16, column100_0Expr 2 0 k = column100_0_r2_0 k := by decide +kernel
lemma column100_0_r2_1_eq : ∀ k : Fin 16, column100_0Expr 2 1 k = column100_0_r2_1 k := by decide +kernel
lemma column100_0_r2_2_eq : ∀ k : Fin 16, column100_0Expr 2 2 k = column100_0_r2_2 k := by decide +kernel
lemma column100_0_r2_3_eq : ∀ k : Fin 16, column100_0Expr 2 3 k = column100_0_r2_3 k := by decide +kernel
lemma column100_0_r2_4_eq : ∀ k : Fin 16, column100_0Expr 2 4 k = column100_0_r2_4 k := by decide +kernel
lemma column100_0_r2_5_eq : ∀ k : Fin 16, column100_0Expr 2 5 k = column100_0_r2_5 k := by decide +kernel
lemma column100_0_r2_6_eq : ∀ k : Fin 16, column100_0Expr 2 6 k = column100_0_r2_6 k := by decide +kernel
lemma column100_0_r2_7_eq : ∀ k : Fin 16, column100_0Expr 2 7 k = column100_0_r2_7 k := by decide +kernel
lemma column100_0_r2_8_eq : ∀ k : Fin 16, column100_0Expr 2 8 k = column100_0_r2_8 k := by decide +kernel
lemma column100_0_r2_9_eq : ∀ k : Fin 16, column100_0Expr 2 9 k = column100_0_r2_9 k := by decide +kernel
lemma column100_0_r2_10_eq : ∀ k : Fin 16, column100_0Expr 2 10 k = column100_0_r2_10 k := by decide +kernel
lemma column100_0_r2_11_eq : ∀ k : Fin 16, column100_0Expr 2 11 k = column100_0_r2_11 k := by decide +kernel
lemma column100_0_r2_12_eq : ∀ k : Fin 16, column100_0Expr 2 12 k = column100_0_r2_12 k := by decide +kernel
lemma column100_0_r2_13_eq : ∀ k : Fin 16, column100_0Expr 2 13 k = column100_0_r2_13 k := by decide +kernel
lemma column100_0_r2_14_eq : ∀ k : Fin 16, column100_0Expr 2 14 k = column100_0_r2_14 k := by decide +kernel
lemma column100_0_r2_15_eq : ∀ k : Fin 16, column100_0Expr 2 15 k = column100_0_r2_15 k := by decide +kernel
lemma column100_0_r2_eq (i k : Fin 16) : column100_0Expr 2 i k = column100_0_r2 i k := by
  fin_cases i
  · exact column100_0_r2_0_eq k
  · exact column100_0_r2_1_eq k
  · exact column100_0_r2_2_eq k
  · exact column100_0_r2_3_eq k
  · exact column100_0_r2_4_eq k
  · exact column100_0_r2_5_eq k
  · exact column100_0_r2_6_eq k
  · exact column100_0_r2_7_eq k
  · exact column100_0_r2_8_eq k
  · exact column100_0_r2_9_eq k
  · exact column100_0_r2_10_eq k
  · exact column100_0_r2_11_eq k
  · exact column100_0_r2_12_eq k
  · exact column100_0_r2_13_eq k
  · exact column100_0_r2_14_eq k
  · exact column100_0_r2_15_eq k
lemma column100_0_r3_0_eq : ∀ k : Fin 16, column100_0Expr 3 0 k = column100_0_r3_0 k := by decide +kernel
lemma column100_0_r3_1_eq : ∀ k : Fin 16, column100_0Expr 3 1 k = column100_0_r3_1 k := by decide +kernel
lemma column100_0_r3_2_eq : ∀ k : Fin 16, column100_0Expr 3 2 k = column100_0_r3_2 k := by decide +kernel
lemma column100_0_r3_3_eq : ∀ k : Fin 16, column100_0Expr 3 3 k = column100_0_r3_3 k := by decide +kernel
lemma column100_0_r3_4_eq : ∀ k : Fin 16, column100_0Expr 3 4 k = column100_0_r3_4 k := by decide +kernel
lemma column100_0_r3_5_eq : ∀ k : Fin 16, column100_0Expr 3 5 k = column100_0_r3_5 k := by decide +kernel
lemma column100_0_r3_6_eq : ∀ k : Fin 16, column100_0Expr 3 6 k = column100_0_r3_6 k := by decide +kernel
lemma column100_0_r3_7_eq : ∀ k : Fin 16, column100_0Expr 3 7 k = column100_0_r3_7 k := by decide +kernel
lemma column100_0_r3_8_eq : ∀ k : Fin 16, column100_0Expr 3 8 k = column100_0_r3_8 k := by decide +kernel
lemma column100_0_r3_9_eq : ∀ k : Fin 16, column100_0Expr 3 9 k = column100_0_r3_9 k := by decide +kernel
lemma column100_0_r3_10_eq : ∀ k : Fin 16, column100_0Expr 3 10 k = column100_0_r3_10 k := by decide +kernel
lemma column100_0_r3_11_eq : ∀ k : Fin 16, column100_0Expr 3 11 k = column100_0_r3_11 k := by decide +kernel
lemma column100_0_r3_12_eq : ∀ k : Fin 16, column100_0Expr 3 12 k = column100_0_r3_12 k := by decide +kernel
lemma column100_0_r3_13_eq : ∀ k : Fin 16, column100_0Expr 3 13 k = column100_0_r3_13 k := by decide +kernel
lemma column100_0_r3_14_eq : ∀ k : Fin 16, column100_0Expr 3 14 k = column100_0_r3_14 k := by decide +kernel
lemma column100_0_r3_15_eq : ∀ k : Fin 16, column100_0Expr 3 15 k = column100_0_r3_15 k := by decide +kernel
lemma column100_0_r3_eq (i k : Fin 16) : column100_0Expr 3 i k = column100_0_r3 i k := by
  fin_cases i
  · exact column100_0_r3_0_eq k
  · exact column100_0_r3_1_eq k
  · exact column100_0_r3_2_eq k
  · exact column100_0_r3_3_eq k
  · exact column100_0_r3_4_eq k
  · exact column100_0_r3_5_eq k
  · exact column100_0_r3_6_eq k
  · exact column100_0_r3_7_eq k
  · exact column100_0_r3_8_eq k
  · exact column100_0_r3_9_eq k
  · exact column100_0_r3_10_eq k
  · exact column100_0_r3_11_eq k
  · exact column100_0_r3_12_eq k
  · exact column100_0_r3_13_eq k
  · exact column100_0_r3_14_eq k
  · exact column100_0_r3_15_eq k
lemma column100_0_r4_0_eq : ∀ k : Fin 16, column100_0Expr 4 0 k = column100_0_r4_0 k := by decide +kernel
lemma column100_0_r4_1_eq : ∀ k : Fin 16, column100_0Expr 4 1 k = column100_0_r4_1 k := by decide +kernel
lemma column100_0_r4_2_eq : ∀ k : Fin 16, column100_0Expr 4 2 k = column100_0_r4_2 k := by decide +kernel
lemma column100_0_r4_3_eq : ∀ k : Fin 16, column100_0Expr 4 3 k = column100_0_r4_3 k := by decide +kernel
lemma column100_0_r4_4_eq : ∀ k : Fin 16, column100_0Expr 4 4 k = column100_0_r4_4 k := by decide +kernel
lemma column100_0_r4_10_eq : ∀ k : Fin 16, column100_0Expr 4 10 k = column100_0_r4_10 k := by decide +kernel
lemma column100_0_r4_11_eq : ∀ k : Fin 16, column100_0Expr 4 11 k = column100_0_r4_11 k := by decide +kernel
lemma column100_0_r4_12_eq : ∀ k : Fin 16, column100_0Expr 4 12 k = column100_0_r4_12 k := by decide +kernel
lemma column100_0_r4_13_eq : ∀ k : Fin 16, column100_0Expr 4 13 k = column100_0_r4_13 k := by decide +kernel
lemma column100_0_r4_14_eq : ∀ k : Fin 16, column100_0Expr 4 14 k = column100_0_r4_14 k := by decide +kernel
lemma column100_0_r4_15_eq : ∀ k : Fin 16, column100_0Expr 4 15 k = column100_0_r4_15 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues10
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
noncomputable def kernel1_0_r0 : Fin 16 → Fin 16 → CBox := ![kernel1_0_r0_0,kernel1_0_r0_1,kernel1_0_r0_2,kernel1_0_r0_3,kernel1_0_r0_4,kernel1_0_r0_5,kernel1_0_r0_6,kernel1_0_r0_7,kernel1_0_r0_8,kernel1_0_r0_9,kernel1_0_r0_10,kernel1_0_r0_11,kernel1_0_r0_12,kernel1_0_r0_13,kernel1_0_r0_14,kernel1_0_r0_15]
noncomputable def kernel1_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel1_0_r0,kernel1_0_r1,kernel1_0_r2,kernel1_0_r3,kernel1_0_r4,kernel1_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments100
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace cm100_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column100_0 j i k).mul (kernel1_0 j i k))
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
lemma checked : cachedMomentRuleBox column100_0 kernel1_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
end cm100_1_0_0
end SharpPlanar.CachedData

end OAI
end


