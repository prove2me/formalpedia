-- Prove2me | Definitions.Def_OAIQ262T087
-- name    : OAIQ262T087
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:49:59.357752+00:00
-- url     : https://prove2.me/theorems/7b2ca369-216c-4ebd-b596-5b287aa3db95
-- title:
--   Definitions bundle OAIQ262T087 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 33 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_WaveIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean), [`Triangular_Construction_RepetitionBound`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/RepetitionBound.lean), [`Triangular_Envelope_EnvelopePsiC`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiC.lean), [`Triangular_Envelope_EnvelopeSumsBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSumsBase.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005`, `OAIQ262T006` and `OAIQ262T007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T137` and `OAIQ262T138`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T006
import Definitions.Def_OAIQ262T007

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma jetBox3_4_mem : jetBox3_4.Mem (waveDerivative 3 ((4:ℤ):ℂ)) := by
  rw [← jetBox3_4_calc]
  exact waveDerivativeBox_mem 3 4
lemma DBox4_calc : jetBox3_4.re.mul ((RI.point 6).mul QBox4).inv = DBox4 := by decide +kernel
lemma jetBox3_7_mem : jetBox3_7.Mem (waveDerivative 3 ((7:ℤ):ℂ)) := by
  rw [← jetBox3_7_calc]
  exact waveDerivativeBox_mem 3 7
lemma DBox7_calc : jetBox3_7.re.mul ((RI.point 6).mul QBox7).inv = DBox7 := by decide +kernel
lemma jetBox3_9_mem : jetBox3_9.Mem (waveDerivative 3 ((9:ℤ):ℂ)) := by
  rw [← jetBox3_9_calc]
  exact waveDerivativeBox_mem 3 9
lemma DBox9_calc : jetBox3_9.re.mul ((RI.point 6).mul QBox9).inv = DBox9 := by decide +kernel
lemma jetBox3_12_mem : jetBox3_12.Mem (waveDerivative 3 ((12:ℤ):ℂ)) := by
  rw [← jetBox3_12_calc]
  exact waveDerivativeBox_mem 3 12
lemma DBox12_calc : jetBox3_12.re.mul ((RI.point 6).mul QBox12).inv = DBox12 := by decide +kernel
lemma jetBox3_13_mem : jetBox3_13.Mem (waveDerivative 3 ((13:ℤ):ℂ)) := by
  rw [← jetBox3_13_calc]
  exact waveDerivativeBox_mem 3 13
lemma DBox13_calc : jetBox3_13.re.mul ((RI.point 6).mul QBox13).inv = DBox13 := by decide +kernel
lemma jetBox3_16_mem : jetBox3_16.Mem (waveDerivative 3 ((16:ℤ):ℂ)) := by
  rw [← jetBox3_16_calc]
  exact waveDerivativeBox_mem 3 16
lemma DBox16_calc : jetBox3_16.re.mul ((RI.point 6).mul QBox16).inv = DBox16 := by decide +kernel
lemma jetBox3_19_mem : jetBox3_19.Mem (waveDerivative 3 ((19:ℤ):ℂ)) := by
  rw [← jetBox3_19_calc]
  exact waveDerivativeBox_mem 3 19
lemma DBox19_calc : jetBox3_19.re.mul ((RI.point 6).mul QBox19).inv = DBox19 := by decide +kernel
lemma jetBox3_21_mem : jetBox3_21.Mem (waveDerivative 3 ((21:ℤ):ℂ)) := by
  rw [← jetBox3_21_calc]
  exact waveDerivativeBox_mem 3 21
lemma DBox21_calc : jetBox3_21.re.mul ((RI.point 6).mul QBox21).inv = DBox21 := by decide +kernel
end AtomicTriangular.FiniteCertificate

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopePsiC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpC36_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 36))).exp.re=envelopeExpC36 j := by
  revert j
  decide +kernel
lemma envelopeExpC36_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 36))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC37_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 37))).exp.re=envelopeExpC37 j := by
  revert j
  decide +kernel
lemma envelopeExpC37_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 37))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC39_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 39))).exp.re=envelopeExpC39 j := by
  revert j
  decide +kernel
lemma envelopeExpC39_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 39))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC40_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 40))).exp.re=envelopeExpC40 j := by
  revert j
  decide +kernel
lemma envelopeExpC40_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 40))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC27_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 27))).exp.re=envelopeExpC27 j := by
  revert j
  decide +kernel
lemma envelopeExpC27_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 27))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC28_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 28))).exp.re=envelopeExpC28 j := by
  revert j
  decide +kernel
lemma envelopeExpC28_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 28))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC31_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 31))).exp.re=envelopeExpC31 j := by
  revert j
  decide +kernel
lemma envelopeExpC31_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 31))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeSumsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ri_mem_lt {a : RI} {x : ℝ} (hx : a.Mem x) (p : ℤ) (q : ℕ) (hq : 0<q)
    (h : a.hi*q < p*scale) : x < p/q := by
  have hh : (a.hi:ℝ)*(q:ℝ) < p*(scale:ℝ) := by exact_mod_cast h
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply (lt_div_iff₀ hqR).mpr
  have hx' := mul_le_mul_of_nonneg_right hx.2 hqR.le
  exact (mul_lt_mul_iff_right₀ scale_pos).mp (by nlinarith)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_RepetitionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma repetitionExpData_calc : repetitionExpInput.exp.re=repetitionExpData := by decide +kernel
lemma repetitionNormBox_calc :
    (((RI.point 1).add (piBox.mul ((RI.point 1).divNat 5))).mul repetitionExpData).mul
      (((RI.point 1).sub repetitionExpData).invPos)=repetitionNormBox := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


