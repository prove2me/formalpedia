-- Prove2me | Definitions.Def_OAIQ262T151
-- name    : OAIQ262T151
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:32:15.783682+00:00
-- url     : https://prove2.me/theorems/62bea1ac-b477-4c89-be0e-59963acdf98d
-- title:
--   Definitions bundle OAIQ262T151 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 17 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Construction_BlockOperators`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean), [`Triangular_Envelope_EnvelopePsiC`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiC.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean), [`Triangular_Envelope_KernelBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/KernelBounds.lean), [`Triangular_Taylor_TaylorPhase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorPhase.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T137`, `OAIQ262T138` and `OAIQ262T140` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T193` and `OAIQ262T194`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T137
import Definitions.Def_OAIQ262T138
import Definitions.Def_OAIQ262T140

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
lemma psiC37_mem (j : Fin 31) : (psiC37 j).Mem (normJetEnvelope (damping 1) (damping 0) 37 (frequency j)) := by
  rw [← psiC37_calc]
  apply psiBox_mem
  · convert QBox1_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox1_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC37_mem j
  · decide +kernel
lemma psiC39_mem (j : Fin 31) : (psiC39 j).Mem (normJetEnvelope (damping 1) (damping 0) 39 (frequency j)) := by
  rw [← psiC39_calc]
  apply psiBox_mem
  · convert QBox3_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox3_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC39_mem j
  · decide +kernel
lemma psiC40_mem (j : Fin 31) : (psiC40 j).Mem (normJetEnvelope (damping 1) (damping 0) 40 (frequency j)) := by
  rw [← psiC40_calc]
  apply psiBox_mem
  · convert QBox4_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox4_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC40_mem j
  · decide +kernel
lemma psiC43_mem (j : Fin 31) : (psiC43 j).Mem (normJetEnvelope (damping 1) (damping 0) 43 (frequency j)) := by
  rw [← psiC43_calc]
  apply psiBox_mem
  · convert QBox7_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox7_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC43_mem j
  · decide +kernel
lemma psiC45_mem (j : Fin 31) : (psiC45 j).Mem (normJetEnvelope (damping 1) (damping 0) 45 (frequency j)) := by
  rw [← psiC45_calc]
  apply psiBox_mem
  · convert QBox9_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox9_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC45_mem j
  · decide +kernel
lemma psiC48_mem (j : Fin 31) : (psiC48 j).Mem (normJetEnvelope (damping 1) (damping 0) 48 (frequency j)) := by
  rw [← psiC48_calc]
  apply psiBox_mem
  · convert QBox12_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox12_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC48_mem j
  · decide +kernel
lemma psiC49_mem (j : Fin 31) : (psiC49 j).Mem (normJetEnvelope (damping 1) (damping 0) 49 (frequency j)) := by
  rw [← psiC49_calc]
  apply psiBox_mem
  · convert QBox13_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox13_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC49_mem j
  · decide +kernel
lemma psiC52_mem (j : Fin 31) : (psiC52 j).Mem (normJetEnvelope (damping 1) (damping 0) 52 (frequency j)) := by
  rw [← psiC52_calc]
  apply psiBox_mem
  · convert QBox16_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox16_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC52_mem j
  · decide +kernel
lemma psiC55_mem (j : Fin 31) : (psiC55 j).Mem (normJetEnvelope (damping 1) (damping 0) 55 (frequency j)) := by
  rw [← psiC55_calc]
  apply psiBox_mem
  · convert QBox19_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox19_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC55_mem j
  · decide +kernel
lemma psiC57_mem (j : Fin 31) : (psiC57 j).Mem (normJetEnvelope (damping 1) (damping 0) 57 (frequency j)) := by
  rw [← psiC57_calc]
  apply psiBox_mem
  · convert QBox21_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox21_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC57_mem j
  · decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma psiTableC_mem (i : Fin 15) (j : Fin 31) : (psiTableC i j).Mem (normJetEnvelope (damping 1) (damping 0) (tailBase i) (frequency j)) := by
  fin_cases i
  · exact psiC36_mem j
  · exact psiC37_mem j
  · exact psiC39_mem j
  · exact psiC40_mem j
  · exact psiC43_mem j
  · exact psiC45_mem j
  · exact psiC48_mem j
  · exact psiC49_mem j
  · exact psiC52_mem j
  · exact psiC55_mem j
  · exact psiC57_mem j
  · exact psiC25_mem j
  · exact psiC27_mem j
  · exact psiC28_mem j
  · exact psiC31_mem j
lemma envelopeSumBoxC_mem (j : Fin 31) : (envelopeSumBoxC j).Mem (tailEnvelopeSum 1 0 j) := by
  rw [← envelopeSumBoxC_calc]
  exact RI.mem_mul (RI.mem_sum (fun i => psiTableC_mem i j))
    (RI.mem_invPos (RI.mem_sub ri1_mem (periodExpC_mem j)) (periodDenC_pos j))
lemma boundC_mem (c : Fin 22) : (boundC c).Mem (tailFiniteEnvelope c) := by
  rw [← boundC_calc]
  exact RI.mem_sum (fun j => RI.mem_mul (envelopeSumBoxC_mem j) (columnNormTable_mem _ j))
lemma tailFiniteEnvelope_bound (c : Fin 22) : tailFiniteEnvelope c < (7/1000000000000000:ℝ) := by
  apply ri_mem_lt (boundC_mem c) 7 1000000000000000 (by norm_num)
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_KernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma tail_finite_column_bound (c : Fin 22) :
    (∑' p : TailNode × Fin 2, |jet H h p.1.val.val p.2 (finiteColumn ⟨c.val,by omega⟩)|) < 7/10^15 := by
  exact (tail_atom_column_bounds 1 0 _).2.trans_lt (by norm_num [tailFiniteEnvelope,damping,H,h] at ⊢; simpa [tailFiniteEnvelope] using FiniteCertificate.tailFiniteEnvelope_bound c)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
lemma Ckernel_bound (i : Fin 20) : (∑' p, |Ckernel p i|) ≤ 7/10^15 :=
  (tail_finite_column_bound ⟨i.val+2,by omega⟩).le
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorPhaseBox_mem (q branch : Fin 2) (j : Fin 31) :
    (taylorPhaseBox q branch j).Mem (taylorPhase q branch (frequency j)) := by
  unfold taylorPhaseBox taylorPhase
  split_ifs
  · exact CI.mem_sub (CI.mem_mul (CI.mem_mul CI.mem_imag (CI.mem_ofReal piBox_mem)) (CI.mem_ofReal (realFrequencyBox_mem j)))
      (CI.mem_ofReal (RI.mem_mul piBox_mem (RI.mem_sub (dampingBox_mem q) (dampingBox_mem 0))))
  · exact wavePhaseBox_mem q 0 j

end AtomicTriangular.FiniteCertificate
end

end OAI
end


