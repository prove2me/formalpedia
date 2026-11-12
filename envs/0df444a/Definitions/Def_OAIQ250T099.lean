-- Prove2me | Definitions.Def_OAIQ250T099
-- name    : OAIQ250T099
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:33:14.40631+00:00
-- url     : https://prove2.me/theorems/f47d878e-06bb-4e74-a744-794506f84354
-- title:
--   Definitions bundle OAIQ250T099 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 2 definitions and 35 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.Boperator`, `OAI.AtomicTriangular.Construction.splitB`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_ParamInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamInterval.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Certificate_WaveJetsData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean), [`Triangular_Construction_ActualTail`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ActualTail.lean), [`Triangular_Construction_BlockOperators`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean), [`Triangular_Construction_ConcreteSchur`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ConcreteSchur.lean), [`Triangular_Envelope_EnvelopePsiB`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiB.lean), [`Triangular_Envelope_EnvelopePsiD`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean), [`Triangular_Envelope_KernelBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/KernelBounds.lean), [`Triangular_Signs_RemainderNorm`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderNorm.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T064`, `OAIQ250T083`, `OAIQ250T084` and `OAIQ250T151` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T112` and `OAIQ250T113`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T064
import Definitions.Def_OAIQ250T083
import Definitions.Def_OAIQ250T084
import Definitions.Def_OAIQ250T151

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveExpData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma DTable_mem (a : Fin 10) : (DTable a).Mem (D (finiteNode a)) := by
  fin_cases a
  · exact DBox1_mem
  · exact DBox3_mem
  · exact DBox4_mem
  · exact DBox7_mem
  · exact DBox9_mem
  · exact DBox12_mem
  · exact DBox13_mem
  · exact DBox16_mem
  · exact DBox19_mem
  · exact DBox21_mem

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveJetsData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma jetTable0_0_calc (j : Fin 31) : jetMultiplierBox 0 0 j = jetTable0_0 j := by
  revert j
  decide +kernel
lemma jetTable0_10_calc (j : Fin 31) : jetMultiplierBox 0 10 j = jetTable0_10 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma YfBox_mem (i : Fin 20) (j : Fin 8) : (YfBox i j).Mem (Yf i j) := by
  unfold YfBox Yf
  split_ifs
  all_goals first
    | apply RI.mem_mul (targetCoefficientBox_mem _); first
        | simpa using RI.mem_point 1
        | simpa using RI.mem_point (-1)
        | simpa using RI.mem_point 0
        | exact RI.mem_sub etaPiBox_mem (DTable_mem _)
    | simpa using RI.mem_point 0

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopePsiB
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma psiB1_mem (j : Fin 31) : (psiB1 j).Mem (normJetEnvelope (damping 0) (damping 1) 1 (frequency j)) := by
  rw [← psiB1_calc]
  apply psiBox_mem
  · exact QBox1_mem
  · exact DBox1_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB1_mem j
  · decide +kernel
lemma psiB3_mem (j : Fin 31) : (psiB3 j).Mem (normJetEnvelope (damping 0) (damping 1) 3 (frequency j)) := by
  rw [← psiB3_calc]
  apply psiBox_mem
  · exact QBox3_mem
  · exact DBox3_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB3_mem j
  · decide +kernel
lemma psiB4_mem (j : Fin 31) : (psiB4 j).Mem (normJetEnvelope (damping 0) (damping 1) 4 (frequency j)) := by
  rw [← psiB4_calc]
  apply psiBox_mem
  · exact QBox4_mem
  · exact DBox4_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB4_mem j
  · decide +kernel
lemma psiB7_mem (j : Fin 31) : (psiB7 j).Mem (normJetEnvelope (damping 0) (damping 1) 7 (frequency j)) := by
  rw [← psiB7_calc]
  apply psiBox_mem
  · exact QBox7_mem
  · exact DBox7_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB7_mem j
  · decide +kernel
lemma psiB9_mem (j : Fin 31) : (psiB9 j).Mem (normJetEnvelope (damping 0) (damping 1) 9 (frequency j)) := by
  rw [← psiB9_calc]
  apply psiBox_mem
  · exact QBox9_mem
  · exact DBox9_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB9_mem j
  · decide +kernel
lemma psiB21_mem (j : Fin 31) : (psiB21 j).Mem (normJetEnvelope (damping 0) (damping 1) 21 (frequency j)) := by
  rw [← psiB21_calc]
  apply psiBox_mem
  · exact QBox21_mem
  · exact DBox21_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB21_mem j
  · decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopePsiD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma psiD36_mem (j : Fin 31) : (psiD36 j).Mem (normJetEnvelope (damping 0) (damping 0) 36 (frequency j)) := by
  rw [← psiD36_calc]
  apply psiBox_mem
  · convert QBox0_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox0_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD36_mem j
  · decide +kernel
lemma psiD37_mem (j : Fin 31) : (psiD37 j).Mem (normJetEnvelope (damping 0) (damping 0) 37 (frequency j)) := by
  rw [← psiD37_calc]
  apply psiBox_mem
  · convert QBox1_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox1_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD37_mem j
  · decide +kernel
lemma psiD39_mem (j : Fin 31) : (psiD39 j).Mem (normJetEnvelope (damping 0) (damping 0) 39 (frequency j)) := by
  rw [← psiD39_calc]
  apply psiBox_mem
  · convert QBox3_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox3_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD39_mem j
  · decide +kernel
lemma psiD40_mem (j : Fin 31) : (psiD40 j).Mem (normJetEnvelope (damping 0) (damping 0) 40 (frequency j)) := by
  rw [← psiD40_calc]
  apply psiBox_mem
  · convert QBox4_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox4_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD40_mem j
  · decide +kernel
lemma psiD43_mem (j : Fin 31) : (psiD43 j).Mem (normJetEnvelope (damping 0) (damping 0) 43 (frequency j)) := by
  rw [← psiD43_calc]
  apply psiBox_mem
  · convert QBox7_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox7_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD43_mem j
  · decide +kernel
lemma psiD45_mem (j : Fin 31) : (psiD45 j).Mem (normJetEnvelope (damping 0) (damping 0) 45 (frequency j)) := by
  rw [← psiD45_calc]
  apply psiBox_mem
  · convert QBox9_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox9_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD45_mem j
  · decide +kernel
lemma psiD48_mem (j : Fin 31) : (psiD48 j).Mem (normJetEnvelope (damping 0) (damping 0) 48 (frequency j)) := by
  rw [← psiD48_calc]
  apply psiBox_mem
  · convert QBox12_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox12_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD48_mem j
  · decide +kernel
lemma psiD25_mem (j : Fin 31) : (psiD25 j).Mem (normJetEnvelope (damping 0) (damping 0) 25 (frequency j)) := by
  rw [← psiD25_calc]
  apply psiBox_mem
  · exact QBox25_mem
  · exact DBox25_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD25_mem j
  · decide +kernel
lemma psiD27_mem (j : Fin 31) : (psiD27 j).Mem (normJetEnvelope (damping 0) (damping 0) 27 (frequency j)) := by
  rw [← psiD27_calc]
  apply psiBox_mem
  · exact QBox27_mem
  · exact DBox27_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD27_mem j
  · decide +kernel
lemma psiD28_mem (j : Fin 31) : (psiD28 j).Mem (normJetEnvelope (damping 0) (damping 0) 28 (frequency j)) := by
  rw [← psiD28_calc]
  apply psiBox_mem
  · exact QBox28_mem
  · exact DBox28_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD28_mem j
  · decide +kernel
lemma psiD31_mem (j : Fin 31) : (psiD31 j).Mem (normJetEnvelope (damping 0) (damping 0) 31 (frequency j)) := by
  rw [← psiD31_calc]
  apply psiBox_mem
  · exact QBox31_mem
  · exact DBox31_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD31_mem j
  · decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma psiTableB_mem (i : Fin 10) (j : Fin 31) : (psiTableB i j).Mem (normJetEnvelope (damping 0) (damping 1) (finiteNode i) (frequency j)) := by
  fin_cases i
  · exact psiB1_mem j
  · exact psiB3_mem j
  · exact psiB4_mem j
  · exact psiB7_mem j
  · exact psiB9_mem j
  · exact psiB12_mem j
  · exact psiB13_mem j
  · exact psiB16_mem j
  · exact psiB19_mem j
  · exact psiB21_mem j
lemma envelopeSumBoxB_mem (j : Fin 31) : (envelopeSumBoxB j).Mem (finiteEnvelopeSum 0 1 j) := by
  rw [← envelopeSumBoxB_calc]
  exact RI.mem_sum (fun i => psiTableB_mem i j)
lemma boundB_mem (c : Fin 2) : (boundB c).Mem (finiteTailEnvelope c) := by
  rw [← boundB_calc]
  exact RI.mem_sum (fun i => RI.mem_mul (envelopeSumBoxB_mem _) (fullWTable_mem i c))
lemma finiteTailEnvelope_bound (c : Fin 2) : finiteTailEnvelope c < (335/1:ℝ) := by
  have hh := ri_mem_lt (boundB_mem c) 335 1 (by norm_num) (by revert c; decide +kernel)
  simpa only [Int.cast_ofNat, Nat.cast_one] using hh
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_KernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma finite_tail_column_bound (n : ℤ) (c : Fin 2) :
    (∑ m : Fin 10, ∑ d : Fin 2, |tailJet h H (finiteNode m) n c d|) < 335 := by
  apply lt_of_le_of_lt _ (by simpa using FiniteCertificate.finiteTailEnvelope_bound c)
  calc
    _  ≤  ∑ m : Fin 10, ∑ i : Fin 15,
        normJetEnvelope h H (finiteNode m) (frequency ⟨i.val+16,by omega⟩)*fullTailW i c := by
      apply Finset.sum_le_sum
      intro m _
      exact tailJet_pair_bound 0 1 _ n (by have h := (finiteNode_node m).1; omega) (finiteNode_Qpos m) c
    _ = finiteTailEnvelope c := by
      rw [Finset.sum_comm]
      simp only [finiteTailEnvelope,finiteEnvelopeSum,damping,↓reduceIte,Fin.val_zero,Fin.val_one,one_ne_zero,Finset.sum_mul]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
lemma Bkernel_bound (p : TailNode × Fin 2) : (∑' i, |Bkernel i p|) ≤ 335 := by
  rw [tsum_fintype]
  change (∑ i : Fin 20, |tailJet h H (finiteNode ⟨i.val/2,by omega⟩) p.1.val.val p.2 ⟨i.val%2,by omega⟩|) ≤ 335
  exact (sum_fin20_pairs (fun n d => |tailJet h H (finiteNode n) p.1.val.val p.2 d|)).trans_le (finite_tail_column_bound _ _).le
def Boperator : TailCoefficients →L[ℝ] FiniteCoefficients :=
  operator Bkernel (fun _ => (hasSum_fintype _).summable) 335 Bkernel_bound
lemma Boperator_norm : ‖Boperator‖ ≤ 335 := operator_norm _ _ _ (by norm_num) _
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ConcreteSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.Schur

def splitB (e : Fin 2) : TailCoefficients →L[ℝ] FiniteCoefficients :=
  if e.val=0 then Boperator else -Boperator
lemma splitB_norm (e : Fin 2) : ‖splitB e‖ ≤ 340 := by
  have hh := Boperator_norm
  fin_cases e <;> simp only [splitB,↓reduceIte,Nat.one_ne_zero,norm_neg] <;> linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma CallOperator_extend (u : FiniteCoefficients) :
    CallOperator (extendFiniteError u)=Coperator u := by
  ext p
  unfold CallOperator Coperator
  erw [operator_apply,operator_apply,tsum_fintype,tsum_fintype]
  change (∑ i : Fin 22, (if hi : i.val<2 then 0 else u ⟨i.val-2,by omega⟩)*CallKernel p i)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,show 0<2 by omega,show 0+1<2 by omega,↓reduceDIte,zero_mul,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show ¬(i.val+1+1<2) by omega,↓reduceDIte]
  congr 1
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorNorm00_mem (j : Fin 31) : (taylorNorm00 j).Mem ‖taylorPhase 0 0 (frequency j)‖ := by
  have hh := taylorNorm00_check j
  exact CI.mem_norm (taylorPhaseTable_mem 0 0 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma taylorNorm01_mem (j : Fin 31) : (taylorNorm01 j).Mem ‖taylorPhase 0 1 (frequency j)‖ := by
  have hh := taylorNorm01_check j
  exact CI.mem_norm (taylorPhaseTable_mem 0 1 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma taylorNorm10_mem (j : Fin 31) : (taylorNorm10 j).Mem ‖taylorPhase 1 0 (frequency j)‖ := by
  have hh := taylorNorm10_check j
  exact CI.mem_norm (taylorPhaseTable_mem 1 0 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma taylorNorm11_mem (j : Fin 31) : (taylorNorm11 j).Mem ‖taylorPhase 1 1 (frequency j)‖ := by
  have hh := taylorNorm11_check j
  exact CI.mem_norm (taylorPhaseTable_mem 1 1 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma taylorNormTable_mem (q br : Fin 2) (j : Fin 31) : (taylorNormTable q br j).Mem ‖taylorPhase q br (frequency j)‖ := by
  fin_cases q <;> fin_cases br
  · exact taylorNorm00_mem j
  · exact taylorNorm01_mem j
  · exact taylorNorm10_mem j
  · exact taylorNorm11_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end


