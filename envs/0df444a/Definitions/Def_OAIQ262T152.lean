-- Prove2me | Definitions.Def_OAIQ262T152
-- name    : OAIQ262T152
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:39:39.652778+00:00
-- url     : https://prove2.me/theorems/543cb85a-e0e2-44b0-adb3-72fb99c66615
-- title:
--   Definitions bundle OAIQ262T152 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 2 definitions and 25 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.Boperator`, `OAI.AtomicTriangular.Construction.splitB`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_TargetInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/TargetInterval.lean), [`Triangular_Certificate_WaveJetsData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean), [`Triangular_Construction_BlockOperators`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean), [`Triangular_Construction_ConcreteSchur`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ConcreteSchur.lean), [`Triangular_Construction_NodeJets`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/NodeJets.lean), [`Triangular_Envelope_EnvelopeNorms`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorms.lean), [`Triangular_Envelope_EnvelopePsiB`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiB.lean), [`Triangular_Envelope_EnvelopePsiD`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean), [`Triangular_Envelope_KernelBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/KernelBounds.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T137`, `OAIQ262T138`, `OAIQ262T139` and `OAIQ262T142` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T193` and `OAIQ262T194`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T137
import Definitions.Def_OAIQ262T138
import Definitions.Def_OAIQ262T139
import Definitions.Def_OAIQ262T142

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_WaveJetsData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma jetTable0_12_calc (j : Fin 31) : jetMultiplierBox 0 12 j = jetTable0_12 j := by
  revert j
  decide +kernel
lemma jetTable0_13_calc (j : Fin 31) : jetMultiplierBox 0 13 j = jetTable0_13 j := by
  revert j
  decide +kernel
lemma jetTable0_14_calc (j : Fin 31) : jetMultiplierBox 0 14 j = jetTable0_14 j := by
  revert j
  decide +kernel
lemma jetTable0_15_calc (j : Fin 31) : jetMultiplierBox 0 15 j = jetTable0_15 j := by
  revert j
  decide +kernel
lemma jetTable0_16_calc (j : Fin 31) : jetMultiplierBox 0 16 j = jetTable0_16 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma fullWTable_mem (i : Fin 15) (d : Fin 2) : (fullWTable i d).Mem (fullTailW i d) := by
  rw [← fullWTable_calc]
  exact fullTailWBox_mem columnNorm22 fourierNorm_mem i d
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopePsiB
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
lemma psiB13_mem (j : Fin 31) : (psiB13 j).Mem (normJetEnvelope (damping 0) (damping 1) 13 (frequency j)) := by
  rw [← psiB13_calc]
  apply psiBox_mem
  · exact QBox13_mem
  · exact DBox13_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB13_mem j
  · decide +kernel
lemma psiB16_mem (j : Fin 31) : (psiB16 j).Mem (normJetEnvelope (damping 0) (damping 1) 16 (frequency j)) := by
  rw [← psiB16_calc]
  apply psiBox_mem
  · exact QBox16_mem
  · exact DBox16_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB16_mem j
  · decide +kernel
lemma psiB19_mem (j : Fin 31) : (psiB19 j).Mem (normJetEnvelope (damping 0) (damping 1) 19 (frequency j)) := by
  rw [← psiB19_calc]
  apply psiBox_mem
  · exact QBox19_mem
  · exact DBox19_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB19_mem j
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
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopePsiD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma psiD25_mem (j : Fin 31) : (psiD25 j).Mem (normJetEnvelope (damping 0) (damping 0) 25 (frequency j)) := by
  rw [← psiD25_calc]
  apply psiBox_mem
  · exact QBox25_mem
  · exact DBox25_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD25_mem j
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
-- module Solutions.OAIQ262_TG.Triangular_Envelope_KernelBounds
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
-- module Solutions.OAIQ262_TG.Triangular_Certificate_TargetInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma targetEnvBox_mem (q : Fin 2) (n : ℤ) {qb db eb : RI}
    (hq : qb.Mem (Q n)) (hd : db.Mem (D n))
    (he : eb.Mem (Real.exp (Real.pi*(damping q-h)*n+(1-n)/Z))) (hp : 0<qb.lo) :
    (targetEnvBox q qb db eb).Mem (targetEnvelope (damping q) n) := by
  unfold targetEnvelope
  rw [div_eq_mul_inv]
  exact RI.mem_mul (RI.mem_mul (RI.mem_mul QBox1_mem (RI.mem_invPos hq hp))
    (RI.mem_add (RI.mem_add ri1_mem targetZBox_mem)
      (RI.mem_mul targetZBox_mem (RI.mem_abs (RI.mem_sub (targetRateBox_mem q) hd))))) he

end AtomicTriangular.FiniteCertificate
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
-- module Solutions.OAIQ262_TG.Triangular_Construction_ConcreteSchur
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
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_NodeJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ComplexConjugate
namespace AtomicTriangular.Construction

lemma P_cBasis (n : Node) : P = fun s => (s-(n.val:ℂ))^2*cBasis n s := by
  funext s
  by_cases hs : s = (n.val:ℂ)
  · simp [hs,P_node]
  · rw [cBasis_eq n hs]
    field_simp

end AtomicTriangular.Construction
end

end OAI
end


