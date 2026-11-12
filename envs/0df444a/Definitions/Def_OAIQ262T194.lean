-- Prove2me | Definitions.Def_OAIQ262T194
-- name    : OAIQ262T194
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T20:57:21.265105+00:00
-- url     : https://prove2.me/theorems/7ac8df19-fa97-40f9-8710-db77a034db5b
-- title:
--   Definitions bundle OAIQ262T194 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 128 declarations of OpenAI's Lean: 128 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_ParamInterval`, `Triangular_Certificate_ParamRHS`, `Triangular_Certificate_TargetInterval`, `Triangular_Construction_ActualCorrection`, `Triangular_Construction_ConcreteSchur`, `Triangular_Construction_CurvatureEnvelope`, `Triangular_Construction_DirectCoordinates`, `Triangular_Construction_DirectWaveJets`, `Triangular_Construction_FiniteAssembly`, `Triangular_Construction_FiniteProjection`, `Triangular_Construction_NodeJets`, `Triangular_Construction_Normalization`, `Triangular_Construction_SpectralProduct`, `Triangular_Construction_TailCoordinates`, `Triangular_Schwartz_FourierPair`, `Triangular_Schwartz_Realness`, `Triangular_Taylor_CoefficientSpectral`, `Triangular_Taylor_TaylorPhase`, `Triangular_Taylor_TaylorSpectrum`, `Triangular_Taylor_VariationBound`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T151`, `OAIQ262T152`, `OAIQ262T153`, `OAIQ262T154`, `OAIQ262T155`, `OAIQ262T157`, `OAIQ262T158` and `OAIQ262T159` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T253`, `OAIQ262T254`, `OAIQ262T255`, `OAIQ262T256`, `OAIQ262T257` and `OAIQ262T258`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T151
import Definitions.Def_OAIQ262T152
import Definitions.Def_OAIQ262T153
import Definitions.Def_OAIQ262T154
import Definitions.Def_OAIQ262T155
import Definitions.Def_OAIQ262T157
import Definitions.Def_OAIQ262T158
import Definitions.Def_OAIQ262T159

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamInterval
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
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamRHS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma rhsMinusTableRow0_calc (j : Fin 8) : rhsMinusBox 0 j = rhsMinusTableRow0 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow1_calc (j : Fin 8) : rhsMinusBox 1 j = rhsMinusTableRow1 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow2_calc (j : Fin 8) : rhsMinusBox 2 j = rhsMinusTableRow2 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow3_calc (j : Fin 8) : rhsMinusBox 3 j = rhsMinusTableRow3 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow4_calc (j : Fin 8) : rhsMinusBox 4 j = rhsMinusTableRow4 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow5_calc (j : Fin 8) : rhsMinusBox 5 j = rhsMinusTableRow5 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow6_calc (j : Fin 8) : rhsMinusBox 6 j = rhsMinusTableRow6 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow7_calc (j : Fin 8) : rhsMinusBox 7 j = rhsMinusTableRow7 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow8_calc (j : Fin 8) : rhsMinusBox 8 j = rhsMinusTableRow8 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow9_calc (j : Fin 8) : rhsMinusBox 9 j = rhsMinusTableRow9 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow10_calc (j : Fin 8) : rhsMinusBox 10 j = rhsMinusTableRow10 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow11_calc (j : Fin 8) : rhsMinusBox 11 j = rhsMinusTableRow11 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow12_calc (j : Fin 8) : rhsMinusBox 12 j = rhsMinusTableRow12 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow13_calc (j : Fin 8) : rhsMinusBox 13 j = rhsMinusTableRow13 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow14_calc (j : Fin 8) : rhsMinusBox 14 j = rhsMinusTableRow14 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow15_calc (j : Fin 8) : rhsMinusBox 15 j = rhsMinusTableRow15 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow16_calc (j : Fin 8) : rhsMinusBox 16 j = rhsMinusTableRow16 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow17_calc (j : Fin 8) : rhsMinusBox 17 j = rhsMinusTableRow17 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow18_calc (j : Fin 8) : rhsMinusBox 18 j = rhsMinusTableRow18 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow19_calc (j : Fin 8) : rhsMinusBox 19 j = rhsMinusTableRow19 j := by
  revert j
  decide +kernel
lemma rhsMinusTable_calc (i : Fin 20) (j : Fin 8) : rhsMinusBox i j = rhsMinusTable i j := by
  fin_cases i
  · exact rhsMinusTableRow0_calc j
  · exact rhsMinusTableRow1_calc j
  · exact rhsMinusTableRow2_calc j
  · exact rhsMinusTableRow3_calc j
  · exact rhsMinusTableRow4_calc j
  · exact rhsMinusTableRow5_calc j
  · exact rhsMinusTableRow6_calc j
  · exact rhsMinusTableRow7_calc j
  · exact rhsMinusTableRow8_calc j
  · exact rhsMinusTableRow9_calc j
  · exact rhsMinusTableRow10_calc j
  · exact rhsMinusTableRow11_calc j
  · exact rhsMinusTableRow12_calc j
  · exact rhsMinusTableRow13_calc j
  · exact rhsMinusTableRow14_calc j
  · exact rhsMinusTableRow15_calc j
  · exact rhsMinusTableRow16_calc j
  · exact rhsMinusTableRow17_calc j
  · exact rhsMinusTableRow18_calc j
  · exact rhsMinusTableRow19_calc j
end AtomicTriangular.FiniteCertificate
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
lemma targetEnvf9_mem : targetEnvf9.Mem (targetEnvelope (damping 1) 9) := by
  rw [← targetEnvf9_calc]
  apply targetEnvBox_mem 1 9 _ _ targetExpf9_mem (by decide +kernel)
  · exact QBox9_mem
  · exact DBox9_mem
lemma targetEnvf12_mem : targetEnvf12.Mem (targetEnvelope (damping 1) 12) := by
  rw [← targetEnvf12_calc]
  apply targetEnvBox_mem 1 12 _ _ targetExpf12_mem (by decide +kernel)
  · exact QBox12_mem
  · exact DBox12_mem
lemma targetEnvf13_mem : targetEnvf13.Mem (targetEnvelope (damping 1) 13) := by
  rw [← targetEnvf13_calc]
  apply targetEnvBox_mem 1 13 _ _ targetExpf13_mem (by decide +kernel)
  · exact QBox13_mem
  · exact DBox13_mem
lemma targetEnvf16_mem : targetEnvf16.Mem (targetEnvelope (damping 1) 16) := by
  rw [← targetEnvf16_calc]
  apply targetEnvBox_mem 1 16 _ _ targetExpf16_mem (by decide +kernel)
  · exact QBox16_mem
  · exact DBox16_mem
lemma targetEnvf19_mem : targetEnvf19.Mem (targetEnvelope (damping 1) 19) := by
  rw [← targetEnvf19_calc]
  apply targetEnvBox_mem 1 19 _ _ targetExpf19_mem (by decide +kernel)
  · exact QBox19_mem
  · exact DBox19_mem
lemma targetEnvf21_mem : targetEnvf21.Mem (targetEnvelope (damping 1) 21) := by
  rw [← targetEnvf21_calc]
  apply targetEnvBox_mem 1 21 _ _ targetExpf21_mem (by decide +kernel)
  · exact QBox21_mem
  · exact DBox21_mem
lemma targetEnvTablef_mem (i : Fin 6) : (targetEnvTablef i).Mem (targetEnvelope (damping 1) (finiteNode ⟨i.val+4,by omega⟩)) := by
  fin_cases i
  · exact targetEnvf9_mem
  · exact targetEnvf12_mem
  · exact targetEnvf13_mem
  · exact targetEnvf16_mem
  · exact targetEnvf19_mem
  · exact targetEnvf21_mem
lemma targetEnvt36_mem : targetEnvt36.Mem (targetEnvelope (damping 0) 36) := by
  rw [← targetEnvt36_calc]
  apply targetEnvBox_mem 0 36 _ _ targetExpt36_mem (by decide +kernel)
  · rw [Q_emod 36]; norm_num; exact QBox0_mem
  · rw [D_emod 36]; norm_num; exact DBox0_mem
lemma targetEnvt37_mem : targetEnvt37.Mem (targetEnvelope (damping 0) 37) := by
  rw [← targetEnvt37_calc]
  apply targetEnvBox_mem 0 37 _ _ targetExpt37_mem (by decide +kernel)
  · rw [Q_emod 37]; norm_num; exact QBox1_mem
  · rw [D_emod 37]; norm_num; exact DBox1_mem
lemma targetEnvt39_mem : targetEnvt39.Mem (targetEnvelope (damping 0) 39) := by
  rw [← targetEnvt39_calc]
  apply targetEnvBox_mem 0 39 _ _ targetExpt39_mem (by decide +kernel)
  · rw [Q_emod 39]; norm_num; exact QBox3_mem
  · rw [D_emod 39]; norm_num; exact DBox3_mem
lemma targetEnvt40_mem : targetEnvt40.Mem (targetEnvelope (damping 0) 40) := by
  rw [← targetEnvt40_calc]
  apply targetEnvBox_mem 0 40 _ _ targetExpt40_mem (by decide +kernel)
  · rw [Q_emod 40]; norm_num; exact QBox4_mem
  · rw [D_emod 40]; norm_num; exact DBox4_mem
lemma targetEnvt43_mem : targetEnvt43.Mem (targetEnvelope (damping 0) 43) := by
  rw [← targetEnvt43_calc]
  apply targetEnvBox_mem 0 43 _ _ targetExpt43_mem (by decide +kernel)
  · rw [Q_emod 43]; norm_num; exact QBox7_mem
  · rw [D_emod 43]; norm_num; exact DBox7_mem
lemma targetEnvt45_mem : targetEnvt45.Mem (targetEnvelope (damping 0) 45) := by
  rw [← targetEnvt45_calc]
  apply targetEnvBox_mem 0 45 _ _ targetExpt45_mem (by decide +kernel)
  · rw [Q_emod 45]; norm_num; exact QBox9_mem
  · rw [D_emod 45]; norm_num; exact DBox9_mem
lemma targetEnvt48_mem : targetEnvt48.Mem (targetEnvelope (damping 0) 48) := by
  rw [← targetEnvt48_calc]
  apply targetEnvBox_mem 0 48 _ _ targetExpt48_mem (by decide +kernel)
  · rw [Q_emod 48]; norm_num; exact QBox12_mem
  · rw [D_emod 48]; norm_num; exact DBox12_mem
lemma targetEnvt49_mem : targetEnvt49.Mem (targetEnvelope (damping 0) 49) := by
  rw [← targetEnvt49_calc]
  apply targetEnvBox_mem 0 49 _ _ targetExpt49_mem (by decide +kernel)
  · rw [Q_emod 49]; norm_num; exact QBox13_mem
  · rw [D_emod 49]; norm_num; exact DBox13_mem
lemma targetEnvt52_mem : targetEnvt52.Mem (targetEnvelope (damping 0) 52) := by
  rw [← targetEnvt52_calc]
  apply targetEnvBox_mem 0 52 _ _ targetExpt52_mem (by decide +kernel)
  · rw [Q_emod 52]; norm_num; exact QBox16_mem
  · rw [D_emod 52]; norm_num; exact DBox16_mem
lemma targetEnvt55_mem : targetEnvt55.Mem (targetEnvelope (damping 0) 55) := by
  rw [← targetEnvt55_calc]
  apply targetEnvBox_mem 0 55 _ _ targetExpt55_mem (by decide +kernel)
  · rw [Q_emod 55]; norm_num; exact QBox19_mem
  · rw [D_emod 55]; norm_num; exact DBox19_mem
lemma targetEnvt57_mem : targetEnvt57.Mem (targetEnvelope (damping 0) 57) := by
  rw [← targetEnvt57_calc]
  apply targetEnvBox_mem 0 57 _ _ targetExpt57_mem (by decide +kernel)
  · rw [Q_emod 57]; norm_num; exact QBox21_mem
  · rw [D_emod 57]; norm_num; exact DBox21_mem
lemma targetEnvt25_mem : targetEnvt25.Mem (targetEnvelope (damping 0) 25) := by
  rw [← targetEnvt25_calc]
  apply targetEnvBox_mem 0 25 _ _ targetExpt25_mem (by decide +kernel)
  · exact QBox25_mem
  · exact DBox25_mem
lemma targetEnvt27_mem : targetEnvt27.Mem (targetEnvelope (damping 0) 27) := by
  rw [← targetEnvt27_calc]
  apply targetEnvBox_mem 0 27 _ _ targetExpt27_mem (by decide +kernel)
  · exact QBox27_mem
  · exact DBox27_mem
lemma targetEnvt28_mem : targetEnvt28.Mem (targetEnvelope (damping 0) 28) := by
  rw [← targetEnvt28_calc]
  apply targetEnvBox_mem 0 28 _ _ targetExpt28_mem (by decide +kernel)
  · exact QBox28_mem
  · exact DBox28_mem
lemma targetEnvt31_mem : targetEnvt31.Mem (targetEnvelope (damping 0) 31) := by
  rw [← targetEnvt31_calc]
  apply targetEnvBox_mem 0 31 _ _ targetExpt31_mem (by decide +kernel)
  · exact QBox31_mem
  · exact DBox31_mem
lemma targetEnvTablet_mem (i : Fin 15) : (targetEnvTablet i).Mem (targetEnvelope (damping 0) (tailBase i)) := by
  fin_cases i
  · exact targetEnvt36_mem
  · exact targetEnvt37_mem
  · exact targetEnvt39_mem
  · exact targetEnvt40_mem
  · exact targetEnvt43_mem
  · exact targetEnvt45_mem
  · exact targetEnvt48_mem
  · exact targetEnvt49_mem
  · exact targetEnvt52_mem
  · exact targetEnvt55_mem
  · exact targetEnvt57_mem
  · exact targetEnvt25_mem
  · exact targetEnvt27_mem
  · exact targetEnvt28_mem
  · exact targetEnvt31_mem
lemma finiteTargetEnvelope_bound : finiteTargetEnvelope < (81/10^9:ℝ) := by
  have hh := RI.mem_sum targetEnvTablef_mem
  rw [finiteTargetBox_calc] at hh
  have hb := ri_mem_lt hh 81 (10^9) (by norm_num) (by decide +kernel)
  simpa [finiteTargetEnvelope,tailTargetEnvelope,damping,div_eq_mul_inv,show (10:ℝ)^9=1000000000 by norm_num,show (10:ℝ)^30=1000000000000000000000000000000 by norm_num] using hb
lemma tailTargetEnvelope_bound : tailTargetEnvelope < (92/10^30:ℝ) := by
  have hh := RI.mem_mul (RI.mem_sum targetEnvTablet_mem)
    (RI.mem_invPos (RI.mem_sub ri1_mem targetRatioBox_mem) (by decide +kernel))
  rw [tailTargetBox_calc] at hh
  have hb := ri_mem_lt hh 92 (10^30) (by norm_num) (by decide +kernel)
  simpa [finiteTargetEnvelope,tailTargetEnvelope,damping,div_eq_mul_inv,show (10:ℝ)^9=1000000000 by norm_num,show (10:ℝ)^30=1000000000000000000000000000000 by norm_num] using hb
end AtomicTriangular.FiniteCertificate
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

lemma splitB_norm (e : Fin 2) : ‖splitB e‖ ≤ 340 := by
  have hh := Boperator_norm
  fin_cases e <;> simp only [splitB,↓reduceIte,Nat.one_ne_zero,norm_neg] <;> linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_ActualCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate

lemma finiteResidual_norm {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖finiteResidual z‖ ≤ finiteResidualBound := by
  rw [l1_norm,tsum_fintype]
  change (∑ i : Fin 20, |if i.val<8 then 0 else
    gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩|) ≤ _
  have he : (∑ i : Fin 20, |if i.val<8 then 0 else
      gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩|) =
      ∑ n : Fin 10, if n.val<4 then 0 else ∑ d : Fin 2, |gaussianTarget H z (finiteNode n) d| := by
    rw [show (fun i : Fin 20 => |if i.val<8 then 0 else
      gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩|) =
      (fun i : Fin 20 => (fun n : Fin 10 => fun d : Fin 2 =>
        if n.val<4 then (0:ℝ) else |gaussianTarget H z (finiteNode n) d|)
        ⟨i.val/2,by omega⟩ ⟨i.val%2,by omega⟩) by
        funext i; by_cases hi : i.val<8 <;> simp [hi,show i.val/2<4 ↔ i.val<8 by omega]]
    rw [sum_fin20_pairs (fun n d => if n.val<4 then (0:ℝ) else |gaussianTarget H z (finiteNode n) d|)]
    apply Finset.sum_congr rfl
    intro n _; by_cases hn : n.val<4 <;> simp [hn]
  rw [he]
  have hb : (∑ n : Fin 10, if n.val<4 then 0 else ∑ d : Fin 2, |gaussianTarget H z (finiteNode n) d|) ≤
      ∑ n : Fin 10, if n.val<4 then 0 else targetEnvelope H (finiteNode n) := by
    apply Finset.sum_le_sum
    intro n _
    split_ifs with hn
    · rfl
    · exact gaussianTarget_pair_bound hz hzB H
        ⟨finiteNode n, by fin_cases n <;> decide +kernel⟩ (by fin_cases n <;> norm_num [finiteNode,residue])
  have he2 : (∑ n : Fin 10, if n.val<4 then 0 else targetEnvelope H (finiteNode n)) = finiteTargetEnvelope := by
    simp [finiteTargetEnvelope,Fin.sum_univ_succ]
  exact hb.trans ((he2 ▸ finiteTargetEnvelope_bound.le).trans (by norm_num [finiteResidualBound]))

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
lemma taylorPhase1_0_mem (j : Fin 31) : (taylorPhase1_0 j).Mem (taylorPhase 1 0 (frequency j)) := by
  rw [← taylorPhase1_0_calc]
  exact taylorPhaseBox_mem 1 0 j
lemma taylorPhase1_1_mem (j : Fin 31) : (taylorPhase1_1 j).Mem (taylorPhase 1 1 (frequency j)) := by
  rw [← taylorPhase1_1_calc]
  exact taylorPhaseBox_mem 1 1 j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_VariationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma dVariation_lt : dVariation < 119 := by
  have hx := ri_mem_lt dVariationBox_mem 119 1 (by norm_num) (by decide +kernel)
  simpa using hx
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CoefficientSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma tail_pair_norm119 (n : Node) (u v : ℝ) :
    ‖(u:ℂ) • spectralCCLM n+(v:ℂ) • spectralDCLM n‖ ≤ 119*(|u|+|v|) := by
  have h0 := (spectralCCLM_norm n).trans cVariation_lt.le
  have h1 := (spectralDCLM_norm n).trans dVariation_lt.le
  have hsum := norm_add_le ((u:ℂ) • spectralCCLM n) ((v:ℂ) • spectralDCLM n)
  have hsm := add_le_add (complex_smul_clm_bound u (spectralCCLM n))
    (complex_smul_clm_bound v (spectralDCLM n))
  have hh : ‖(u:ℂ) • spectralCCLM n+(v:ℂ) • spectralDCLM n‖ ≤
      |u| * ‖spectralCCLM n‖+|v| * ‖spectralDCLM n‖ := by
    exact hsum.trans hsm
  nlinarith [mul_le_mul_of_nonneg_left h0 (abs_nonneg u),mul_le_mul_of_nonneg_left h1 (abs_nonneg v)]
lemma tailSeries_norm (w : TailCoefficients) :
    ‖∑' n : TailNode, ((w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val)‖ ≤ 119*‖w‖ := by
  have hh := norm_series_bound (fun n : TailNode => (w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val)
    (fun n => |w (n,0)|+|w (n,1)|) (tail_pairs_summable w) 119
    (fun n => tail_pair_norm119 n.val (w (n,0)) (w (n,1)))
  rw [tail_pairs_norm] at hh
  exact hh
lemma tailSpectral_zero_constant_norm (a : TrigonometricCoefficients) (w : TailCoefficients) :
    ‖tailSpectral (coefficientInput 0 a w)‖ ≤ 119*‖w‖ := by
  rw [tailSpectral_zero_constant]
  exact tailSeries_norm w
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_CurvatureEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.FiniteCertificate

lemma tailSpectral_curvature (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (i : Fin 5) {s : ℝ} (hs : curvaturePoint i≤ s) :
    ‖tailSpectral (coefficientInput 0 a w) (waveFunctionJet 0 br 2 s)‖≤119*‖w‖*tailCurvatureCap br i := by
  exact ((tailSpectral _).le_opNorm _).trans (mul_le_mul (tailSpectral_zero_constant_norm a w)
    (waveFunctionJet_uniform _ _ _ (tailCurvatureCap_nonneg br i) (fun t ht => tailCurvatureCap_bound br i hs ht))
    (norm_nonneg _) (by positivity))
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

lemma cBasis_at_node (n : Node) : (cBasis n n.val).re = Q n.val := by
  have hh := (factor_second_third (cBasis n) (differentiable_cBasis n) n.val).1
  rw [← P_cBasis n] at hh
  have he := congrArg Complex.re hh
  rw [← waveDerivative_eq_iterated] at he
  norm_num [Complex.mul_re] at he
  unfold Q
  linarith
lemma cBasis_deriv_at_node (n : Node) : 6*(deriv (cBasis n) n.val).re =
    (waveDerivative 3 n.val).re := by
  have hh := (factor_second_third (cBasis n) (differentiable_cBasis n) n.val).2
  rw [← P_cBasis n,← waveDerivative_eq_iterated] at hh
  have he := congrArg Complex.re hh
  simpa using he.symm

lemma deriv_cBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) :
    deriv (cBasis n) m.val = 0 := by
  have hh := ((((hasDerivAt_id (m.val:ℂ)).sub_const (n.val:ℂ)).pow 2).mul
    ((differentiable_cBasis n _).hasDerivAt)).deriv
  change deriv (fun s => (s-(n.val:ℂ))^2*cBasis n s) m.val = _ at hh
  rw [← P_cBasis n,deriv_P_node m,cBasis_other_node hmn] at hh
  have hne : ((m.val:ℂ)-(n.val:ℂ))^2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (by exact_mod_cast hmn))
  have hzero : ((m.val:ℂ)-(n.val:ℂ))^2 * deriv (cBasis n) m.val = 0 := by simpa using hh.symm
  exact (mul_eq_zero.mp hzero).resolve_left hne
lemma deriv_dBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) :
    deriv (dBasis n) m.val = 0 := by
  have hh := (((hasDerivAt_id (m.val:ℂ)).sub_const (n.val:ℂ)).mul
    ((differentiable_cBasis n _).hasDerivAt)).deriv
  change deriv (fun s => (s-(n.val:ℂ))*cBasis n s) m.val = _ at hh
  rw [← dBasis_cBasis n,cBasis_other_node hmn,deriv_cBasis_other_node hmn] at hh
  simpa using hh

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_DirectWaveJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma spectralC_direct (n : Node) (s : ℂ) :
    spectralCCLM n (waveFunctionJet 0 0 0 s)=cBasis n s ∧
    spectralCCLM n (waveFunctionJet 0 0 1 s)=deriv (cBasis n) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,spectralCCLM_apply,spectralC_phase]
  · have he : (fun s => spectralCCLM n (phaseFunction s))=cBasis n := funext fun s => by rw [spectralCCLM_apply,spectralC_phase]
    have hh := ((spectralCCLM n).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma cBasis_deriv_re (n : Node) : (deriv (cBasis n) n.val).re=Q n.val*D n.val := by
  have hQ : Q n.val≠0 := (lt_trans (by norm_num) (FiniteCertificate.Q_node_bounds n.val n.property.2).1).ne'
  have hh := cBasis_deriv_at_node n
  unfold D
  field_simp
  linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_DirectCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma spectralC_directJet (n m : Node) (d : Fin 2) :
    (spectralCCLM m (directJetFunction 0 h n.val d)).re=
      if n.val=m.val ∧ d.val=0 then -1 else 0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralC_direct m _).1,(spectralC_direct m _).2]
  simp only [damping,Fin.val_zero,↓reduceIte,sub_self,mul_zero,zero_mul,Real.exp_zero,sub_zero]
  by_cases hm : n=m
  · subst m
    rw [cBasis_at_node,cBasis_deriv_re]
    by_cases hd : d.val=0
    · simp only [hd,↓reduceIte,and_self]
      field_simp [Q_node_ne n]
    · simp only [hd,↓reduceIte,and_false]
      ring
  · have hmn : n.val≠m.val := fun he => hm (Subtype.ext he)
    rw [cBasis_other_node hmn,deriv_cBasis_other_node hmn]
    simp [hmn]
lemma spectralD_directJet (n m : Node) (d : Fin 2) :
    (spectralDCLM m (directJetFunction 0 h n.val d)).re=
      if n.val=m.val ∧ d.val=1 then -1 else 0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralD_direct m _).1,(spectralD_direct m _).2]
  simp only [damping,Fin.val_zero,↓reduceIte,sub_self,mul_zero,zero_mul,Real.exp_zero,sub_zero]
  by_cases hm : n=m
  · subst m
    have hd0 : dBasis n n.val=0 := by rw [dBasis_cBasis]; simp
    rw [hd0,deriv_dBasis_at_node,cBasis_at_node]
    fin_cases d <;> simp only [Nat.one_ne_zero,↓reduceIte,zero_re,mul_zero,zero_sub,neg_zero,mul_zero,and_true]
    · norm_num
    · field_simp [Q_node_ne n]
  · have hmn : n.val≠m.val := fun he => hm (Subtype.ext he)
    rw [dBasis_other_node hmn,deriv_dBasis_other_node hmn]
    simp [hmn]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_SpectralProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate

lemma tailColumnSpectral_norm (p : TailNode × Fin 2) : ‖tailColumnSpectral p‖≤119 := by
  unfold tailColumnSpectral
  split_ifs
  · exact (spectralCCLM_norm _).trans cVariation_lt.le
  · exact (spectralDCLM_norm _).trans dVariation_lt.le
lemma summable_tail_columns (w : TailCoefficients) :
    Summable (fun p => (w p:ℂ) • tailColumnSpectral p) := by
  exact summable_l1_complex_smul w tailColumnSpectral 119 tailColumnSpectral_norm
lemma tailSpectral_product (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) :
    tailSpectral (coefficientInput C a w)= (C:ℂ) • spectralPCLM+
      ∑' p : TailNode × Fin 2,(w p:ℂ) • tailColumnSpectral p := by
  have he := tsum_prod_fin_two (fun p => (w p:ℂ) • tailColumnSpectral p) (summable_tail_columns w)
  rw [he,tailSpectral_coefficient]
  rfl
lemma summable_tail_columns_apply (w : TailCoefficients) (f : C(Spectrum,ℂ)) :
    Summable (fun p => (w p:ℂ)*tailColumnSpectral p f) := by
  simpa only [ContinuousLinearMap.apply_apply,smul_apply,smul_eq_mul] using
    ((ContinuousLinearMap.apply ℂ ℂ f).summable (summable_tail_columns w))
lemma tailSpectral_product_apply (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (f : C(Spectrum,ℂ)) :
    tailSpectral (coefficientInput C a w) f=(C:ℂ)*spectralP f+
      ∑' p : TailNode × Fin 2,(w p:ℂ)*tailColumnSpectral p f := by
  rw [tailSpectral_product,add_apply,smul_apply,smul_eq_mul,spectralPCLM_apply]
  congr 1
  exact (ContinuousLinearMap.apply ℂ ℂ f).map_tsum (summable_tail_columns w)
lemma tailSpectral_jet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) :
    (tailSpectral (coefficientInput C a w) (jetFunction q v m d)).re=
      C*jet (damping q) v m d (finiteColumn 22)+
      ∑' p : TailNode × Fin 2,w p*tailJet (damping q) v m p.1.val.val p.2 d := by
  rw [tailSpectral_product_apply,add_re,re_tsum (summable_tail_columns_apply _ _)]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,spectralP_jet,tailColumnSpectral_jet]
lemma inputJJet_negative_coefficient (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (v : ℝ) (n : ℤ) (d : Fin 2) :
    (negativeJet v n d (inputJJet (coefficientInput C a w) 1 0 n)
      (inputJJet (coefficientInput C a w) 1 1 n)).re=
      C*jet h v n d (finiteColumn 22)+
      (∑' p : TailNode × Fin 2,w p*tailJet h v n p.1.val.val p.2 d)+
      ∑ c : Fin 22,a c*jet H v n d (finiteColumn ⟨c.val,by omega⟩) := by
  rw [inputJJet_negative,add_re,tailSpectral_jet,finiteSpectral_jet]
  rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_TailCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
attribute [local instance] Classical.propDecidable
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma tailColumnSpectral_directJet (p q : TailNode × Fin 2) :
    (tailColumnSpectral q (directJetFunction 0 h p.1.val.val p.2)).re=if q=p then -1 else 0 := by
  unfold tailColumnSpectral
  by_cases hc : q.2.val=0
  · simp only [hc,↓reduceIte,spectralC_directJet]
    congr 1
    apply propext
    constructor
    · rintro ⟨hn,hd⟩
      apply Prod.ext
      · exact Subtype.ext (Subtype.ext hn.symm)
      · exact Fin.ext (hc.trans hd.symm)
    · intro he; subst q; exact ⟨rfl,hc⟩
  · simp only [hc,↓reduceIte,spectralD_directJet]
    have hc1 : q.2.val=1 := by omega
    congr 1
    apply propext
    constructor
    · rintro ⟨hn,hd⟩
      apply Prod.ext
      · exact Subtype.ext (Subtype.ext hn.symm)
      · exact Fin.ext (hc1.trans hd.symm)
    · intro he; subst q; exact ⟨rfl,hc1⟩
lemma tailSpectral_tail_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (p : TailNode × Fin 2) :
    (tailSpectral (coefficientInput C a w) (directJetFunction 0 h p.1.val.val p.2)).re= -w p := by
  rw [tailSpectral_product_apply,add_re,re_tsum (summable_tail_columns_apply _ _)]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,←spectralPCLM_apply,
    spectralP_directJet,tailColumnSpectral_directJet,mul_zero,zero_add,mul_ite,mul_neg,mul_one,
    tsum_ite_eq]
lemma spectralC_other_directJet (q : Fin 2) (v : ℝ) (n m : Node) (hne : n.val≠m.val) (d : Fin 2) :
    (spectralCCLM m (directJetFunction q v n.val d)).re=0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralC_direct m _).1,(spectralC_direct m _).2,
    cBasis_other_node hne,deriv_cBasis_other_node hne]
  split_ifs <;> simp
lemma spectralD_other_directJet (q : Fin 2) (v : ℝ) (n m : Node) (hne : n.val≠m.val) (d : Fin 2) :
    (spectralDCLM m (directJetFunction q v n.val d)).re=0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralD_direct m _).1,(spectralD_direct m _).2,
    dBasis_other_node hne,deriv_dBasis_other_node hne]
  split_ifs <;> simp
lemma tailColumnSpectral_other_directJet (n : Node) (hn : n.val∈FiniteNodes)
    (q : TailNode × Fin 2) (v : ℝ) (d : Fin 2) :
    (tailColumnSpectral q (directJetFunction 0 v n.val d)).re=0 := by
  have hne : n.val≠q.1.val.val := fun he => q.1.property (he ▸ hn)
  unfold tailColumnSpectral
  split_ifs
  · exact spectralC_other_directJet _ _ _ _ hne _
  · exact spectralD_other_directJet _ _ _ _ hne _
lemma tailSpectral_finite_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (n : Node) (hn : n.val∈FiniteNodes) (v : ℝ) (d : Fin 2) :
    (tailSpectral (coefficientInput C a w) (directJetFunction 0 v n.val d)).re=0 := by
  rw [tailSpectral_product_apply,add_re,re_tsum (summable_tail_columns_apply _ _)]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,←spectralPCLM_apply,
    spectralP_directJet,tailColumnSpectral_other_directJet n hn,mul_zero,zero_add,tsum_zero]
lemma inputJJet_tail_direct_negative (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (p : TailNode × Fin 2) :
    (negativeJet h p.1.val.val p.2 (inputJJet (coefficientInput C a w) 0 0 p.1.val.val)
      (inputJJet (coefficientInput C a w) 0 1 p.1.val.val)).re= -w p-AallOperator a p := by
  rw [inputJJet_direct_negative,add_re,tailSpectral_tail_directJet,finiteSpectral_tail_directJet]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma inputJJet_row_direct_negative (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (i : Fin 20) :
    (negativeJet H (rowNode i).val (rowDerivative i) (inputJJet (coefficientInput C a w) 0 0 (rowNode i).val)
      (inputJJet (coefficientInput C a w) 0 1 (rowNode i).val)).re= -a ⟨i.val+2,by omega⟩ := by
  rw [inputJJet_direct_negative,add_re,tailSpectral_finite_directJet C a w _ (rowNode_mem i),
    finiteSpectral_row_directJet,zero_add]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
lemma inputJJet_row_transformed (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) (i : Fin 20) :
    (negativeJet H (rowNode i).val (rowDerivative i) (inputJJet (coefficientInput C a w) 1 0 (rowNode i).val)
      (inputJJet (coefficientInput C a w) 1 1 (rowNode i).val)).re=
    Boperator w i + C*jet h H (rowNode i).val (rowDerivative i) (finiteColumn 22)+
      (∑ c : Fin 22,a c*jet H H (rowNode i).val (rowDerivative i) (finiteColumn ⟨c.val,by omega⟩)) := by
  rw [inputJJet_negative_coefficient]
  have hb : Boperator w i=∑' p : TailNode × Fin 2,w p*tailJet h H (rowNode i).val p.1.val.val p.2 (rowDerivative i) := by
    unfold Boperator
    erw [operator_apply]
    rfl
  rw [hb]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_Realness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma inputComplex_re (a : InputCoefficients) (x : Plane) : (inputComplex a x).re = inputSchwartz a x := by
  rw [inputSchwartz_apply]
  simp [inputComplex,Complex.mul_re,← Complex.ofReal_mul,← Complex.ofReal_neg,Complex.exp_ofReal_re]
lemma inputComplex_eq (a : InputCoefficients) (x : Plane) : inputComplex a x = (inputSchwartz a x:ℂ) := by
  rw [← inputComplex_re]
  exact (Complex.conj_eq_iff_re.mp (inputComplex_real a x)).symm

lemma complexInputSchwartz_apply (a : InputCoefficients) (x : Plane) :
    complexInputSchwartz a x = inputComplex a x := by
  exact (inputComplex_eq a x).symm

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_FourierPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma fourier_inputComplex (a : InputCoefficients) : 𝓕 (inputComplex a) = outputComplex a := by
  ext w
  simp only [Real.fourier_eq,inputComplex_spectral,smul_add]
  rw [integral_add ((Real.fourierIntegral_convergent_iff w).mpr (integrable_spectral (tailSpectral a) h_pos))
    ((Real.fourierIntegral_convergent_iff w).mpr (integrable_spectral (finiteSpectral a) H_pos))]
  change 𝓕 (fun x => exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailSpectral a (phaseFunction (radial x:ℂ))) w +
    𝓕 (fun x => exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteSpectral a (phaseFunction (radial x:ℂ))) w = _
  rw [fourier_spectral _ h_pos h,fourier_spectral _ H_pos h]
  simp only [outputComplex,transformedInput,mul_add]

lemma coe_complexInputSchwartz (a : InputCoefficients) :
    (complexInputSchwartz a : Plane → ℂ) = inputComplex a := funext (complexInputSchwartz_apply a)
lemma coe_fourier_input (a : InputCoefficients) :
    ((𝓕 (complexInputSchwartz a) : 𝓢(Plane,ℂ)) : Plane → ℂ) = outputComplex a := by
  rw [SchwartzMap.fourier_coe,coe_complexInputSchwartz,fourier_inputComplex]
lemma outputComplex_real (a : InputCoefficients) (x : Plane) : conj (outputComplex a x) = outputComplex a x := by
  rw [← fourier_inputComplex]
  exact fourier_conj_even _ (inputComplex_real a) (inputComplex_even a) x
lemma fourier_outputComplex (a : InputCoefficients) : 𝓕 (outputComplex a) = inputComplex a := by
  have hh := (complexInputSchwartz a).continuous.fourierInv_fourier_eq
    (complexInputSchwartz a).integrable (𝓕 (complexInputSchwartz a)).integrable
  rw [coe_complexInputSchwartz,fourier_inputComplex,Real.fourierInv_eq_fourier_comp_neg] at hh
  have he : (fun x => outputComplex a (-x)) = outputComplex a := by
    ext x
    exact outputComplex_radial a (-x) x (norm_neg x)
  rwa [he] at hh

lemma pairSchwartz_apply (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairSchwartz a₁ a₂ x = (pairComplex a₁ a₂ x).re := by
  simp only [pairSchwartz,SchwartzMap.postcompCLM_apply,Complex.reCLM_apply,add_apply,
    coe_fourier_input,complexInputSchwartz_apply,pairComplex,Pi.add_apply]
lemma pairComplex_real (a₁ a₂ : InputCoefficients) (x : Plane) : conj (pairComplex a₁ a₂ x) = pairComplex a₁ a₂ x := by
  simp only [pairComplex,Pi.add_apply,map_add,inputComplex_real,outputComplex_real]
lemma pairComplex_eq (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairComplex a₁ a₂ x = (pairSchwartz a₁ a₂ x:ℂ) := by
  rw [pairSchwartz_apply]
  exact (Complex.conj_eq_iff_re.mp (pairComplex_real a₁ a₂ x)).symm
lemma fourier_pairComplex (a₁ a₂ : InputCoefficients) : 𝓕 (pairComplex a₁ a₂) = pairComplex a₂ a₁ := by
  have hi : Integrable (inputComplex a₁) := by
    rw [← coe_complexInputSchwartz]
    exact (complexInputSchwartz a₁).integrable
  have ho : Integrable (outputComplex a₂) := by
    rw [← coe_fourier_input]
    exact (𝓕 (complexInputSchwartz a₂)).integrable
  ext w
  simp only [pairComplex,Pi.add_apply,Real.fourier_eq,smul_add]
  rw [integral_add ((Real.fourierIntegral_convergent_iff w).mpr hi)
    ((Real.fourierIntegral_convergent_iff w).mpr ho)]
  change 𝓕 (inputComplex a₁) w + 𝓕 (outputComplex a₂) w = _
  rw [fourier_inputComplex,fourier_outputComplex]
  exact add_comm _ _
lemma pairSchwartz_fourier (a₁ a₂ : InputCoefficients) (w : Plane) :
    realFourier (pairSchwartz a₁ a₂) w = (pairSchwartz a₂ a₁ w:ℂ) := by
  simp only [realFourier,← pairComplex_eq]
  rw [fourier_pairComplex,pairComplex_eq]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma spectrum0_0_0_calc (r : Fin 8) : spectrumBox 0 0 0 r = spectrum0_0_0 r := by
  revert r
  decide +kernel
lemma spectrum0_0_1_calc (r : Fin 8) : spectrumBox 0 0 1 r = spectrum0_0_1 r := by
  revert r
  decide +kernel
lemma spectrum0_0_2_calc (r : Fin 8) : spectrumBox 0 0 2 r = spectrum0_0_2 r := by
  revert r
  decide +kernel
lemma spectrum0_0_3_calc (r : Fin 8) : spectrumBox 0 0 3 r = spectrum0_0_3 r := by
  revert r
  decide +kernel
lemma spectrum0_0_4_calc (r : Fin 8) : spectrumBox 0 0 4 r = spectrum0_0_4 r := by
  revert r
  decide +kernel
lemma spectrum0_0_5_calc (r : Fin 8) : spectrumBox 0 0 5 r = spectrum0_0_5 r := by
  revert r
  decide +kernel
lemma spectrum0_0_6_calc (r : Fin 8) : spectrumBox 0 0 6 r = spectrum0_0_6 r := by
  revert r
  decide +kernel
lemma spectrum0_0_7_calc (r : Fin 8) : spectrumBox 0 0 7 r = spectrum0_0_7 r := by
  revert r
  decide +kernel
lemma spectrum0_0_8_calc (r : Fin 8) : spectrumBox 0 0 8 r = spectrum0_0_8 r := by
  revert r
  decide +kernel
lemma spectrum0_0_9_calc (r : Fin 8) : spectrumBox 0 0 9 r = spectrum0_0_9 r := by
  revert r
  decide +kernel
lemma spectrum0_0_10_calc (r : Fin 8) : spectrumBox 0 0 10 r = spectrum0_0_10 r := by
  revert r
  decide +kernel
lemma spectrum0_0_11_calc (r : Fin 8) : spectrumBox 0 0 11 r = spectrum0_0_11 r := by
  revert r
  decide +kernel
lemma spectrum0_0_12_calc (r : Fin 8) : spectrumBox 0 0 12 r = spectrum0_0_12 r := by
  revert r
  decide +kernel
lemma spectrum0_0_13_calc (r : Fin 8) : spectrumBox 0 0 13 r = spectrum0_0_13 r := by
  revert r
  decide +kernel
lemma spectrum0_0_14_calc (r : Fin 8) : spectrumBox 0 0 14 r = spectrum0_0_14 r := by
  revert r
  decide +kernel
lemma spectrum0_0_15_calc (r : Fin 8) : spectrumBox 0 0 15 r = spectrum0_0_15 r := by
  revert r
  decide +kernel
lemma spectrum0_0_16_calc (r : Fin 8) : spectrumBox 0 0 16 r = spectrum0_0_16 r := by
  revert r
  decide +kernel
lemma spectrum0_0_17_calc (r : Fin 8) : spectrumBox 0 0 17 r = spectrum0_0_17 r := by
  revert r
  decide +kernel
lemma spectrum0_0_18_calc (r : Fin 8) : spectrumBox 0 0 18 r = spectrum0_0_18 r := by
  revert r
  decide +kernel
lemma spectrum0_0_19_calc (r : Fin 8) : spectrumBox 0 0 19 r = spectrum0_0_19 r := by
  revert r
  decide +kernel
lemma spectrum0_0_20_calc (r : Fin 8) : spectrumBox 0 0 20 r = spectrum0_0_20 r := by
  revert r
  decide +kernel
lemma spectrum0_0_21_calc (r : Fin 8) : spectrumBox 0 0 21 r = spectrum0_0_21 r := by
  revert r
  decide +kernel
lemma spectrum0_0_22_calc (r : Fin 8) : spectrumBox 0 0 22 r = spectrum0_0_22 r := by
  revert r
  decide +kernel
lemma spectrum0_0_23_calc (r : Fin 8) : spectrumBox 0 0 23 r = spectrum0_0_23 r := by
  revert r
  decide +kernel
lemma spectrum0_0_24_calc (r : Fin 8) : spectrumBox 0 0 24 r = spectrum0_0_24 r := by
  revert r
  decide +kernel
lemma spectrum0_0_25_calc (r : Fin 8) : spectrumBox 0 0 25 r = spectrum0_0_25 r := by
  revert r
  decide +kernel
lemma spectrum0_0_26_calc (r : Fin 8) : spectrumBox 0 0 26 r = spectrum0_0_26 r := by
  revert r
  decide +kernel
lemma spectrum0_0_27_calc (r : Fin 8) : spectrumBox 0 0 27 r = spectrum0_0_27 r := by
  revert r
  decide +kernel
lemma spectrum0_0_28_calc (r : Fin 8) : spectrumBox 0 0 28 r = spectrum0_0_28 r := by
  revert r
  decide +kernel
lemma spectrum0_0_29_calc (r : Fin 8) : spectrumBox 0 0 29 r = spectrum0_0_29 r := by
  revert r
  decide +kernel
lemma spectrum0_0_30_calc (r : Fin 8) : spectrumBox 0 0 30 r = spectrum0_0_30 r := by
  revert r
  decide +kernel
lemma spectrum1_0_0_calc (r : Fin 8) : spectrumBox 1 0 0 r = spectrum1_0_0 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma inputComplex_radialJ (a : InputCoefficients) (x : Plane) :
    inputComplex a x=exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*inputJJet a 0 0 (radial x) := by
  rw [inputComplex_spectral,inputJJet,waveFunctionJet_zero_phase,waveFunctionJet_direct_zero]
  simp only [map_smul,smul_eq_mul,mul_add,←mul_assoc,damping,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  rw [←exp_add]
  congr 3
  ring
lemma pairComplex_radialJ (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairComplex a₁ a₂ x=exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*pairJJet a₁ a₂ 0 (radial x) := by
  simp only [pairComplex,Pi.add_apply,inputComplex_radialJ,outputComplex,pairJJet,inputJJet_transformed_zero,mul_add]
lemma pairSchwartz_radialJ (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairSchwartz a₁ a₂ x=Real.exp (-Real.pi*h*radial x)*pairJ a₁ a₂ (radial x) := by
  rw [pairSchwartz_apply,pairComplex_radialJ]
  have he : exp (-(Real.pi:ℂ)*h*(radial x:ℂ))=(Real.exp (-Real.pi*h*radial x):ℝ) := by simp
  rw [he,mul_re]
  simp only [ofReal_re,ofReal_im,zero_mul,sub_zero,pairJ]

end AtomicTriangular.Construction
end

end OAI
end


