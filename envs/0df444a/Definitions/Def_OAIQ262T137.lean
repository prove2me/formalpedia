-- Prove2me | Definitions.Def_OAIQ262T137
-- name    : OAIQ262T137
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:22:10.69272+00:00
-- url     : https://prove2.me/theorems/8fc28e9a-5ef6-441f-a3b2-8dbb9efa3214
-- title:
--   Definitions bundle OAIQ262T137 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 1 definition and 59 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.jetMultiplierBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_JetMatrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean), [`Triangular_Certificate_WaveIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean), [`Triangular_Certificate_WaveJetsData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean), [`Triangular_Envelope_EnvelopeNorm0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorm0.lean), [`Triangular_Envelope_EnvelopeNorm1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorm1.lean), [`Triangular_Envelope_EnvelopeNorm2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorm2.lean), [`Triangular_Envelope_EnvelopeNorms`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorms.lean), [`Triangular_Envelope_EnvelopePsiC`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiC.lean), [`Triangular_Envelope_EnvelopeWaves`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeWaves.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T085`, `OAIQ262T086`, `OAIQ262T087`, `OAIQ262T088`, `OAIQ262T089` and `OAIQ262T090` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T151`, `OAIQ262T152`, `OAIQ262T153`, `OAIQ262T154`, `OAIQ262T155`, `OAIQ262T156`, `OAIQ262T157`, `OAIQ262T158` and `OAIQ262T159`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T085
import Definitions.Def_OAIQ262T086
import Definitions.Def_OAIQ262T087
import Definitions.Def_OAIQ262T088
import Definitions.Def_OAIQ262T089
import Definitions.Def_OAIQ262T090

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
namespace AtomicTriangular.Construction

theorem cBasis_eq (n : Node) {s : ℂ} (hs : s ≠ (n.val : ℂ)) :
    cBasis n s = P s / (s-n.val)^2 := by
  rw [cBasis, dslope_of_ne _ hs, slope_def_field, dBasis_node,
    sub_zero, dBasis_eq n hs, div_div, pow_two]

open Polynomial

end AtomicTriangular.Construction

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
lemma DBox0_mem : DBox0.Mem (D 0) := by
  rw [← DBox0_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_0_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox0_mem
  · left; decide +kernel
lemma DBox1_mem : DBox1.Mem (D 1) := by
  rw [← DBox1_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_1_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox1_mem
  · left; decide +kernel
lemma DBox3_mem : DBox3.Mem (D 3) := by
  rw [← DBox3_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_3_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox3_mem
  · left; decide +kernel
lemma DBox4_mem : DBox4.Mem (D 4) := by
  rw [← DBox4_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_4_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox4_mem
  · left; decide +kernel
lemma DBox7_mem : DBox7.Mem (D 7) := by
  rw [← DBox7_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_7_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox7_mem
  · left; decide +kernel
lemma DBox9_mem : DBox9.Mem (D 9) := by
  rw [← DBox9_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_9_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox9_mem
  · left; decide +kernel
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex
lemma dBox3_mem (j : Fin 31) : (dBox3 j).Mem (dCoefficient ⟨2,by norm_num⟩ j) := by
  rw [← dBox3_calc]
  apply dCoeffBox_mem ⟨2,by norm_num⟩ phaseBox3 restBox3
  · have hr : residue ⟨2,by norm_num⟩ = (3:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox3_mem
  · exact restBox3_mem
lemma dBox4_mem (j : Fin 31) : (dBox4 j).Mem (dCoefficient ⟨3,by norm_num⟩ j) := by
  rw [← dBox4_calc]
  apply dCoeffBox_mem ⟨3,by norm_num⟩ phaseBox4 restBox4
  · have hr : residue ⟨3,by norm_num⟩ = (4:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox4_mem
  · exact restBox4_mem
lemma dBox7_mem (j : Fin 31) : (dBox7 j).Mem (dCoefficient ⟨4,by norm_num⟩ j) := by
  rw [← dBox7_calc]
  apply dCoeffBox_mem ⟨4,by norm_num⟩ phaseBox7 restBox7
  · have hr : residue ⟨4,by norm_num⟩ = (7:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox7_mem
  · exact restBox7_mem
lemma dBox9_mem (j : Fin 31) : (dBox9 j).Mem (dCoefficient ⟨5,by norm_num⟩ j) := by
  rw [← dBox9_calc]
  apply dCoeffBox_mem ⟨5,by norm_num⟩ phaseBox9 restBox9
  · have hr : residue ⟨5,by norm_num⟩ = (9:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox9_mem
  · exact restBox9_mem
lemma dBox21_mem (j : Fin 31) : (dBox21 j).Mem (dCoefficient ⟨10,by norm_num⟩ j) := by
  rw [← dBox21_calc]
  apply dCoeffBox_mem ⟨10,by norm_num⟩ phaseBox21 restBox21
  · have hr : residue ⟨10,by norm_num⟩ = (21:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox21_mem
  · exact restBox21_mem
end AtomicTriangular.FiniteCertificate

end
end
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
def jetMultiplierBox (q : Fin 2) (i : Fin 20) (j : Fin 31) : CI :=
  let n : Fin 10 := ⟨i.val/2,by omega⟩
  (((CI.ofReal (QTable n).invPos).mul (lambdaTable q j)).mul (waveExpTable q n j)).mul
    (if i.val%2=0 then CI.point (-1) else (CI.ofReal (DTable n)).sub (phaseHTable q j))
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_JetMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnTable_mem (col : Fin 23) (j : Fin 31) : (columnTable col j).Mem (finiteColumn col j) := by
  fin_cases col
  · exact cBox0_mem j
  · exact dBox0_mem j
  · exact cBox1_mem j
  · exact dBox1_mem j
  · exact cBox3_mem j
  · exact dBox3_mem j
  · exact cBox4_mem j
  · exact dBox4_mem j
  · exact cBox7_mem j
  · exact dBox7_mem j
  · exact cBox9_mem j
  · exact dBox9_mem j
  · exact cBox12_mem j
  · exact dBox12_mem j
  · exact cBox13_mem j
  · exact dBox13_mem j
  · exact cBox16_mem j
  · exact dBox16_mem j
  · exact cBox19_mem j
  · exact dBox19_mem j
  · exact cBox21_mem j
  · exact dBox21_mem j
  · exact atomPolynomial_coeff_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeNorm0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnNorm0_mem (j : Fin 31) : (columnNorm0 j).Mem ‖finiteColumn 0 j‖ := by
  have hh := columnNorm0_check j
  exact CI.mem_norm (columnTable_mem 0 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm1_mem (j : Fin 31) : (columnNorm1 j).Mem ‖finiteColumn 1 j‖ := by
  have hh := columnNorm1_check j
  exact CI.mem_norm (columnTable_mem 1 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm2_mem (j : Fin 31) : (columnNorm2 j).Mem ‖finiteColumn 2 j‖ := by
  have hh := columnNorm2_check j
  exact CI.mem_norm (columnTable_mem 2 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm3_mem (j : Fin 31) : (columnNorm3 j).Mem ‖finiteColumn 3 j‖ := by
  have hh := columnNorm3_check j
  exact CI.mem_norm (columnTable_mem 3 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm4_mem (j : Fin 31) : (columnNorm4 j).Mem ‖finiteColumn 4 j‖ := by
  have hh := columnNorm4_check j
  exact CI.mem_norm (columnTable_mem 4 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm5_mem (j : Fin 31) : (columnNorm5 j).Mem ‖finiteColumn 5 j‖ := by
  have hh := columnNorm5_check j
  exact CI.mem_norm (columnTable_mem 5 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm6_mem (j : Fin 31) : (columnNorm6 j).Mem ‖finiteColumn 6 j‖ := by
  have hh := columnNorm6_check j
  exact CI.mem_norm (columnTable_mem 6 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm7_mem (j : Fin 31) : (columnNorm7 j).Mem ‖finiteColumn 7 j‖ := by
  have hh := columnNorm7_check j
  exact CI.mem_norm (columnTable_mem 7 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeNorm1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnNorm8_mem (j : Fin 31) : (columnNorm8 j).Mem ‖finiteColumn 8 j‖ := by
  have hh := columnNorm8_check j
  exact CI.mem_norm (columnTable_mem 8 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm9_mem (j : Fin 31) : (columnNorm9 j).Mem ‖finiteColumn 9 j‖ := by
  have hh := columnNorm9_check j
  exact CI.mem_norm (columnTable_mem 9 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm10_mem (j : Fin 31) : (columnNorm10 j).Mem ‖finiteColumn 10 j‖ := by
  have hh := columnNorm10_check j
  exact CI.mem_norm (columnTable_mem 10 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm11_mem (j : Fin 31) : (columnNorm11 j).Mem ‖finiteColumn 11 j‖ := by
  have hh := columnNorm11_check j
  exact CI.mem_norm (columnTable_mem 11 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm12_mem (j : Fin 31) : (columnNorm12 j).Mem ‖finiteColumn 12 j‖ := by
  have hh := columnNorm12_check j
  exact CI.mem_norm (columnTable_mem 12 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm13_mem (j : Fin 31) : (columnNorm13 j).Mem ‖finiteColumn 13 j‖ := by
  have hh := columnNorm13_check j
  exact CI.mem_norm (columnTable_mem 13 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm14_mem (j : Fin 31) : (columnNorm14 j).Mem ‖finiteColumn 14 j‖ := by
  have hh := columnNorm14_check j
  exact CI.mem_norm (columnTable_mem 14 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm15_mem (j : Fin 31) : (columnNorm15 j).Mem ‖finiteColumn 15 j‖ := by
  have hh := columnNorm15_check j
  exact CI.mem_norm (columnTable_mem 15 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeNorm2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnNorm16_mem (j : Fin 31) : (columnNorm16 j).Mem ‖finiteColumn 16 j‖ := by
  have hh := columnNorm16_check j
  exact CI.mem_norm (columnTable_mem 16 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm17_mem (j : Fin 31) : (columnNorm17 j).Mem ‖finiteColumn 17 j‖ := by
  have hh := columnNorm17_check j
  exact CI.mem_norm (columnTable_mem 17 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm18_mem (j : Fin 31) : (columnNorm18 j).Mem ‖finiteColumn 18 j‖ := by
  have hh := columnNorm18_check j
  exact CI.mem_norm (columnTable_mem 18 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm19_mem (j : Fin 31) : (columnNorm19 j).Mem ‖finiteColumn 19 j‖ := by
  have hh := columnNorm19_check j
  exact CI.mem_norm (columnTable_mem 19 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm20_mem (j : Fin 31) : (columnNorm20 j).Mem ‖finiteColumn 20 j‖ := by
  have hh := columnNorm20_check j
  exact CI.mem_norm (columnTable_mem 20 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm21_mem (j : Fin 31) : (columnNorm21 j).Mem ‖finiteColumn 21 j‖ := by
  have hh := columnNorm21_check j
  exact CI.mem_norm (columnTable_mem 21 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm22_mem (j : Fin 31) : (columnNorm22 j).Mem ‖finiteColumn 22 j‖ := by
  have hh := columnNorm22_check j
  exact CI.mem_norm (columnTable_mem 22 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
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
lemma columnNormTable_mem (c : Fin 23) (j : Fin 31) : (columnNormTable c j).Mem ‖finiteColumn c j‖ := by
  fin_cases c
  · exact columnNorm0_mem j
  · exact columnNorm1_mem j
  · exact columnNorm2_mem j
  · exact columnNorm3_mem j
  · exact columnNorm4_mem j
  · exact columnNorm5_mem j
  · exact columnNorm6_mem j
  · exact columnNorm7_mem j
  · exact columnNorm8_mem j
  · exact columnNorm9_mem j
  · exact columnNorm10_mem j
  · exact columnNorm11_mem j
  · exact columnNorm12_mem j
  · exact columnNorm13_mem j
  · exact columnNorm14_mem j
  · exact columnNorm15_mem j
  · exact columnNorm16_mem j
  · exact columnNorm17_mem j
  · exact columnNorm18_mem j
  · exact columnNorm19_mem j
  · exact columnNorm20_mem j
  · exact columnNorm21_mem j
  · exact columnNorm22_mem j
lemma fourierNorm_mem (j : Fin 31) : (columnNorm22 j).Mem ‖fourierCoeff j‖ := columnNorm22_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma lambdaNorm1_mem (j : Fin 31) : (lambdaNorm1 j).Mem ‖lambda (damping 1) (frequency j)‖ := by
  have hh := lambdaNorm1_check j
  exact CI.mem_norm (lambdaTable_mem 1 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma phaseNorm10_mem (j : Fin 31) : (phaseNorm10 j).Mem ‖I*Real.pi*zeta (damping 1) (damping 0) (frequency j)‖ := by
  have hh := phaseNorm10_check j
  exact CI.mem_norm (envelopePhase10_mem j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
end AtomicTriangular.FiniteCertificate
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
lemma envelopeExpC36_mem (j : Fin 31) : (envelopeExpC36 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*36)) := by
  rw [← envelopeExpC36_calc]
  have hh := decayExpBox_mem 1 0 36 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC36_pre j)
lemma psiC36_calc (j : Fin 31) : psiBox 1 0 36 j QBox0 DBox0 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC36 j)=psiC36 j := by
  revert j
  decide +kernel
lemma psiC36_mem (j : Fin 31) : (psiC36 j).Mem (normJetEnvelope (damping 1) (damping 0) 36 (frequency j)) := by
  rw [← psiC36_calc]
  apply psiBox_mem
  · convert QBox0_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox0_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC36_mem j
  · decide +kernel
lemma envelopeExpC37_mem (j : Fin 31) : (envelopeExpC37 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*37)) := by
  rw [← envelopeExpC37_calc]
  have hh := decayExpBox_mem 1 0 37 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC37_pre j)
lemma psiC37_calc (j : Fin 31) : psiBox 1 0 37 j QBox1 DBox1 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC37 j)=psiC37 j := by
  revert j
  decide +kernel
lemma envelopeExpC39_mem (j : Fin 31) : (envelopeExpC39 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*39)) := by
  rw [← envelopeExpC39_calc]
  have hh := decayExpBox_mem 1 0 39 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC39_pre j)
lemma envelopeExpC40_mem (j : Fin 31) : (envelopeExpC40 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*40)) := by
  rw [← envelopeExpC40_calc]
  have hh := decayExpBox_mem 1 0 40 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC40_pre j)
lemma envelopeExpC43_mem (j : Fin 31) : (envelopeExpC43 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*43)) := by
  rw [← envelopeExpC43_calc]
  have hh := decayExpBox_mem 1 0 43 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC43_pre j)
lemma envelopeExpC45_mem (j : Fin 31) : (envelopeExpC45 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*45)) := by
  rw [← envelopeExpC45_calc]
  have hh := decayExpBox_mem 1 0 45 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC45_pre j)
lemma psiC25_mem (j : Fin 31) : (psiC25 j).Mem (normJetEnvelope (damping 1) (damping 0) 25 (frequency j)) := by
  rw [← psiC25_calc]
  apply psiBox_mem
  · exact QBox25_mem
  · exact DBox25_mem
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC25_mem j
  · decide +kernel
lemma envelopeExpC27_mem (j : Fin 31) : (envelopeExpC27 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*27)) := by
  rw [← envelopeExpC27_calc]
  have hh := decayExpBox_mem 1 0 27 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC27_pre j)
lemma psiC27_calc (j : Fin 31) : psiBox 1 0 27 j QBox27 DBox27 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC27 j)=psiC27 j := by
  revert j
  decide +kernel
lemma psiC27_mem (j : Fin 31) : (psiC27 j).Mem (normJetEnvelope (damping 1) (damping 0) 27 (frequency j)) := by
  rw [← psiC27_calc]
  apply psiBox_mem
  · exact QBox27_mem
  · exact DBox27_mem
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC27_mem j
  · decide +kernel
lemma envelopeExpC28_mem (j : Fin 31) : (envelopeExpC28 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*28)) := by
  rw [← envelopeExpC28_calc]
  have hh := decayExpBox_mem 1 0 28 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC28_pre j)
lemma psiC28_calc (j : Fin 31) : psiBox 1 0 28 j QBox28 DBox28 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC28 j)=psiC28 j := by
  revert j
  decide +kernel
lemma psiC28_mem (j : Fin 31) : (psiC28 j).Mem (normJetEnvelope (damping 1) (damping 0) 28 (frequency j)) := by
  rw [← psiC28_calc]
  apply psiBox_mem
  · exact QBox28_mem
  · exact DBox28_mem
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC28_mem j
  · decide +kernel
lemma envelopeExpC31_mem (j : Fin 31) : (envelopeExpC31 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*31)) := by
  rw [← envelopeExpC31_calc]
  have hh := decayExpBox_mem 1 0 31 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC31_pre j)
lemma psiC31_calc (j : Fin 31) : psiBox 1 0 31 j QBox31 DBox31 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC31 j)=psiC31 j := by
  revert j
  decide +kernel
lemma psiC31_mem (j : Fin 31) : (psiC31 j).Mem (normJetEnvelope (damping 1) (damping 0) 31 (frequency j)) := by
  rw [← psiC31_calc]
  apply psiBox_mem
  · exact QBox31_mem
  · exact DBox31_mem
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC31_mem j
  · decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


