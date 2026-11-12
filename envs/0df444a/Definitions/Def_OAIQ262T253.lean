-- Prove2me | Definitions.Def_OAIQ262T253
-- name    : OAIQ262T253
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T21:00:34.120958+00:00
-- url     : https://prove2.me/theorems/51f7c352-35ae-4396-9a1d-2068d35d477e
-- title:
--   Definitions bundle OAIQ262T253 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 4 definitions and 95 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.actualInput`, `OAI.AtomicTriangular.Construction.actualJ`, `OAI.AtomicTriangular.Construction.actualJ0`, `OAI.AtomicTriangular.Construction.actualTrigonometric`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_Inverse`, `Triangular_Certificate_JetMatrix`, `Triangular_Certificate_ParamA`, `Triangular_Certificate_ParamInterval`, `Triangular_Certificate_ParamNorm`, `Triangular_Certificate_ParamRHS`, `Triangular_Certificate_ParamU`, `Triangular_Construction_ActualCorrection`, `Triangular_Construction_ActualInput`, `Triangular_Construction_ActualInterpolation`, `Triangular_Construction_BlockOperators`, `Triangular_Construction_ConcreteSchur`, `Triangular_Construction_CurvatureBoxes`, `Triangular_Construction_CurvatureEnvelope`, `Triangular_Construction_CurvatureSums`, `Triangular_Construction_FarCurvature`, `Triangular_Construction_FiniteInterpolation`, `Triangular_Envelope_EnvelopeSums`, `Triangular_Envelope_KernelBounds`, `Triangular_Signs_RemainderNorm`, `Triangular_Taylor_CurvatureData00`, `Triangular_Taylor_CurvatureData10`, `Triangular_Taylor_CurvatureData11`, `Triangular_Taylor_TaylorPhase`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T193` and `OAIQ262T194` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T259` and `OAIQ262T260`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T193
import Definitions.Def_OAIQ262T194

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
lemma R0Box_mem (i : Fin 20) (j : Fin 3) : (R0Box i j).Mem (Construction.R0 i j) :=
  jetMatrixTable_mem i (if j.val<2 then ⟨j.val,by omega⟩ else 22)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
lemma minusInverse_error : matNorm ((1 - Construction.R)⁻¹-minusApprox) ≤ (1:ℝ)/10^23 := by
  exact (inverse_error_of_residual _ _ (16155/1000) ((1:ℝ)/10^26)
    minusApprox_bound minusResidual_bound (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num)
lemma minusInverseBox_mem (i j : Fin 20) :
    (minusInverseBox i j).Mem (((1 - Construction.R)⁻¹) i j) := by
  apply RI.mem_widen (minusApproxBox_mem i j)
  have hh := (matrixEntry_le_norm ((1 - Construction.R)⁻¹-minusApprox) i j).trans minusInverse_error
  norm_num [scale] at hh ⊢
  exact hh

lemma plusInverseBox_mem (i j : Fin 20) :
    (plusInverseBox i j).Mem (((1 + Construction.R)⁻¹) i j) := by
  apply RI.mem_widen (plusApproxBox_mem i j)
  have hh := (matrixEntry_le_norm ((1 + Construction.R)⁻¹-plusApprox) i j).trans plusInverse_error
  norm_num [scale] at hh ⊢
  exact hh

end AtomicTriangular.FiniteCertificate
end

end OAI
end

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
lemma rhsPlusBox_mem (i : Fin 20) (j : Fin 8) :
    (rhsPlusBox i j).Mem ((Yf+Construction.R0*(gamma 1+gamma 0)) i j) :=
  RI.mem_add (YfBox_mem i j) (matrixMul_mem R0Box_mem (fun k j => RI.mem_add (gammaBox_mem 1 k j) (gammaBox_mem 0 k j)) i j)
lemma rhsMinusBox_mem (i : Fin 20) (j : Fin 8) :
    (rhsMinusBox i j).Mem ((Yf+Construction.R0*(gamma 1-gamma 0)) i j) :=
  RI.mem_add (YfBox_mem i j) (matrixMul_mem R0Box_mem (fun k j => RI.mem_sub (gammaBox_mem 1 k j) (gammaBox_mem 0 k j)) i j)

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
lemma rhsPlusTableRow0_calc (j : Fin 8) : rhsPlusBox 0 j = rhsPlusTableRow0 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow1_calc (j : Fin 8) : rhsPlusBox 1 j = rhsPlusTableRow1 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow2_calc (j : Fin 8) : rhsPlusBox 2 j = rhsPlusTableRow2 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow3_calc (j : Fin 8) : rhsPlusBox 3 j = rhsPlusTableRow3 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow4_calc (j : Fin 8) : rhsPlusBox 4 j = rhsPlusTableRow4 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow5_calc (j : Fin 8) : rhsPlusBox 5 j = rhsPlusTableRow5 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow6_calc (j : Fin 8) : rhsPlusBox 6 j = rhsPlusTableRow6 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow7_calc (j : Fin 8) : rhsPlusBox 7 j = rhsPlusTableRow7 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow8_calc (j : Fin 8) : rhsPlusBox 8 j = rhsPlusTableRow8 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow9_calc (j : Fin 8) : rhsPlusBox 9 j = rhsPlusTableRow9 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow10_calc (j : Fin 8) : rhsPlusBox 10 j = rhsPlusTableRow10 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow11_calc (j : Fin 8) : rhsPlusBox 11 j = rhsPlusTableRow11 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow12_calc (j : Fin 8) : rhsPlusBox 12 j = rhsPlusTableRow12 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow13_calc (j : Fin 8) : rhsPlusBox 13 j = rhsPlusTableRow13 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow14_calc (j : Fin 8) : rhsPlusBox 14 j = rhsPlusTableRow14 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow15_calc (j : Fin 8) : rhsPlusBox 15 j = rhsPlusTableRow15 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow16_calc (j : Fin 8) : rhsPlusBox 16 j = rhsPlusTableRow16 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow17_calc (j : Fin 8) : rhsPlusBox 17 j = rhsPlusTableRow17 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow18_calc (j : Fin 8) : rhsPlusBox 18 j = rhsPlusTableRow18 j := by
  revert j
  decide +kernel
lemma rhsPlusTableRow19_calc (j : Fin 8) : rhsPlusBox 19 j = rhsPlusTableRow19 j := by
  revert j
  decide +kernel
lemma rhsPlusTable_calc (i : Fin 20) (j : Fin 8) : rhsPlusBox i j = rhsPlusTable i j := by
  fin_cases i
  · exact rhsPlusTableRow0_calc j
  · exact rhsPlusTableRow1_calc j
  · exact rhsPlusTableRow2_calc j
  · exact rhsPlusTableRow3_calc j
  · exact rhsPlusTableRow4_calc j
  · exact rhsPlusTableRow5_calc j
  · exact rhsPlusTableRow6_calc j
  · exact rhsPlusTableRow7_calc j
  · exact rhsPlusTableRow8_calc j
  · exact rhsPlusTableRow9_calc j
  · exact rhsPlusTableRow10_calc j
  · exact rhsPlusTableRow11_calc j
  · exact rhsPlusTableRow12_calc j
  · exact rhsPlusTableRow13_calc j
  · exact rhsPlusTableRow14_calc j
  · exact rhsPlusTableRow15_calc j
  · exact rhsPlusTableRow16_calc j
  · exact rhsPlusTableRow17_calc j
  · exact rhsPlusTableRow18_calc j
  · exact rhsPlusTableRow19_calc j
lemma rhsPlusTable_mem (i : Fin 20) (j : Fin 8) : (rhsPlusTable i j).Mem ((Yf+Construction.R0*(gamma 1+gamma 0)) i j) := by
  rw [← rhsPlusTable_calc]
  exact rhsPlusBox_mem i j
lemma rhsMinusTable_mem (i : Fin 20) (j : Fin 8) : (rhsMinusTable i j).Mem ((Yf+Construction.R0*(gamma 1-gamma 0)) i j) := by
  rw [← rhsMinusTable_calc]
  exact rhsMinusBox_mem i j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamU
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma UplusCachedBox_mem (i : Fin 20) (j : Fin 8) : (UplusCachedBox i j).Mem (Uplus i j) := matrixMul_mem minusInverseBox_mem rhsPlusTable_mem i j
lemma UplusTable_mem (i : Fin 20) (j : Fin 8) : (UplusTable i j).Mem (Uplus i j) := by
  rw [← UplusTable_calc]
  exact UplusCachedBox_mem i j
lemma UminusCachedBox_mem (i : Fin 20) (j : Fin 8) : (UminusCachedBox i j).Mem (Uminus i j) := matrixMul_mem plusInverseBox_mem rhsMinusTable_mem i j
lemma UminusTable_mem (i : Fin 20) (j : Fin 8) : (UminusTable i j).Mem (Uminus i j) := by
  rw [← UminusTable_calc]
  exact UminusCachedBox_mem i j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamA
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma A1CachedBox_mem (i : Fin 23) (j : Fin 8) : (A1CachedBox i j).Mem (Acoefficient 0 i j) := by
  unfold A1CachedBox Acoefficient
  split_ifs
  · exact gammaBox_mem _ _ _
  · exact gammaBox_mem _ _ _
  · simpa only [finiteSolution, Fin.val_zero, Fin.val_one, ite_true, if_true, one_ne_zero, ite_false, if_false,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Nat.cast_ofNat, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul] using
      RI.mem_divNat (RI.mem_add (UplusTable_mem ⟨i.val-2,by omega⟩ j) (UminusTable_mem ⟨i.val-2,by omega⟩ j)) (by norm_num : 0<(2:ℕ))

lemma A1Table_mem (i : Fin 23) (j : Fin 8) : (A1Table i j).Mem ((Acoefficient 0) i j) := by
  rw [← A1Table_calc]
  exact A1CachedBox_mem i j
lemma A2CachedBox_mem (i : Fin 23) (j : Fin 8) : (A2CachedBox i j).Mem (Acoefficient 1 i j) := by
  unfold A2CachedBox Acoefficient
  split_ifs
  · exact gammaBox_mem _ _ _
  · exact gammaBox_mem _ _ _
  · simpa only [finiteSolution, Fin.val_zero, Fin.val_one, ite_true, if_true, one_ne_zero, ite_false, if_false,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Nat.cast_ofNat, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul] using
      RI.mem_divNat (RI.mem_sub (UplusTable_mem ⟨i.val-2,by omega⟩ j) (UminusTable_mem ⟨i.val-2,by omega⟩ j)) (by norm_num : 0<(2:ℕ))

lemma A2Table_mem (i : Fin 23) (j : Fin 8) : (A2Table i j).Mem ((Acoefficient 1) i j) := by
  rw [← A2Table_calc]
  exact A2CachedBox_mem i j
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
lemma boundV_mem (c : Fin 1) : (boundV c).Mem (tailConstantEnvelope) := by
  rw [← boundV_calc]
  exact RI.mem_sum (fun j => RI.mem_mul (envelopeSumBoxD_mem j) (fourierNorm_mem j))
lemma tailConstantEnvelope_bound : tailConstantEnvelope < (127/1000000000:ℝ) := by
  apply ri_mem_lt (boundV_mem 0) 127 1000000000 (by norm_num)
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
lemma tail_constant_column_bound :
    (∑' p : TailNode × Fin 2, |jet h h p.1.val.val p.2 fourierCoeff|) < 127/10^9 := by
  exact (tail_atom_column_bounds 0 0 _).2.trans_lt (by norm_num [tailConstantEnvelope,damping,H,h] at ⊢; simpa [tailConstantEnvelope] using FiniteCertificate.tailConstantEnvelope_bound)
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
lemma tailFixedColumn_norm_constant : ‖tailFixedColumn 22‖ ≤ 127/10^9 := by
  rw [l1_norm]
  simp only [tailFixedColumn_apply,Fin.isValue]
  have hh := tail_constant_column_bound
  convert hh.le using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma A1_norm_bound (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    (∑ i : Fin 23, |∑ j : Fin 8, Acoefficient 0 i j*e j|) < (258/100:ℝ) := by
  have hh : ∀ i : Fin 23, |∑ j : Fin 8, Acoefficient 0 i j*e j| ≤ (A1AbsNumerators i:ℝ)/scale := by
    intro i
    rw [← A1AbsNumerators_calc]
    exact rowAbs_bound (A1Table_mem i) e he
  have hc : (100:ℤ)*(∑ i : Fin 23, A1AbsNumerators i) < 258*scale := by decide +kernel
  calc
    _ ≤ ∑ i : Fin 23, (A1AbsNumerators i:ℝ)/scale := Finset.sum_le_sum (fun i _ => hh i)
    _ = ((∑ i : Fin 23, A1AbsNumerators i:ℤ):ℝ)/scale := by rw [← Finset.sum_div,Int.cast_sum]
    _ < (258/100:ℝ) := by
      apply (div_lt_iff₀ scale_pos).mpr
      have hx : (100:ℝ)*((∑ i : Fin 23, A1AbsNumerators i:ℤ):ℝ) < 258*(scale:ℝ) := by exact_mod_cast hc
      linarith
lemma A2_norm_bound (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    (∑ i : Fin 23, |∑ j : Fin 8, Acoefficient 1 i j*e j|) < (280/100:ℝ) := by
  have hh : ∀ i : Fin 23, |∑ j : Fin 8, Acoefficient 1 i j*e j| ≤ (A2AbsNumerators i:ℝ)/scale := by
    intro i
    rw [← A2AbsNumerators_calc]
    exact rowAbs_bound (A2Table_mem i) e he
  have hc : (100:ℤ)*(∑ i : Fin 23, A2AbsNumerators i) < 280*scale := by decide +kernel
  calc
    _ ≤ ∑ i : Fin 23, (A2AbsNumerators i:ℝ)/scale := Finset.sum_le_sum (fun i _ => hh i)
    _ = ((∑ i : Fin 23, A2AbsNumerators i:ℤ):ℝ)/scale := by rw [← Finset.sum_div,Int.cast_sum]
    _ < (280/100:ℝ) := by
      apply (div_lt_iff₀ scale_pos).mpr
      have hx : (100:ℝ)*((∑ i : Fin 23, A2AbsNumerators i:ℤ):ℝ) < 280*(scale:ℝ) := by exact_mod_cast hc
      linarith
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

lemma splitL_norm (e : Fin 2) : ‖splitL e‖ ≤ splitN e := by
  fin_cases e
  · exact Lplus_norm
  · exact Lminus_norm
lemma splitK_norm (e : Fin 2) : ‖splitK e‖ ≤ beta := by
  have ha := AC_bound
  fin_cases e
  · exact (norm_sub_le _ _).trans (by linarith)
  · exact (norm_sub_le _ _).trans (by simpa only [norm_neg] using (show ‖Coperator‖+‖Aoperator‖≤beta by linarith))
lemma splitD_norm (e : Fin 2) : ‖splitD e‖ ≤ delta := by
  have hh := Doperator_norm
  fin_cases e <;> simp only [splitD,↓reduceIte,Nat.one_ne_zero,norm_neg] <;>
    norm_num [delta] at * <;> linarith
lemma splitOperator_norm (e : Fin 2) :
    ‖tailOperator (splitL e) (splitB e) (splitK e) (splitD e)‖ ≤ splitQ e := by
  have hb : 0≤beta := by norm_num [beta]
  have hN := splitN_nonneg e
  calc
    _ ≤ ‖splitD e‖+‖(splitK e).comp ((splitL e).comp (splitB e))‖ := norm_add_le _ _
    _ ≤ delta+‖splitK e‖*(‖splitL e‖*‖splitB e‖) :=
      add_le_add (splitD_norm e) ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)))
    _ ≤ delta+beta*(splitN e*340) := by
      gcongr
      · exact splitK_norm e
      · exact splitL_norm e
      · exact splitB_norm e
    _ = splitQ e := by unfold splitQ; ring

lemma correctionTail_norm (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) :
    ‖correctionTail e r s‖ ≤ (‖s‖+beta*splitN e*‖r‖)/(1-splitQ e) := by
  have hn := neumann_norm (tailOperator (splitL e) (splitB e) (splitK e) (splitD e))
    (splitQ_nonneg e) (splitQ_lt e) (splitOperator_norm e)
  have hq : 0≤1/(1-splitQ e) := by exact div_nonneg (by norm_num) (sub_pos.mpr (splitQ_lt e)).le
  have hbeta : 0≤beta := by norm_num [beta]
  have hN := splitN_nonneg e
  calc
    _ ≤ ‖neumann (tailOperator (splitL e) (splitB e) (splitK e) (splitD e))‖*
        ‖s+splitK e (splitL e r)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (1/(1-splitQ e))*(‖s‖+‖splitK e‖*(‖splitL e‖*‖r‖)) := by
      apply mul_le_mul hn _ (norm_nonneg _) hq
      exact (norm_add_le _ _).trans (add_le_add_right ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))) _)
    _ ≤ (1/(1-splitQ e))*(‖s‖+beta*(splitN e*‖r‖)) := by
      gcongr
      · exact splitK_norm e
      · exact splitL_norm e
    _ = _ := by ring
lemma correctionFinite_norm (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) :
    ‖correctionFinite e r s‖ ≤ splitN e*(‖r‖+340*‖correctionTail e r s‖) := by
  have hN := splitN_nonneg e
  calc
    _ ≤ ‖splitL e‖*‖r+splitB e (correctionTail e r s)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ splitN e*(‖r‖+‖splitB e‖*‖correctionTail e r s‖) :=
      mul_le_mul (splitL_norm e) ((norm_add_le _ _).trans
        (add_le_add_right (ContinuousLinearMap.le_opNorm _ _) _)) (norm_nonneg _) (splitN_nonneg e)
    _ ≤ _ := by gcongr; exact splitB_norm e

lemma correctionTail_small (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients)
    (hr : ‖r‖≤finiteResidualBound) (hs : ‖s‖≤tailResidualBound e) :
    ‖correctionTail e r s‖ ≤ tailErrorBound e := by
  have hh := correctionTail_norm e r s
  have hb : (‖s‖+beta*splitN e*‖r‖)/(1-splitQ e) ≤
      (tailResidualBound e+beta*splitN e*finiteResidualBound)/(1-splitQ e) := by
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr (splitQ_lt e)).le
    apply add_le_add hs
    exact mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num [beta]) (splitN_nonneg e))
  refine (hh.trans hb).trans ?_
  fin_cases e <;> (first | (simp [tailResidualBound,tailErrorBound,finiteResidualBound,splitQ,splitN,beta,delta]; all_goals first | (norm_num [tailResidualBound,tailErrorBound,finiteResidualBound,splitQ,splitN,beta,delta]; done) | rfl | decide) | (norm_num [tailResidualBound,tailErrorBound,finiteResidualBound,splitQ,splitN,beta,delta]; done) | norm_num [tailResidualBound,tailErrorBound,finiteResidualBound,splitQ,splitN,beta,delta])
lemma correctionFinite_small (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients)
    (hr : ‖r‖≤finiteResidualBound) (hs : ‖s‖≤tailResidualBound e) :
    ‖correctionFinite e r s‖ ≤ finiteErrorBound e := by
  have hN := splitN_nonneg e
  have hh := correctionFinite_norm e r s
  have hb := correctionTail_small e r s hr hs
  calc
    _ ≤ splitN e*(‖r‖+340*‖correctionTail e r s‖) := hh
    _ ≤ splitN e*(finiteResidualBound+340*tailErrorBound e) := by gcongr
    _ ≤ _ := by fin_cases e <;> (first | (simp [splitN,finiteResidualBound,tailErrorBound,finiteErrorBound]; all_goals first | (norm_num [splitN,finiteResidualBound,tailErrorBound,finiteErrorBound]; done) | rfl | decide) | (norm_num [splitN,finiteResidualBound,tailErrorBound,finiteErrorBound]; done) | norm_num [splitN,finiteResidualBound,tailErrorBound,finiteErrorBound])
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

lemma finiteApprox_norm (side : Fin 2) (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    ‖finiteApprox side e‖ < 3 := by
  rw [l1_norm,tsum_fintype]
  have hb : (∑ i : Fin 22, |∑ j : Fin 8, Acoefficient side i.castSucc j*e j|) ≤
      ∑ i : Fin 23, |∑ j : Fin 8, Acoefficient side i j*e j| := by
    conv_rhs => rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (abs_nonneg _)
  change (∑ i : Fin 22, |∑ j : Fin 8, Acoefficient side i.castSucc j*e j|) < 3
  refine hb.trans_lt ?_
  fin_cases side
  · exact (A1_norm_bound e he).trans (by norm_num)
  · exact (A2_norm_bound e he).trans (by norm_num)

lemma approximationTailResidual_norm (e : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖approximationTailResidual e z hz hzB‖ ≤ tailResidualBound e := by
  have h1 := (finiteApprox_norm 0 (actualParameter z) (actualParameter_mem hz hzB)).le
  have h2 := (finiteApprox_norm 1 (actualParameter z) (actualParameter_mem hz hzB)).le
  have ht : ‖tailTarget z hz hzB‖ ≤ (1/10^26:ℝ) :=
    (tailTarget_norm hz hzB).trans (tailTargetEnvelope_bound.le.trans (by norm_num))
  have hp : ‖finiteApprox 0 (actualParameter z)+finiteApprox 1 (actualParameter z)‖ ≤ 6 :=
    (norm_add_le _ _).trans (by linarith)
  have hm : ‖finiteApprox 0 (actualParameter z)-finiteApprox 1 (actualParameter z)‖ ≤ 6 :=
    (norm_sub_le _ _).trans (by linarith)
  have hm' : ‖finiteApprox 1 (actualParameter z)-finiteApprox 0 (actualParameter z)‖ ≤ 6 :=
    (norm_sub_le _ _).trans (by linarith)
  have hc (a b : TrigonometricCoefficients) (ha : ‖a‖≤6) (hb : ‖b‖≤6) :
      ‖CallOperator a-AallOperator b‖ ≤ 6*beta := by
    calc
      _ ≤ ‖CallOperator a‖+‖AallOperator b‖ := norm_sub_le _ _
      _ ≤ ‖CallOperator‖*‖a‖+‖AallOperator‖*‖b‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ ‖CallOperator‖*6+‖AallOperator‖*6 := by gcongr
      _ ≤ 6*beta := by nlinarith [AC_all_bound]
  have hv : ‖(12/1000:ℝ) • tailFixedColumn 22‖ ≤ (12/1000:ℝ)*(13/10^8) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<12/1000)]
    exact mul_le_mul_of_nonneg_left (tailFixedColumn_norm_constant.trans (by norm_num)) (by norm_num)
  fin_cases e <;> simp only [approximationTailResidual,tailResidualBound,↓reduceIte,Nat.one_ne_zero]
  · change ‖tailTarget z hz hzB + _‖ ≤ 1/10^26+6*beta+0
    exact (norm_add_le _ _).trans (by linarith [hc _ _ hp hp])
  · change ‖tailTarget z hz hzB + (_+_)‖ ≤ 1/10^26+6*beta+(12/1000)*(13/10^8)
    have hh := (norm_add_le _ _).trans (add_le_add ht
      ((norm_add_le _ _).trans (add_le_add (hc _ _ hm' hm) hv)))
    simpa only [add_assoc] using hh

lemma actualTailSplit_norm (e : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖actualTailSplit e z hz hzB‖ ≤ tailErrorBound e :=
  correctionTail_small _ _ _ (finiteResidual_norm hz hzB) (approximationTailResidual_norm e hz hzB)
lemma actualFiniteSplit_norm (e : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖actualFiniteSplit e z hz hzB‖ ≤ finiteErrorBound e :=
  correctionFinite_small _ _ _ (finiteResidual_norm hz hzB) (approximationTailResidual_norm e hz hzB)

lemma actualTail_norm (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖actualTail side z hz hzB‖ < (3/10^9:ℝ) := by
  have hp := actualTailSplit_norm 0 hz hzB
  have hm := actualTailSplit_norm 1 hz hzB
  unfold actualTail
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hh := norm_add_le (actualTailSplit 0 z hz hzB)
    (if side.val=0 then actualTailSplit 1 z hz hzB else -actualTailSplit 1 z hz hzB)
  split_ifs at hh ⊢ <;> (try simp only [norm_neg] at hh) <;> norm_num [tailErrorBound] at hp hm <;> linarith
lemma actualFiniteError_norm (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖actualFiniteError side z hz hzB‖ < (1/10^5:ℝ) := by
  have hp := actualFiniteSplit_norm 0 hz hzB
  have hm := actualFiniteSplit_norm 1 hz hzB
  unfold actualFiniteError
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hh := norm_add_le (actualFiniteSplit 0 z hz hzB)
    (if side.val=0 then actualFiniteSplit 1 z hz hzB else -actualFiniteSplit 1 z hz hzB)
  split_ifs at hh ⊢ <;> (try simp only [norm_neg] at hh) <;> norm_num [finiteErrorBound] at hp hm <;> linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_ActualInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds

def actualTrigonometric (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : TrigonometricCoefficients :=
  finiteApprox side (actualParameter z)+extendFiniteError (actualFiniteError side z hz hzB)
def actualInput (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : InputCoefficients :=
  coefficientInput (if side.val=0 then -(3/500) else 3/500)
    (actualTrigonometric side z hz hzB) (actualTail side z hz hzB)
lemma actualTrigonometric_norm (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖actualTrigonometric side z hz hzB‖ < (300001/100000:ℝ) := by
  have h1 := finiteApprox_norm side (actualParameter z) (actualParameter_mem hz hzB)
  have h2 := actualFiniteError_norm side hz hzB
  have hh := norm_add_le (finiteApprox side (actualParameter z)) (extendFiniteError (actualFiniteError side z hz hzB))
  rw [extendFiniteError_norm] at hh
  change ‖finiteApprox side (actualParameter z)+_‖ < _
  linarith

lemma actualFiniteError_equations {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualFiniteError 0 z hz hzB = Roperator (actualFiniteError 1 z hz hzB)+Boperator (actualTail 1 z hz hzB)+finiteResidual z ∧
    actualFiniteError 1 z hz hzB = Roperator (actualFiniteError 0 z hz hzB)+Boperator (actualTail 0 z hz hzB) := by
  have hp := correctionFinite_plus (finiteResidual z) (approximationTailResidual 0 z hz hzB)
  have hm := correctionFinite_minus (finiteResidual z) (approximationTailResidual 1 z hz hzB)
  change actualFiniteSplit 0 z hz hzB=Roperator (actualFiniteSplit 0 z hz hzB)+Boperator (actualTailSplit 0 z hz hzB)+finiteResidual z at hp
  change actualFiniteSplit 1 z hz hzB= -Roperator (actualFiniteSplit 1 z hz hzB)-Boperator (actualTailSplit 1 z hz hzB)+finiteResidual z at hm
  constructor <;> ext i
  all_goals
    have hp' := congrArg (fun u : FiniteCoefficients => u i) hp
    have hm' := congrArg (fun u : FiniteCoefficients => u i) hm
    simp only [actualFiniteError,actualTail,Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte,
      map_smul,map_add,map_neg,lp.coeFn_add,lp.coeFn_sub,lp.coeFn_neg,lp.coeFn_smul,
      Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul] at hp' hm' ⊢
    linarith
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
lemma taylorPhaseTable_mem (q br : Fin 2) (j : Fin 31) :
    (taylorPhaseTable q br j).Mem (taylorPhase q br (frequency j)) := by
  fin_cases q <;> fin_cases br
  · exact taylorPhase0_0_mem j
  · exact taylorPhase0_1_mem j
  · exact taylorPhase1_0_mem j
  · exact taylorPhase1_1_mem j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_CurvatureBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureBox_mem (q br : Fin 2) (i : Fin 5) (j : Fin 31)
    (hp : (curvatureExpInput q br i j).normSq.hi ≤ scale*1024^2) :
    (curvatureBox q br i j).Mem (curvatureWave q br (curvaturePoint i) (frequency j)) := by
  have hs := CI.mem_normSq (taylorPhaseTable_mem q br j)
  rw [Complex.normSq_eq_norm_sq] at hs
  exact RI.mem_mul (RI.mem_mul hs (amplitudeNormBox_mem q br j))
    (ri_exp_mem (RI.mem_mul (taylorPhaseTable_mem q br j).1 (curvaturePointBox_mem i)) hp)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma actualInput_row_transformed (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (i : Fin 20) :
    (negativeJet H (rowNode i).val (rowDerivative i)
      (inputJJet (actualInput side z hz hzB) 1 0 (rowNode i).val)
      (inputJJet (actualInput side z hz hzB) 1 1 (rowNode i).val)).re=
      Boperator (actualTail side z hz hzB) i+Roperator (actualFiniteError side z hz hzB) i+
      (R *ᵥ (finiteSolution side *ᵥ actualParameter z)+R0 *ᵥ (gamma side *ᵥ actualParameter z)) i := by
  rw [actualInput,inputJJet_row_transformed]
  simp only [actualTrigonometric,lp.coeFn_add,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  rw [extendFiniteError_transformed]
  have hh := finiteApprox_transformed side (actualParameter z) i
  have hc : (gamma side *ᵥ actualParameter z) 2=if side.val=0 then -(3/500) else 3/500 := by
    rw [gamma_actual]
    rfl
  rw [hc] at hh
  simp only [Pi.add_apply] at hh
  linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_ActualInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
def actualJ (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : ℝ → ℝ :=
  pairJ (actualInput side z hz hzB) (actualInput (otherSide side) z hz hzB)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CurvatureData00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData00_0_mem (j : Fin 31) : (curvatureData00_0 j).Mem (curvatureWave 0 0 (curvaturePoint 0) (frequency j)) := by
  rw [← curvatureData00_0_calc]
  exact curvatureBox_mem 0 0 0 j (curvatureData00_0_pre j)
lemma curvatureData00_1_mem (j : Fin 31) : (curvatureData00_1 j).Mem (curvatureWave 0 0 (curvaturePoint 1) (frequency j)) := by
  rw [← curvatureData00_1_calc]
  exact curvatureBox_mem 0 0 1 j (curvatureData00_1_pre j)
lemma curvatureData00_2_mem (j : Fin 31) : (curvatureData00_2 j).Mem (curvatureWave 0 0 (curvaturePoint 2) (frequency j)) := by
  rw [← curvatureData00_2_calc]
  exact curvatureBox_mem 0 0 2 j (curvatureData00_2_pre j)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CurvatureData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData10_0_mem (j : Fin 31) : (curvatureData10_0 j).Mem (curvatureWave 1 0 (curvaturePoint 0) (frequency j)) := by
  rw [← curvatureData10_0_calc]
  exact curvatureBox_mem 1 0 0 j (curvatureData10_0_pre j)
lemma curvatureData10_1_mem (j : Fin 31) : (curvatureData10_1 j).Mem (curvatureWave 1 0 (curvaturePoint 1) (frequency j)) := by
  rw [← curvatureData10_1_calc]
  exact curvatureBox_mem 1 0 1 j (curvatureData10_1_pre j)
lemma curvatureData10_2_mem (j : Fin 31) : (curvatureData10_2 j).Mem (curvatureWave 1 0 (curvaturePoint 2) (frequency j)) := by
  rw [← curvatureData10_2_calc]
  exact curvatureBox_mem 1 0 2 j (curvatureData10_2_pre j)
lemma curvatureData10_3_mem (j : Fin 31) : (curvatureData10_3 j).Mem (curvatureWave 1 0 (curvaturePoint 3) (frequency j)) := by
  rw [← curvatureData10_3_calc]
  exact curvatureBox_mem 1 0 3 j (curvatureData10_3_pre j)
lemma curvatureData10_4_mem (j : Fin 31) : (curvatureData10_4 j).Mem (curvatureWave 1 0 (curvaturePoint 4) (frequency j)) := by
  rw [← curvatureData10_4_calc]
  exact curvatureBox_mem 1 0 4 j (curvatureData10_4_pre j)
lemma curvatureTable10_mem (i : Fin 5) (j : Fin 31) : (curvatureTable10 i j).Mem (curvatureWave 1 0 (curvaturePoint i) (frequency j)) := by
  fin_cases i
  · exact curvatureData10_0_mem j
  · exact curvatureData10_1_mem j
  · exact curvatureData10_2_mem j
  · exact curvatureData10_3_mem j
  · exact curvatureData10_4_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CurvatureData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData11_0_mem (j : Fin 31) : (curvatureData11_0 j).Mem (curvatureWave 1 1 (curvaturePoint 0) (frequency j)) := by
  rw [← curvatureData11_0_calc]
  exact curvatureBox_mem 1 1 0 j (curvatureData11_0_pre j)
lemma curvatureData11_1_mem (j : Fin 31) : (curvatureData11_1 j).Mem (curvatureWave 1 1 (curvaturePoint 1) (frequency j)) := by
  rw [← curvatureData11_1_calc]
  exact curvatureBox_mem 1 1 1 j (curvatureData11_1_pre j)
lemma curvatureData11_2_mem (j : Fin 31) : (curvatureData11_2 j).Mem (curvatureWave 1 1 (curvaturePoint 2) (frequency j)) := by
  rw [← curvatureData11_2_calc]
  exact curvatureBox_mem 1 1 2 j (curvatureData11_2_pre j)
lemma curvatureData11_3_mem (j : Fin 31) : (curvatureData11_3 j).Mem (curvatureWave 1 1 (curvaturePoint 3) (frequency j)) := by
  rw [← curvatureData11_3_calc]
  exact curvatureBox_mem 1 1 3 j (curvatureData11_3_pre j)
lemma curvatureData11_4_mem (j : Fin 31) : (curvatureData11_4 j).Mem (curvatureWave 1 1 (curvaturePoint 4) (frequency j)) := by
  rw [← curvatureData11_4_calc]
  exact curvatureBox_mem 1 1 4 j (curvatureData11_4_pre j)
lemma curvatureTable11_mem (i : Fin 5) (j : Fin 31) : (curvatureTable11 i j).Mem (curvatureWave 1 1 (curvaturePoint i) (frequency j)) := by
  fin_cases i
  · exact curvatureData11_0_mem j
  · exact curvatureData11_1_mem j
  · exact curvatureData11_2_mem j
  · exact curvatureData11_3_mem j
  · exact curvatureData11_4_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_CurvatureSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureColumn0_0_bound (c : Fin 22) : rawCurvatureColumn 0 (curvaturePoint 0) c < (828/10:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable10_mem 0 j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [curvatureColumn0_0_calc] at hh
  have hb := ri_mem_lt hh 828 10 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawCurvatureColumn, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
lemma curvatureColumn0_1_bound (c : Fin 22) : rawCurvatureColumn 0 (curvaturePoint 1) c < (44164/1000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable10_mem 1 j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [curvatureColumn0_1_calc] at hh
  have hb := ri_mem_lt hh 44164 1000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawCurvatureColumn, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
lemma curvatureColumn0_2_bound (c : Fin 22) : rawCurvatureColumn 0 (curvaturePoint 2) c < (23561/1000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable10_mem 2 j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [curvatureColumn0_2_calc] at hh
  have hb := ri_mem_lt hh 23561 1000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawCurvatureColumn, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
lemma curvatureColumn0_3_bound (c : Fin 22) : rawCurvatureColumn 0 (curvaturePoint 3) c < (9147/1000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable10_mem 3 j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [curvatureColumn0_3_calc] at hh
  have hb := ri_mem_lt hh 9147 1000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawCurvatureColumn, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
lemma curvatureColumn0_4_bound (c : Fin 22) : rawCurvatureColumn 0 (curvaturePoint 4) c < (43834/1000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable10_mem 4 j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [curvatureColumn0_4_calc] at hh
  have hb := ri_mem_lt hh 43834 1000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawCurvatureColumn, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
lemma curvatureColumn1_0_bound (c : Fin 22) : rawCurvatureColumn 1 (curvaturePoint 0) c < (291294/100:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable11_mem 0 j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [curvatureColumn1_0_calc] at hh
  have hb := ri_mem_lt hh 291294 100 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawCurvatureColumn, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
lemma curvatureColumn1_1_bound (c : Fin 22) : rawCurvatureColumn 1 (curvaturePoint 1) c < (45877/1000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable11_mem 1 j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [curvatureColumn1_1_calc] at hh
  have hb := ri_mem_lt hh 45877 1000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawCurvatureColumn, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
lemma curvatureColumn1_2_bound (c : Fin 22) : rawCurvatureColumn 1 (curvaturePoint 2) c < (3893/1000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable11_mem 2 j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [curvatureColumn1_2_calc] at hh
  have hb := ri_mem_lt hh 3893 1000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawCurvatureColumn, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
lemma curvatureColumn1_3_bound (c : Fin 22) : rawCurvatureColumn 1 (curvaturePoint 3) c < (635/10000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable11_mem 3 j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [curvatureColumn1_3_calc] at hh
  have hb := ri_mem_lt hh 635 10000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawCurvatureColumn, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
lemma curvatureColumn1_4_bound (c : Fin 22) : rawCurvatureColumn 1 (curvaturePoint 4) c < (167/100000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable11_mem 4 j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [curvatureColumn1_4_calc] at hh
  have hb := ri_mem_lt hh 167 100000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawCurvatureColumn, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
end AtomicTriangular.FiniteCertificate
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

lemma finiteCurvatureCap_bound (br : Fin 2) (i : Fin 5) (c : Fin 22) :
    rawCurvatureColumn br (curvaturePoint i) c≤finiteCurvatureCap br i := by
  fin_cases br <;> fin_cases i
  all_goals first
    | exact (curvatureColumn0_0_bound c).le | exact (curvatureColumn0_1_bound c).le
    | exact (curvatureColumn0_2_bound c).le | exact (curvatureColumn0_3_bound c).le
    | exact (curvatureColumn0_4_bound c).le | exact (curvatureColumn1_0_bound c).le
    | exact (curvatureColumn1_1_bound c).le | exact (curvatureColumn1_2_bound c).le
    | exact (curvatureColumn1_3_bound c).le | exact (curvatureColumn1_4_bound c).le
lemma finiteSpectral_curvature (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (i : Fin 5) {s : ℝ} (hs : curvaturePoint i≤ s) :
    ‖finiteSpectral (coefficientInput C a w) (waveFunctionJet 1 br 2 s)‖≤‖a‖*finiteCurvatureCap br i := by
  apply finiteSpectral_wave_bound
  intro c
  exact (rawCurvatureColumn_antitone br c hs).trans (finiteCurvatureCap_bound br i c)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FarCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def actualJ0 (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z ≤ Z) : ℝ → ℝ :=
  pairJ (coefficientInput 0 (actualTrigonometric side z hz hzB) (actualTail side z hz hzB))
    (coefficientInput 0 (actualTrigonometric (otherSide side) z hz hzB) (actualTail (otherSide side) z hz hzB))+
      sideConstant (otherSide side) • transformedP
lemma actualJ0_contDiff (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    ContDiff ℝ ⊤ (actualJ0 side z hz hzB) :=
  by
    change ContDiff ℝ ⊤ (fun s => _+sideConstant (otherSide side)*transformedP s)
    exact (pairJ_contDiff _ _).add (by simpa only [smul_eq_mul] using transformedP_contDiff.const_smul (sideConstant (otherSide side)))
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderNorm
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


