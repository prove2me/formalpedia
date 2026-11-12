-- Prove2me | Definitions.Def_OAIQ262T142
-- name    : OAIQ262T142
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:34:58.969212+00:00
-- url     : https://prove2.me/theorems/81627768-322a-435a-8148-0197bb03e1f3
-- title:
--   Definitions bundle OAIQ262T142 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 62 declarations of OpenAI's Lean: 2 definitions and 60 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.tailTarget`, `OAI.AtomicTriangular.FiniteCertificate.ATable`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_ParamA`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamA.lean), [`Triangular_Certificate_ParamActual`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamActual.lean), [`Triangular_Certificate_ParamInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamInterval.lean), [`Triangular_Certificate_ParamNorm`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamNorm.lean), [`Triangular_Certificate_ParamU`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamU.lean), [`Triangular_Certificate_TargetInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/TargetInterval.lean), [`Triangular_Construction_L1Matrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/L1Matrix.lean), [`Triangular_Envelope_TargetEnvelope`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/TargetEnvelope.lean), [`Triangular_Taylor_TaylorSpectrum`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T086`, `OAIQ262T088`, `OAIQ262T089`, `OAIQ262T091`, `OAIQ262T092`, `OAIQ262T093`, `OAIQ262T094` and `OAIQ262T095` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T152`, `OAIQ262T155`, `OAIQ262T157` and `OAIQ262T158`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T086
import Definitions.Def_OAIQ262T088
import Definitions.Def_OAIQ262T089
import Definitions.Def_OAIQ262T091
import Definitions.Def_OAIQ262T092
import Definitions.Def_OAIQ262T093
import Definitions.Def_OAIQ262T094
import Definitions.Def_OAIQ262T095

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
lemma plusResidualRow1_calc (j : Fin 20) : plusResidualBox 1 j = plusResidualRow1 j := by
  revert j
  decide +kernel
lemma plusResidualRow2_calc (j : Fin 20) : plusResidualBox 2 j = plusResidualRow2 j := by
  revert j
  decide +kernel
lemma plusResidualRow3_calc (j : Fin 20) : plusResidualBox 3 j = plusResidualRow3 j := by
  revert j
  decide +kernel
lemma plusResidualRow4_calc (j : Fin 20) : plusResidualBox 4 j = plusResidualRow4 j := by
  revert j
  decide +kernel
lemma plusResidualRow5_calc (j : Fin 20) : plusResidualBox 5 j = plusResidualRow5 j := by
  revert j
  decide +kernel
lemma plusResidualRow6_calc (j : Fin 20) : plusResidualBox 6 j = plusResidualRow6 j := by
  revert j
  decide +kernel
lemma plusResidualRow7_calc (j : Fin 20) : plusResidualBox 7 j = plusResidualRow7 j := by
  revert j
  decide +kernel
lemma plusResidualRow8_calc (j : Fin 20) : plusResidualBox 8 j = plusResidualRow8 j := by
  revert j
  decide +kernel
lemma plusResidualRow9_calc (j : Fin 20) : plusResidualBox 9 j = plusResidualRow9 j := by
  revert j
  decide +kernel
lemma plusResidualRow12_calc (j : Fin 20) : plusResidualBox 12 j = plusResidualRow12 j := by
  revert j
  decide +kernel
lemma plusResidualRow13_calc (j : Fin 20) : plusResidualBox 13 j = plusResidualRow13 j := by
  revert j
  decide +kernel
lemma plusResidualRow14_calc (j : Fin 20) : plusResidualBox 14 j = plusResidualRow14 j := by
  revert j
  decide +kernel
lemma plusResidualRow15_calc (j : Fin 20) : plusResidualBox 15 j = plusResidualRow15 j := by
  revert j
  decide +kernel
lemma plusResidualRow16_calc (j : Fin 20) : plusResidualBox 16 j = plusResidualRow16 j := by
  revert j
  decide +kernel
lemma plusResidualRow17_calc (j : Fin 20) : plusResidualBox 17 j = plusResidualRow17 j := by
  revert j
  decide +kernel
lemma plusResidualRow18_calc (j : Fin 20) : plusResidualBox 18 j = plusResidualRow18 j := by
  revert j
  decide +kernel
lemma plusResidualRow19_calc (j : Fin 20) : plusResidualBox 19 j = plusResidualRow19 j := by
  revert j
  decide +kernel

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
lemma targetExp1_mem : targetExp1.Mem (Complex.exp ((Real.pi*eta*(1:ℤ):ℝ):ℂ)) := by
  rw [← targetExp1_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 1))
  · decide +kernel
lemma targetExp3_mem : targetExp3.Mem (Complex.exp ((Real.pi*eta*(3:ℤ):ℝ):ℂ)) := by
  rw [← targetExp3_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 3))
  · decide +kernel
lemma targetExp4_mem : targetExp4.Mem (Complex.exp ((Real.pi*eta*(4:ℤ):ℝ):ℂ)) := by
  rw [← targetExp4_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 4))
  · decide +kernel
lemma targetExp7_mem : targetExp7.Mem (Complex.exp ((Real.pi*eta*(7:ℤ):ℝ):ℂ)) := by
  rw [← targetExp7_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 7))
  · decide +kernel
lemma targetExp9_mem : targetExp9.Mem (Complex.exp ((Real.pi*eta*(9:ℤ):ℝ):ℂ)) := by
  rw [← targetExp9_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 9))
  · decide +kernel
lemma targetExp12_mem : targetExp12.Mem (Complex.exp ((Real.pi*eta*(12:ℤ):ℝ):ℂ)) := by
  rw [← targetExp12_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 12))
  · decide +kernel
lemma targetExp13_mem : targetExp13.Mem (Complex.exp ((Real.pi*eta*(13:ℤ):ℝ):ℂ)) := by
  rw [← targetExp13_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 13))
  · decide +kernel
lemma targetExp16_mem : targetExp16.Mem (Complex.exp ((Real.pi*eta*(16:ℤ):ℝ):ℂ)) := by
  rw [← targetExp16_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 16))
  · decide +kernel
lemma targetExp19_mem : targetExp19.Mem (Complex.exp ((Real.pi*eta*(19:ℤ):ℝ):ℂ)) := by
  rw [← targetExp19_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 19))
  · decide +kernel
lemma targetExp21_mem : targetExp21.Mem (Complex.exp ((Real.pi*eta*(21:ℤ):ℝ):ℂ)) := by
  rw [← targetExp21_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 21))
  · decide +kernel
lemma targetExpTable_mem (n : Fin 10) : (targetExpTable n).Mem (Complex.exp ((Real.pi*eta*(finiteNode n):ℝ):ℂ)) := by
  fin_cases n
  · exact targetExp1_mem
  · exact targetExp3_mem
  · exact targetExp4_mem
  · exact targetExp7_mem
  · exact targetExp9_mem
  · exact targetExp12_mem
  · exact targetExp13_mem
  · exact targetExp16_mem
  · exact targetExp19_mem
  · exact targetExp21_mem

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
lemma UminusTableRow0_calc (j : Fin 8) : UminusCachedBox 0 j = UminusTableRow0 j := by
  revert j
  decide +kernel
lemma UminusTableRow1_calc (j : Fin 8) : UminusCachedBox 1 j = UminusTableRow1 j := by
  revert j
  decide +kernel
lemma UminusTableRow2_calc (j : Fin 8) : UminusCachedBox 2 j = UminusTableRow2 j := by
  revert j
  decide +kernel
lemma UminusTableRow3_calc (j : Fin 8) : UminusCachedBox 3 j = UminusTableRow3 j := by
  revert j
  decide +kernel
lemma UminusTableRow4_calc (j : Fin 8) : UminusCachedBox 4 j = UminusTableRow4 j := by
  revert j
  decide +kernel
lemma UminusTableRow10_calc (j : Fin 8) : UminusCachedBox 10 j = UminusTableRow10 j := by
  revert j
  decide +kernel
lemma UminusTableRow11_calc (j : Fin 8) : UminusCachedBox 11 j = UminusTableRow11 j := by
  revert j
  decide +kernel
lemma UminusTableRow12_calc (j : Fin 8) : UminusCachedBox 12 j = UminusTableRow12 j := by
  revert j
  decide +kernel
lemma UminusTableRow13_calc (j : Fin 8) : UminusCachedBox 13 j = UminusTableRow13 j := by
  revert j
  decide +kernel
lemma UminusTableRow14_calc (j : Fin 8) : UminusCachedBox 14 j = UminusTableRow14 j := by
  revert j
  decide +kernel
lemma UminusTableRow15_calc (j : Fin 8) : UminusCachedBox 15 j = UminusTableRow15 j := by
  revert j
  decide +kernel
lemma UminusTableRow16_calc (j : Fin 8) : UminusCachedBox 16 j = UminusTableRow16 j := by
  revert j
  decide +kernel
lemma UminusTableRow17_calc (j : Fin 8) : UminusCachedBox 17 j = UminusTableRow17 j := by
  revert j
  decide +kernel
lemma UminusTableRow18_calc (j : Fin 8) : UminusCachedBox 18 j = UminusTableRow18 j := by
  revert j
  decide +kernel
lemma UminusTableRow19_calc (j : Fin 8) : UminusCachedBox 19 j = UminusTableRow19 j := by
  revert j
  decide +kernel
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
lemma A1Table_calc (i : Fin 23) (j : Fin 8) : A1CachedBox i j = A1Table i j := by
  fin_cases i
  · exact A1TableRow0_calc j
  · exact A1TableRow1_calc j
  · exact A1TableRow2_calc j
  · exact A1TableRow3_calc j
  · exact A1TableRow4_calc j
  · exact A1TableRow5_calc j
  · exact A1TableRow6_calc j
  · exact A1TableRow7_calc j
  · exact A1TableRow8_calc j
  · exact A1TableRow9_calc j
  · exact A1TableRow10_calc j
  · exact A1TableRow11_calc j
  · exact A1TableRow12_calc j
  · exact A1TableRow13_calc j
  · exact A1TableRow14_calc j
  · exact A1TableRow15_calc j
  · exact A1TableRow16_calc j
  · exact A1TableRow17_calc j
  · exact A1TableRow18_calc j
  · exact A1TableRow19_calc j
  · exact A1TableRow20_calc j
  · exact A1TableRow21_calc j
  · exact A1TableRow22_calc j
lemma A2Table_calc (i : Fin 23) (j : Fin 8) : A2CachedBox i j = A2Table i j := by
  fin_cases i
  · exact A2TableRow0_calc j
  · exact A2TableRow1_calc j
  · exact A2TableRow2_calc j
  · exact A2TableRow3_calc j
  · exact A2TableRow4_calc j
  · exact A2TableRow5_calc j
  · exact A2TableRow6_calc j
  · exact A2TableRow7_calc j
  · exact A2TableRow8_calc j
  · exact A2TableRow9_calc j
  · exact A2TableRow10_calc j
  · exact A2TableRow11_calc j
  · exact A2TableRow12_calc j
  · exact A2TableRow13_calc j
  · exact A2TableRow14_calc j
  · exact A2TableRow15_calc j
  · exact A2TableRow16_calc j
  · exact A2TableRow17_calc j
  · exact A2TableRow18_calc j
  · exact A2TableRow19_calc j
  · exact A2TableRow20_calc j
  · exact A2TableRow21_calc j
  · exact A2TableRow22_calc j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_L1Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.MatrixBounds
open L1Kernel
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [Nonempty m] [Nonempty n] [Nonempty p]
omit [Nonempty m] in
lemma l1Matrix_mul (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    l1Matrix (A*B) = (l1Matrix A).comp (l1Matrix B) := by
  ext x i
  simp only [l1Matrix_apply,ContinuousLinearMap.comp_apply,Matrix.mul_apply,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring
omit [Nonempty m] in
lemma l1Matrix_sub (A B : Matrix m n ℝ) : l1Matrix (A-B)=l1Matrix A-l1Matrix B := by
  ext x i
  simp [l1Matrix_apply,sub_mul,Finset.sum_sub_distrib]
lemma l1Matrix_inverse [DecidableEq n] (A : Matrix n n ℝ) (hA : IsUnit A) :
    (l1Matrix A).comp (l1Matrix A⁻¹)=1 ∧ (l1Matrix A⁻¹).comp (l1Matrix A)=1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hA
  constructor
  · rw [←l1Matrix_mul,Matrix.mul_nonsing_inv A hd,l1Matrix_one]
  · rw [←l1Matrix_mul,Matrix.nonsing_inv_mul A hd,l1Matrix_one]
end AtomicTriangular.MatrixBounds
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma parameterExp2_bound : Real.exp (-2/Z) < Wstar := by
  have hx : ((RI.point (-2)).mul ZBox.invPos).Mem (-2/Z) := by
    rw [div_eq_mul_inv]
    exact RI.mem_mul (by simpa using RI.mem_point (-2)) (RI.mem_invPos ZBox_mem (by decide +kernel))
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) (by decide +kernel)).1
  rw [parameterExpBox2_calc] at hh
  simp only [Complex.exp_ofReal_re] at hh
  norm_num [RI.Mem,parameterExpBox2,scale,Wstar] at *
  linarith
lemma parameterExp3_bound : Real.exp (-3/Z) < Ustar := by
  have hx : ((RI.point (-3)).mul ZBox.invPos).Mem (-3/Z) := by
    rw [div_eq_mul_inv]
    exact RI.mem_mul (by simpa using RI.mem_point (-3)) (RI.mem_invPos ZBox_mem (by decide +kernel))
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) (by decide +kernel)).1
  rw [parameterExpBox3_calc] at hh
  simp only [Complex.exp_ofReal_re] at hh
  norm_num [RI.Mem,parameterExpBox3,scale,Ustar] at *
  linarith
lemma parameterExp6_bound : Real.exp (-6/Z) < Pstar := by
  have hx : ((RI.point (-6)).mul ZBox.invPos).Mem (-6/Z) := by
    rw [div_eq_mul_inv]
    exact RI.mem_mul (by simpa using RI.mem_point (-6)) (RI.mem_invPos ZBox_mem (by decide +kernel))
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) (by decide +kernel)).1
  rw [parameterExpBox6_calc] at hh
  simp only [Complex.exp_ofReal_re] at hh
  norm_num [RI.Mem,parameterExpBox6,scale,Pstar] at *
  linarith
end AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma delta_parameter_bound {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    (Z-z)*Real.exp (-2/z) < DeltaStar := by
  let t : ℝ := 1/z-1/Z
  have ht : 0≤t := sub_nonneg.mpr (one_div_le_one_div_of_le hz hzB)
  have hid : Z-z = Z*z*t := by
    have hZ : Z ≠ 0 := by norm_num [Z]
    dsimp [t]
    field_simp
  have he : Real.exp (-2/z) = Real.exp (-2/Z)*Real.exp (-(2*t)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  have h1 : (Z-z)*Real.exp (-2/z) ≤ Z^2*Real.exp (-2/Z)*(t*Real.exp (-(2*t))) := by
    rw [hid,he]
    have hh := mul_le_mul_of_nonneg_left hzB
      (show 0≤Z*t*Real.exp (-2/Z)*Real.exp (-(2*t)) by
        have hZ : 0 < Z := by norm_num [Z]
        positivity)
    nlinarith
  have h2 := Real.mul_exp_neg_le_exp_neg_one (2*t)
  have h3 := mul_le_mul_of_nonneg_left h2
    (show 0≤Z^2*Real.exp (-2/Z) by positivity)
  have h4 := mul_le_mul_of_nonneg_left parameterExp2_bound.le
    (show 0≤Z^2*(369/1000:ℝ) by positivity)
  have h5 := mul_le_mul_of_nonneg_left exp_neg_one_bound.le
    (show 0≤Z^2*Real.exp (-2/Z) by positivity)
  norm_num [Z,Wstar,DeltaStar] at *
  nlinarith
lemma actualParameter_mem {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ParameterPolytope (actualParameter z) := by
  have hw := (exp_parameter_mono hz hzB (by norm_num : (0:ℝ)≤2)).trans parameterExp2_bound.le
  have hu := (exp_parameter_mono hz hzB (by norm_num : (0:ℝ)≤3)).trans parameterExp3_bound.le
  have hp := (exp_parameter_mono hz hzB (by norm_num : (0:ℝ)≤6)).trans parameterExp6_bound.le
  have hzp : z*Real.exp (-6/z) ≤ Pstar :=
    (mul_le_of_le_one_left (Real.exp_pos _).le (hzB.trans (by norm_num [Z]))).trans hp
  refine ⟨z,Real.exp (-2/z),(Z-z)*Real.exp (-2/z),Real.exp (-3/z),
    z*Real.exp (-3/z),z*Real.exp (-6/z),Real.exp (-6/z),hz.le,hzB,
    (Real.exp_pos _).le,hw,mul_nonneg (sub_nonneg.mpr hzB) (Real.exp_pos _).le,
    (delta_parameter_bound hz hzB).le,(Real.exp_pos _).le,hu,
    mul_nonneg hz.le (Real.exp_pos _).le,mul_le_mul_of_nonneg_right hzB (Real.exp_pos _).le,
    mul_nonneg hz.le (Real.exp_pos _).le,hzp,(Real.exp_pos _).le,hp,?_⟩
  unfold actualParameter
  congr 1
  ring_nf
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
lemma A1AbsNumerators_calc (i : Fin 23) : rowAbsNumerator (A1Table i) = A1AbsNumerators i := by
  revert i
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_TargetEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate AtomicTriangular.L1Kernel

lemma targetEnvelope_nonneg (v : ℝ) (n : Node) : 0≤targetEnvelope v n.val := by
  have hn : 0<Q n.val := by linarith [(Q_node_bounds n.val n.property.2).1]
  have hZ : 0<Z := by norm_num [Z]
  unfold targetEnvelope
  exact mul_nonneg (mul_nonneg (div_nonneg Q_one_pos.le hn.le) (by positivity)) (Real.exp_pos _).le
lemma gaussianTarget_pair_bound {z : ℝ} (hz : 0<z) (hzB : z≤Z) (v : ℝ)
    (n : Node) (hn : 1≤n.val) :
    (∑ d : Fin 2, |gaussianTarget v z n.val d|) ≤ targetEnvelope v n.val := by
  have hQ : 0<Q n.val := by linarith [(Q_node_bounds n.val n.property.2).1]
  have hZ : 0<Z := by norm_num [Z]
  have hn' : 0≤(n.val:ℝ)-1 := by
    have hi : (1:ℝ)≤(n.val:ℝ) := by exact_mod_cast hn
    linarith
  have he : Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/z) ≤
      Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/Z) := by
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_left hn' hz hzB
    have hnz : (1-(n.val:ℝ))/z = -(((n.val:ℝ)-1)/z) := by ring
    have hnZ : (1-(n.val:ℝ))/Z = -(((n.val:ℝ)-1)/Z) := by ring
    rw [hnz,hnZ]
    linarith
  have hb : z+|-1+(Real.pi*(v-h)-D n.val)*z| ≤ 1+Z+Z*|Real.pi*(v-h)-D n.val| := by
    have ha := abs_add_le (-1:ℝ) ((Real.pi*(v-h)-D n.val)*z)
    rw [abs_mul,abs_of_pos hz] at ha
    norm_num at ha
    have hm := mul_le_mul_of_nonneg_left hzB (abs_nonneg (Real.pi*(v-h)-D n.val))
    linarith
  have hp : 0≤Q 1/Q n.val := div_nonneg Q_one_pos.le hQ.le
  simp only [Fin.sum_univ_succ,gaussianTarget,Fin.val_zero,Fin.val_succ,Fin.isValue,
    ↓reduceIte,Nat.one_ne_zero,Nat.reduceAdd,abs_mul,abs_of_nonneg hp,abs_of_pos (Real.exp_pos _),abs_of_pos hz]
  unfold targetEnvelope
  calc
    _ = (Q 1/Q n.val)*(z+|-1+(Real.pi*(v-h)-D n.val)*z|)*
        Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/z) := by ring
    _ ≤ (Q 1/Q n.val)*(1+Z+Z*|Real.pi*(v-h)-D n.val|)*
        Real.exp (Real.pi*(v-h)*n.val+(1-n.val)/Z) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hb hp) he (Real.exp_pos _).le
        (by positivity)
lemma summable_targetEnvelope : Summable (fun n : TailNode => targetEnvelope h n.val.val) := by
  apply tailEnumeration.summable_iff.mp
  apply (summable_prod_of_nonneg (fun p => targetEnvelope_nonneg h (enumerateTail p).val)).mpr
  refine ⟨fun a => ?_,(hasSum_fintype _).summable⟩
  change Summable (fun l : ℕ => targetEnvelope h (enumerateTail (a,l)).val.val)
  simp_rw [targetEnvelope_enumerate]
  exact (summable_geometric_of_lt_one (Real.exp_pos _).le targetRatio_lt).mul_left _
lemma tsum_targetEnvelope : (∑' n : TailNode, targetEnvelope h n.val.val)=tailTargetEnvelope := by
  rw [←tailEnumeration.tsum_eq]
  have hs := tailEnumeration.summable_iff.mpr summable_targetEnvelope
  change Summable (fun p : Fin 15 × ℕ => targetEnvelope h (enumerateTail p).val.val) at hs
  change (∑' p : Fin 15 × ℕ, targetEnvelope h (enumerateTail p).val.val)=_
  rw [hs.tsum_prod]
  simp_rw [targetEnvelope_enumerate,tsum_mul_left,
    tsum_geometric_of_lt_one (Real.exp_pos _).le targetRatio_lt]
  rw [tsum_fintype,←Finset.sum_mul]
  rfl
lemma tailTarget_bounds {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    Summable (fun p : TailNode × Fin 2 => |gaussianTarget h z p.1.val.val p.2|) ∧
      (∑' p : TailNode × Fin 2, |gaussianTarget h z p.1.val.val p.2|) ≤ tailTargetEnvelope := by
  obtain ⟨hs,hb⟩ := paired_summable_bound (fun (n : TailNode) d => gaussianTarget h z n.val.val d)
    (fun n => targetEnvelope h n.val.val) summable_targetEnvelope
    (fun n => gaussianTarget_pair_bound hz hzB h n.val (by have := n.val.property.1; omega))
  exact ⟨hs,hb.trans_eq tsum_targetEnvelope⟩
def tailTarget (z : ℝ) (hz : 0<z) (hzB : z≤Z) : ℓ¹(TailNode × Fin 2,ℝ) :=
  column (fun p (_ : Unit) => gaussianTarget h z p.1.val.val p.2)
    (fun _ => (tailTarget_bounds hz hzB).1) ()
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
lemma targetRateBox_mem (q : Fin 2) : (targetRateBox q).Mem (Real.pi*(damping q-h)) := by
  fin_cases q
  · simpa [targetRateBox,damping] using ri0_mem
  · convert RI.mem_mul piBox_mem (RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<5)) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [targetRateBox,damping,H,h])
end AtomicTriangular.FiniteCertificate
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
def ATable (side : Fin 2) (i : Fin 23) (r : Fin 8) : RI := if side.val=0 then A1Table i r else A2Table i r
end AtomicTriangular.FiniteCertificate
end

end OAI
end


