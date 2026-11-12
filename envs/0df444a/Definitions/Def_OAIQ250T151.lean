-- Prove2me | Definitions.Def_OAIQ250T151
-- name    : OAIQ250T151
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:27:18.288073+00:00
-- url     : https://prove2.me/theorems/6cd02717-ac40-44dc-aa1e-9cd7144e7a35
-- title:
--   Definitions bundle OAIQ250T151 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 70 declarations of OpenAI's Lean: 70 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_MatrixInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/MatrixInterval.lean), [`Triangular_Certificate_ParamInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamInterval.lean), [`Triangular_Certificate_ParamNormBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamNormBase.lean), [`Triangular_Certificate_PolytopeInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/PolytopeInterval.lean), [`Triangular_Certificate_TargetInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/TargetInterval.lean), [`Triangular_Construction_L1Matrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/L1Matrix.lean), [`Triangular_Taylor_CurvatureData01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData01.lean), [`Triangular_Taylor_TaylorPhase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorPhase.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T047`, `OAIQ250T048`, `OAIQ250T049`, `OAIQ250T148` and `OAIQ250T050` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T099`, `OAIQ250T102`, `OAIQ250T103`, `OAIQ250T106`, `OAIQ250T107` and `OAIQ250T108`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T047
import Definitions.Def_OAIQ250T048
import Definitions.Def_OAIQ250T049
import Definitions.Def_OAIQ250T148
import Definitions.Def_OAIQ250T050

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_MatrixInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval
open Matrix AtomicTriangular.MatrixBounds

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
lemma matrixNorm_bound [Nonempty n] {a : m → n → RI} {A : Matrix m n ℝ} {b : ℤ}
    (ha : ∀ i j, (a i j).Mem (A i j)) (hb : ∀ j, matrixColBound a j ≤ b) :
    matNorm A ≤ (b:ℝ)/(scale:ℝ) := by
  apply matNorm_le
  intro j
  have hh := (RI.mem_sum (fun i => RI.mem_abs (ha i j))).2
  apply (le_div_iff₀ scale_pos).mpr
  change colNorm A j * (scale:ℝ) ≤ (b:ℝ)
  rw [mul_comm]
  apply hh.trans
  exact_mod_cast hb j

end AtomicTriangular.Interval
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
lemma plusApprox_bound : matNorm plusApprox ≤ (3885/1000:ℝ) := by
  have hh := matrixNorm_bound (b := 3885000000000000000000000000000000000000000000000000000000000) plusApproxBox_mem (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
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
lemma plusResidualRow19_calc (j : Fin 20) : plusResidualBox 19 j = plusResidualRow19 j := by
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
lemma targetCoefficientBox_mem (n : Fin 10) : (targetCoefficientBox n).Mem (targetCoefficient n) := by
  have he : ((Complex.exp ((Real.pi*eta*(finiteNode n):ℝ):ℂ))).re = Real.exp (Real.pi*eta*(finiteNode n)) := by rw [Complex.exp_ofReal_re]
  have hq : ∀ n : Fin 10, 0 < (QTable n).lo := by decide +kernel
  unfold targetCoefficient
  rw [div_eq_mul_inv]
  apply RI.mem_mul (RI.mem_mul QBox1_mem (RI.mem_invPos (QTable_mem n) (hq n)))
  simpa only [he] using (targetExpTable_mem n).1

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_L1Matrix
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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_PolytopeInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma rowLowerBox_mem {a : Fin 8 → RI} {v : Fin 8 → ℝ}
    (hv : ∀ i, (a i).Mem (v i)) : (rowLowerBox a).Mem (rowLower v) := by
  have hz : (RI.point 0).Mem (0:ℝ) := by simpa using RI.mem_point 0
  unfold rowLowerBox rowLower
  apply RI.mem_add
  · apply RI.mem_add
    · apply RI.mem_add
      · apply RI.mem_add
        · exact RI.mem_add (hv 1) (RI.mem_mul ZBox_mem (RI.mem_min hz (hv 0)))
        · exact RI.mem_mul DeltaStarBox_mem (RI.mem_min hz (RI.mem_neg (hv 2)))
      · exact RI.mem_mul WstarBox_mem (RI.mem_min hz (RI.mem_add (hv 3) (RI.mem_mul ZBox_mem (hv 2))))
    · exact RI.mem_mul UstarBox_mem (RI.mem_min hz (RI.mem_min (hv 5) (RI.mem_add (hv 5) (RI.mem_mul ZBox_mem (hv 4)))))
  · exact RI.mem_mul PstarBox_mem (RI.mem_add (RI.mem_min hz (hv 6)) (RI.mem_min hz (hv 7)))
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamNormBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma rowAbs_bound {a : Fin 8 → RI} {v : Fin 8 → ℝ}
    (hv : ∀ j, (a j).Mem (v j)) (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    |∑ j : Fin 8, v j*e j| ≤ (rowAbsNumerator a : ℝ)/scale := by
  have h1 := (rowLowerBox_mem hv).1
  have h2 := (rowLowerBox_mem (fun j => RI.mem_neg (hv j))).1
  have h3 := rowLower_le v e he
  have h4 := rowLower_le (fun j => -v j) e he
  have heq : (∑ j : Fin 8, -v j*e j) = -(∑ j : Fin 8, v j*e j) := by simp only [neg_mul,Finset.sum_neg_distrib]
  rw [heq] at h4
  have hb1 : (-(rowLowerBox a).lo:ℝ) ≤ (rowAbsNumerator a:ℝ) := by
    exact_mod_cast (le_max_left (-(rowLowerBox a).lo) _)
  have hb2 : (-(rowLowerBox (fun j => (a j).neg)).lo:ℝ) ≤ (rowAbsNumerator a:ℝ) := by
    exact_mod_cast (le_max_right (-(rowLowerBox a).lo) _)
  apply abs_le.mpr
  constructor
  · rw [← neg_div]
    apply (div_le_iff₀ scale_pos).mpr
    have hg := mul_le_mul_of_nonneg_left h3 scale_pos.le
    nlinarith
  · apply (le_div_iff₀ scale_pos).mpr
    have hg := mul_le_mul_of_nonneg_left h4 scale_pos.le
    nlinarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_TargetInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma targetExpInput_mem (q : Fin 2) (n : ℤ) :
    (targetExpInput q n).Mem (Real.pi*(damping q-h)*n+(1-n)/Z) := by
  apply RI.mem_add (RI.mem_mul (targetRateBox_mem q) (RI.mem_point n))
  rw [div_eq_mul_inv]
  exact RI.mem_mul (by simpa using RI.mem_point (1-n))
    (RI.mem_invPos targetZBox_mem (by decide +kernel))
lemma targetEnvBox_mem (q : Fin 2) (n : ℤ) {qb db eb : RI}
    (hq : qb.Mem (Q n)) (hd : db.Mem (D n))
    (he : eb.Mem (Real.exp (Real.pi*(damping q-h)*n+(1-n)/Z))) (hp : 0<qb.lo) :
    (targetEnvBox q qb db eb).Mem (targetEnvelope (damping q) n) := by
  unfold targetEnvelope
  rw [div_eq_mul_inv]
  exact RI.mem_mul (RI.mem_mul (RI.mem_mul QBox1_mem (RI.mem_invPos hq hp))
    (RI.mem_add (RI.mem_add ri1_mem targetZBox_mem)
      (RI.mem_mul targetZBox_mem (RI.mem_abs (RI.mem_sub (targetRateBox_mem q) hd))))) he

lemma targetExpf9_mem : targetExpf9.Mem (Real.exp (Real.pi*(damping 1-h)*(9:ℤ)+(1-(9:ℤ))/Z)) := by
  rw [← targetExpf9_calc]
  exact ri_exp_mem (targetExpInput_mem 1 9) (by decide +kernel)
lemma targetEnvf9_mem : targetEnvf9.Mem (targetEnvelope (damping 1) 9) := by
  rw [← targetEnvf9_calc]
  apply targetEnvBox_mem 1 9 _ _ targetExpf9_mem (by decide +kernel)
  · exact QBox9_mem
  · exact DBox9_mem
lemma targetExpf12_mem : targetExpf12.Mem (Real.exp (Real.pi*(damping 1-h)*(12:ℤ)+(1-(12:ℤ))/Z)) := by
  rw [← targetExpf12_calc]
  exact ri_exp_mem (targetExpInput_mem 1 12) (by decide +kernel)
lemma targetEnvf12_mem : targetEnvf12.Mem (targetEnvelope (damping 1) 12) := by
  rw [← targetEnvf12_calc]
  apply targetEnvBox_mem 1 12 _ _ targetExpf12_mem (by decide +kernel)
  · exact QBox12_mem
  · exact DBox12_mem
lemma targetExpf13_mem : targetExpf13.Mem (Real.exp (Real.pi*(damping 1-h)*(13:ℤ)+(1-(13:ℤ))/Z)) := by
  rw [← targetExpf13_calc]
  exact ri_exp_mem (targetExpInput_mem 1 13) (by decide +kernel)
lemma targetEnvf13_mem : targetEnvf13.Mem (targetEnvelope (damping 1) 13) := by
  rw [← targetEnvf13_calc]
  apply targetEnvBox_mem 1 13 _ _ targetExpf13_mem (by decide +kernel)
  · exact QBox13_mem
  · exact DBox13_mem
lemma targetExpf16_mem : targetExpf16.Mem (Real.exp (Real.pi*(damping 1-h)*(16:ℤ)+(1-(16:ℤ))/Z)) := by
  rw [← targetExpf16_calc]
  exact ri_exp_mem (targetExpInput_mem 1 16) (by decide +kernel)
lemma targetEnvf16_mem : targetEnvf16.Mem (targetEnvelope (damping 1) 16) := by
  rw [← targetEnvf16_calc]
  apply targetEnvBox_mem 1 16 _ _ targetExpf16_mem (by decide +kernel)
  · exact QBox16_mem
  · exact DBox16_mem
lemma targetExpf19_mem : targetExpf19.Mem (Real.exp (Real.pi*(damping 1-h)*(19:ℤ)+(1-(19:ℤ))/Z)) := by
  rw [← targetExpf19_calc]
  exact ri_exp_mem (targetExpInput_mem 1 19) (by decide +kernel)
lemma targetEnvf19_mem : targetEnvf19.Mem (targetEnvelope (damping 1) 19) := by
  rw [← targetEnvf19_calc]
  apply targetEnvBox_mem 1 19 _ _ targetExpf19_mem (by decide +kernel)
  · exact QBox19_mem
  · exact DBox19_mem
lemma targetExpf21_mem : targetExpf21.Mem (Real.exp (Real.pi*(damping 1-h)*(21:ℤ)+(1-(21:ℤ))/Z)) := by
  rw [← targetExpf21_calc]
  exact ri_exp_mem (targetExpInput_mem 1 21) (by decide +kernel)
lemma targetExpt36_mem : targetExpt36.Mem (Real.exp (Real.pi*(damping 0-h)*(36:ℤ)+(1-(36:ℤ))/Z)) := by
  rw [← targetExpt36_calc]
  exact ri_exp_mem (targetExpInput_mem 0 36) (by decide +kernel)
lemma targetEnvt36_mem : targetEnvt36.Mem (targetEnvelope (damping 0) 36) := by
  rw [← targetEnvt36_calc]
  apply targetEnvBox_mem 0 36 _ _ targetExpt36_mem (by decide +kernel)
  · rw [Q_emod 36]; norm_num; exact QBox0_mem
  · rw [D_emod 36]; norm_num; exact DBox0_mem
lemma targetExpt37_mem : targetExpt37.Mem (Real.exp (Real.pi*(damping 0-h)*(37:ℤ)+(1-(37:ℤ))/Z)) := by
  rw [← targetExpt37_calc]
  exact ri_exp_mem (targetExpInput_mem 0 37) (by decide +kernel)
lemma targetEnvt37_mem : targetEnvt37.Mem (targetEnvelope (damping 0) 37) := by
  rw [← targetEnvt37_calc]
  apply targetEnvBox_mem 0 37 _ _ targetExpt37_mem (by decide +kernel)
  · rw [Q_emod 37]; norm_num; exact QBox1_mem
  · rw [D_emod 37]; norm_num; exact DBox1_mem
lemma targetExpt39_mem : targetExpt39.Mem (Real.exp (Real.pi*(damping 0-h)*(39:ℤ)+(1-(39:ℤ))/Z)) := by
  rw [← targetExpt39_calc]
  exact ri_exp_mem (targetExpInput_mem 0 39) (by decide +kernel)
lemma targetEnvt39_mem : targetEnvt39.Mem (targetEnvelope (damping 0) 39) := by
  rw [← targetEnvt39_calc]
  apply targetEnvBox_mem 0 39 _ _ targetExpt39_mem (by decide +kernel)
  · rw [Q_emod 39]; norm_num; exact QBox3_mem
  · rw [D_emod 39]; norm_num; exact DBox3_mem
lemma targetExpt40_mem : targetExpt40.Mem (Real.exp (Real.pi*(damping 0-h)*(40:ℤ)+(1-(40:ℤ))/Z)) := by
  rw [← targetExpt40_calc]
  exact ri_exp_mem (targetExpInput_mem 0 40) (by decide +kernel)
lemma targetEnvt40_mem : targetEnvt40.Mem (targetEnvelope (damping 0) 40) := by
  rw [← targetEnvt40_calc]
  apply targetEnvBox_mem 0 40 _ _ targetExpt40_mem (by decide +kernel)
  · rw [Q_emod 40]; norm_num; exact QBox4_mem
  · rw [D_emod 40]; norm_num; exact DBox4_mem
lemma targetExpt43_mem : targetExpt43.Mem (Real.exp (Real.pi*(damping 0-h)*(43:ℤ)+(1-(43:ℤ))/Z)) := by
  rw [← targetExpt43_calc]
  exact ri_exp_mem (targetExpInput_mem 0 43) (by decide +kernel)
lemma targetEnvt43_mem : targetEnvt43.Mem (targetEnvelope (damping 0) 43) := by
  rw [← targetEnvt43_calc]
  apply targetEnvBox_mem 0 43 _ _ targetExpt43_mem (by decide +kernel)
  · rw [Q_emod 43]; norm_num; exact QBox7_mem
  · rw [D_emod 43]; norm_num; exact DBox7_mem
lemma targetExpt45_mem : targetExpt45.Mem (Real.exp (Real.pi*(damping 0-h)*(45:ℤ)+(1-(45:ℤ))/Z)) := by
  rw [← targetExpt45_calc]
  exact ri_exp_mem (targetExpInput_mem 0 45) (by decide +kernel)
lemma targetEnvt45_mem : targetEnvt45.Mem (targetEnvelope (damping 0) 45) := by
  rw [← targetEnvt45_calc]
  apply targetEnvBox_mem 0 45 _ _ targetExpt45_mem (by decide +kernel)
  · rw [Q_emod 45]; norm_num; exact QBox9_mem
  · rw [D_emod 45]; norm_num; exact DBox9_mem
lemma targetExpt48_mem : targetExpt48.Mem (Real.exp (Real.pi*(damping 0-h)*(48:ℤ)+(1-(48:ℤ))/Z)) := by
  rw [← targetExpt48_calc]
  exact ri_exp_mem (targetExpInput_mem 0 48) (by decide +kernel)
lemma targetEnvt48_mem : targetEnvt48.Mem (targetEnvelope (damping 0) 48) := by
  rw [← targetEnvt48_calc]
  apply targetEnvBox_mem 0 48 _ _ targetExpt48_mem (by decide +kernel)
  · rw [Q_emod 48]; norm_num; exact QBox12_mem
  · rw [D_emod 48]; norm_num; exact DBox12_mem
lemma targetExpt49_mem : targetExpt49.Mem (Real.exp (Real.pi*(damping 0-h)*(49:ℤ)+(1-(49:ℤ))/Z)) := by
  rw [← targetExpt49_calc]
  exact ri_exp_mem (targetExpInput_mem 0 49) (by decide +kernel)
lemma targetEnvt49_mem : targetEnvt49.Mem (targetEnvelope (damping 0) 49) := by
  rw [← targetEnvt49_calc]
  apply targetEnvBox_mem 0 49 _ _ targetExpt49_mem (by decide +kernel)
  · rw [Q_emod 49]; norm_num; exact QBox13_mem
  · rw [D_emod 49]; norm_num; exact DBox13_mem
lemma targetExpt52_mem : targetExpt52.Mem (Real.exp (Real.pi*(damping 0-h)*(52:ℤ)+(1-(52:ℤ))/Z)) := by
  rw [← targetExpt52_calc]
  exact ri_exp_mem (targetExpInput_mem 0 52) (by decide +kernel)
lemma targetEnvt52_mem : targetEnvt52.Mem (targetEnvelope (damping 0) 52) := by
  rw [← targetEnvt52_calc]
  apply targetEnvBox_mem 0 52 _ _ targetExpt52_mem (by decide +kernel)
  · rw [Q_emod 52]; norm_num; exact QBox16_mem
  · rw [D_emod 52]; norm_num; exact DBox16_mem
lemma targetExpt55_mem : targetExpt55.Mem (Real.exp (Real.pi*(damping 0-h)*(55:ℤ)+(1-(55:ℤ))/Z)) := by
  rw [← targetExpt55_calc]
  exact ri_exp_mem (targetExpInput_mem 0 55) (by decide +kernel)
lemma targetEnvt55_mem : targetEnvt55.Mem (targetEnvelope (damping 0) 55) := by
  rw [← targetEnvt55_calc]
  apply targetEnvBox_mem 0 55 _ _ targetExpt55_mem (by decide +kernel)
  · rw [Q_emod 55]; norm_num; exact QBox19_mem
  · rw [D_emod 55]; norm_num; exact DBox19_mem
lemma targetExpt57_mem : targetExpt57.Mem (Real.exp (Real.pi*(damping 0-h)*(57:ℤ)+(1-(57:ℤ))/Z)) := by
  rw [← targetExpt57_calc]
  exact ri_exp_mem (targetExpInput_mem 0 57) (by decide +kernel)
lemma targetExpt25_mem : targetExpt25.Mem (Real.exp (Real.pi*(damping 0-h)*(25:ℤ)+(1-(25:ℤ))/Z)) := by
  rw [← targetExpt25_calc]
  exact ri_exp_mem (targetExpInput_mem 0 25) (by decide +kernel)
lemma targetEnvt25_mem : targetEnvt25.Mem (targetEnvelope (damping 0) 25) := by
  rw [← targetEnvt25_calc]
  apply targetEnvBox_mem 0 25 _ _ targetExpt25_mem (by decide +kernel)
  · exact QBox25_mem
  · exact DBox25_mem
lemma targetExpt27_mem : targetExpt27.Mem (Real.exp (Real.pi*(damping 0-h)*(27:ℤ)+(1-(27:ℤ))/Z)) := by
  rw [← targetExpt27_calc]
  exact ri_exp_mem (targetExpInput_mem 0 27) (by decide +kernel)
lemma targetEnvt27_mem : targetEnvt27.Mem (targetEnvelope (damping 0) 27) := by
  rw [← targetEnvt27_calc]
  apply targetEnvBox_mem 0 27 _ _ targetExpt27_mem (by decide +kernel)
  · exact QBox27_mem
  · exact DBox27_mem
lemma targetExpt28_mem : targetExpt28.Mem (Real.exp (Real.pi*(damping 0-h)*(28:ℤ)+(1-(28:ℤ))/Z)) := by
  rw [← targetExpt28_calc]
  exact ri_exp_mem (targetExpInput_mem 0 28) (by decide +kernel)
lemma targetEnvt28_mem : targetEnvt28.Mem (targetEnvelope (damping 0) 28) := by
  rw [← targetEnvt28_calc]
  apply targetEnvBox_mem 0 28 _ _ targetExpt28_mem (by decide +kernel)
  · exact QBox28_mem
  · exact DBox28_mem
lemma targetExpt31_mem : targetExpt31.Mem (Real.exp (Real.pi*(damping 0-h)*(31:ℤ)+(1-(31:ℤ))/Z)) := by
  rw [← targetExpt31_calc]
  exact ri_exp_mem (targetExpInput_mem 0 31) (by decide +kernel)
lemma targetEnvt31_mem : targetEnvt31.Mem (targetEnvelope (damping 0) 31) := by
  rw [← targetEnvt31_calc]
  apply targetEnvBox_mem 0 31 _ _ targetExpt31_mem (by decide +kernel)
  · exact QBox31_mem
  · exact DBox31_mem
lemma targetRatioBox_mem : targetRatioBox.Mem (Real.exp (-36/Z)) := by
  rw [←targetRatioBox_calc]
  apply ri_exp_mem
  · rw [div_eq_mul_inv]
    exact RI.mem_mul (by simpa using RI.mem_point (-36)) (RI.mem_invPos targetZBox_mem (by decide +kernel))
  · decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorPhase
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

lemma taylorPhase0_0_mem (j : Fin 31) : (taylorPhase0_0 j).Mem (taylorPhase 0 0 (frequency j)) := by
  rw [← taylorPhase0_0_calc]
  exact taylorPhaseBox_mem 0 0 j
lemma taylorPhase0_1_mem (j : Fin 31) : (taylorPhase0_1 j).Mem (taylorPhase 0 1 (frequency j)) := by
  rw [← taylorPhase0_1_calc]
  exact taylorPhaseBox_mem 0 1 j
lemma taylorPhase1_0_mem (j : Fin 31) : (taylorPhase1_0 j).Mem (taylorPhase 1 0 (frequency j)) := by
  rw [← taylorPhase1_0_calc]
  exact taylorPhaseBox_mem 1 0 j
lemma taylorPhase1_1_mem (j : Fin 31) : (taylorPhase1_1 j).Mem (taylorPhase 1 1 (frequency j)) := by
  rw [← taylorPhase1_1_calc]
  exact taylorPhaseBox_mem 1 1 j
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
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData01_1_calc (j : Fin 31) : curvatureBox 0 1 1 j=curvatureData01_1 j := by
  revert j
  decide +kernel
lemma curvatureData01_2_calc (j : Fin 31) : curvatureBox 0 1 2 j=curvatureData01_2 j := by
  revert j
  decide +kernel
lemma curvatureData01_3_calc (j : Fin 31) : curvatureBox 0 1 3 j=curvatureData01_3 j := by
  revert j
  decide +kernel
lemma curvatureData01_4_calc (j : Fin 31) : curvatureBox 0 1 4 j=curvatureData01_4 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


