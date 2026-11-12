-- Prove2me | Definitions.Def_OAIQ262T143
-- name    : OAIQ262T143
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:39:31.222071+00:00
-- url     : https://prove2.me/theorems/3bf928b6-174d-444f-8dd8-8447338ad2f2
-- title:
--   Definitions bundle OAIQ262T143 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 68 declarations of OpenAI's Lean: 1 definition and 67 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.spectrumTable`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_ParamNorm`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamNorm.lean), [`Triangular_Certificate_ParamNormBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamNormBase.lean), [`Triangular_Certificate_ParamU`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamU.lean), [`Triangular_Certificate_PolytopeInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/PolytopeInterval.lean), [`Triangular_Certificate_TargetInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/TargetInterval.lean), [`Triangular_Construction_BlockOperators`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean), [`Triangular_Construction_CurvatureEnvelope`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureEnvelope.lean), [`Triangular_Construction_CurvatureSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureSums.lean), [`Triangular_Construction_FiniteInterpolation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/FiniteInterpolation.lean), [`Triangular_Taylor_CurvatureData10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData10.lean), [`Triangular_Taylor_CurvatureData11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData11.lean), [`Triangular_Taylor_TaylorSpectrum`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T085`, `OAIQ262T086`, `OAIQ262T088`, `OAIQ262T089`, `OAIQ262T092`, `OAIQ262T093`, `OAIQ262T094`, `OAIQ262T095`, `OAIQ262T096`, `OAIQ262T100` and `OAIQ262T101` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T157`, `OAIQ262T158` and `OAIQ262T161`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T085
import Definitions.Def_OAIQ262T086
import Definitions.Def_OAIQ262T088
import Definitions.Def_OAIQ262T089
import Definitions.Def_OAIQ262T092
import Definitions.Def_OAIQ262T093
import Definitions.Def_OAIQ262T094
import Definitions.Def_OAIQ262T095
import Definitions.Def_OAIQ262T096
import Definitions.Def_OAIQ262T100
import Definitions.Def_OAIQ262T101

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
lemma UminusTableRow5_calc (j : Fin 8) : UminusCachedBox 5 j = UminusTableRow5 j := by
  revert j
  decide +kernel
lemma UminusTableRow6_calc (j : Fin 8) : UminusCachedBox 6 j = UminusTableRow6 j := by
  revert j
  decide +kernel
lemma UminusTableRow7_calc (j : Fin 8) : UminusCachedBox 7 j = UminusTableRow7 j := by
  revert j
  decide +kernel
lemma UminusTableRow8_calc (j : Fin 8) : UminusCachedBox 8 j = UminusTableRow8 j := by
  revert j
  decide +kernel
lemma UminusTableRow9_calc (j : Fin 8) : UminusCachedBox 9 j = UminusTableRow9 j := by
  revert j
  decide +kernel
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
lemma tailFixedColumn_apply (c : Fin 23) (p : TailNode × Fin 2) :
    tailFixedColumn c p = jet (if c.val=22 then h else H) h p.1.val.val p.2 (finiteColumn c) := rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_PolytopeInterval
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
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamNormBase
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
lemma A2AbsNumerators_calc (i : Fin 23) : rowAbsNumerator (A2Table i) = A2AbsNumerators i := by
  revert i
  decide +kernel
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
lemma targetExpf9_calc : (CI.ofReal (targetExpInput 1 9)).exp.re=targetExpf9 := by decide +kernel
lemma targetEnvf9_calc : targetEnvBox 1 QBox9 DBox9 targetExpf9=targetEnvf9 := by decide +kernel
lemma targetExpf12_calc : (CI.ofReal (targetExpInput 1 12)).exp.re=targetExpf12 := by decide +kernel
lemma targetEnvf12_calc : targetEnvBox 1 QBox12 DBox12 targetExpf12=targetEnvf12 := by decide +kernel
lemma targetExpf13_calc : (CI.ofReal (targetExpInput 1 13)).exp.re=targetExpf13 := by decide +kernel
lemma targetEnvf13_calc : targetEnvBox 1 QBox13 DBox13 targetExpf13=targetEnvf13 := by decide +kernel
lemma targetExpf16_calc : (CI.ofReal (targetExpInput 1 16)).exp.re=targetExpf16 := by decide +kernel
lemma targetEnvf16_calc : targetEnvBox 1 QBox16 DBox16 targetExpf16=targetEnvf16 := by decide +kernel
lemma targetExpf19_calc : (CI.ofReal (targetExpInput 1 19)).exp.re=targetExpf19 := by decide +kernel
lemma targetEnvf19_calc : targetEnvBox 1 QBox19 DBox19 targetExpf19=targetEnvf19 := by decide +kernel
lemma targetExpf21_calc : (CI.ofReal (targetExpInput 1 21)).exp.re=targetExpf21 := by decide +kernel
lemma targetEnvf21_calc : targetEnvBox 1 QBox21 DBox21 targetExpf21=targetEnvf21 := by decide +kernel
lemma targetExpt36_calc : (CI.ofReal (targetExpInput 0 36)).exp.re=targetExpt36 := by decide +kernel
lemma targetEnvt36_calc : targetEnvBox 0 QBox0 DBox0 targetExpt36=targetEnvt36 := by decide +kernel
lemma targetExpt37_calc : (CI.ofReal (targetExpInput 0 37)).exp.re=targetExpt37 := by decide +kernel
lemma targetEnvt37_calc : targetEnvBox 0 QBox1 DBox1 targetExpt37=targetEnvt37 := by decide +kernel
lemma targetExpt39_calc : (CI.ofReal (targetExpInput 0 39)).exp.re=targetExpt39 := by decide +kernel
lemma targetEnvt39_calc : targetEnvBox 0 QBox3 DBox3 targetExpt39=targetEnvt39 := by decide +kernel
lemma targetExpt40_calc : (CI.ofReal (targetExpInput 0 40)).exp.re=targetExpt40 := by decide +kernel
lemma targetEnvt40_calc : targetEnvBox 0 QBox4 DBox4 targetExpt40=targetEnvt40 := by decide +kernel
lemma targetExpt43_calc : (CI.ofReal (targetExpInput 0 43)).exp.re=targetExpt43 := by decide +kernel
lemma targetEnvt43_calc : targetEnvBox 0 QBox7 DBox7 targetExpt43=targetEnvt43 := by decide +kernel
lemma targetExpt45_calc : (CI.ofReal (targetExpInput 0 45)).exp.re=targetExpt45 := by decide +kernel
lemma targetEnvt45_calc : targetEnvBox 0 QBox9 DBox9 targetExpt45=targetEnvt45 := by decide +kernel
lemma targetExpt48_calc : (CI.ofReal (targetExpInput 0 48)).exp.re=targetExpt48 := by decide +kernel
lemma targetEnvt48_calc : targetEnvBox 0 QBox12 DBox12 targetExpt48=targetEnvt48 := by decide +kernel
lemma targetExpt49_calc : (CI.ofReal (targetExpInput 0 49)).exp.re=targetExpt49 := by decide +kernel
lemma targetEnvt49_calc : targetEnvBox 0 QBox13 DBox13 targetExpt49=targetEnvt49 := by decide +kernel
lemma targetExpt52_calc : (CI.ofReal (targetExpInput 0 52)).exp.re=targetExpt52 := by decide +kernel
lemma targetEnvt52_calc : targetEnvBox 0 QBox16 DBox16 targetExpt52=targetEnvt52 := by decide +kernel
lemma targetExpt55_calc : (CI.ofReal (targetExpInput 0 55)).exp.re=targetExpt55 := by decide +kernel
lemma targetEnvt55_calc : targetEnvBox 0 QBox19 DBox19 targetExpt55=targetEnvt55 := by decide +kernel
lemma targetExpt57_calc : (CI.ofReal (targetExpInput 0 57)).exp.re=targetExpt57 := by decide +kernel
lemma targetEnvt57_calc : targetEnvBox 0 QBox21 DBox21 targetExpt57=targetEnvt57 := by decide +kernel
lemma targetExpt25_calc : (CI.ofReal (targetExpInput 0 25)).exp.re=targetExpt25 := by decide +kernel
lemma targetEnvt25_calc : targetEnvBox 0 QBox25 DBox25 targetExpt25=targetEnvt25 := by decide +kernel
lemma targetExpt27_calc : (CI.ofReal (targetExpInput 0 27)).exp.re=targetExpt27 := by decide +kernel
lemma targetEnvt27_calc : targetEnvBox 0 QBox27 DBox27 targetExpt27=targetEnvt27 := by decide +kernel
lemma targetExpt28_calc : (CI.ofReal (targetExpInput 0 28)).exp.re=targetExpt28 := by decide +kernel
lemma targetEnvt28_calc : targetEnvBox 0 QBox28 DBox28 targetExpt28=targetEnvt28 := by decide +kernel
lemma targetExpt31_calc : (CI.ofReal (targetExpInput 0 31)).exp.re=targetExpt31 := by decide +kernel
lemma targetEnvt31_calc : targetEnvBox 0 QBox31 DBox31 targetExpt31=targetEnvt31 := by decide +kernel
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
lemma curvatureData10_2_calc (j : Fin 31) : curvatureBox 1 0 2 j=curvatureData10_2 j := by
  revert j
  decide +kernel
lemma curvatureData10_3_calc (j : Fin 31) : curvatureBox 1 0 3 j=curvatureData10_3 j := by
  revert j
  decide +kernel
lemma curvatureData10_4_calc (j : Fin 31) : curvatureBox 1 0 4 j=curvatureData10_4 j := by
  revert j
  decide +kernel
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
lemma curvatureData11_0_calc (j : Fin 31) : curvatureBox 1 1 0 j=curvatureData11_0 j := by
  revert j
  decide +kernel
lemma curvatureData11_3_calc (j : Fin 31) : curvatureBox 1 1 3 j=curvatureData11_3 j := by
  revert j
  decide +kernel
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
lemma curvatureColumn0_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable10 0 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn0_0 c := by
  revert c
  decide +kernel
lemma curvatureColumn0_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable10 1 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn0_1 c := by
  revert c
  decide +kernel
lemma curvatureColumn0_2_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable10 2 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn0_2 c := by
  revert c
  decide +kernel
lemma curvatureColumn0_3_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable10 3 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn0_3 c := by
  revert c
  decide +kernel
lemma curvatureColumn0_4_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable10 4 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn0_4 c := by
  revert c
  decide +kernel
lemma curvatureColumn1_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable11 0 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn1_0 c := by
  revert c
  decide +kernel
lemma curvatureColumn1_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable11 1 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn1_1 c := by
  revert c
  decide +kernel
lemma curvatureColumn1_2_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (curvatureTable11 2 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=curvatureColumn1_2 c := by
  revert c
  decide +kernel
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

lemma tailCurvatureCap_nonneg (br : Fin 2) (i : Fin 5) : 0≤tailCurvatureCap br i := curvatureWave_nonneg _ _ _ _
end AtomicTriangular.Construction
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
lemma extendFiniteError_transformed (u : FiniteCoefficients) (i : Fin 20) :
    (∑ c : Fin 22,extendFiniteError u c*jet H H (rowNode i).val (rowDerivative i)
      (finiteColumn ⟨c.val,by omega⟩))=Roperator u i := by
  have hh := finiteRow_sum 0 (extendFiniteError u) i
  have h0 : extendFiniteError u 0=0 := extendFiniteError_fixed u 0
  have h1 : extendFiniteError u 1=0 := extendFiniteError_fixed u 1
  erw [h0] at hh
  simp only [extendFiniteError_shift,zero_mul,zero_add,mul_zero,add_zero] at hh
  rw [hh,Roperator_apply]
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
def spectrumTable : Fin 2 → Fin 2 → Fin 31 → Fin 8 → CI := ![![spectrum0_0,spectrum0_1],![spectrum1_0,spectrum1_1]]
end AtomicTriangular.FiniteCertificate
end

end OAI
end


