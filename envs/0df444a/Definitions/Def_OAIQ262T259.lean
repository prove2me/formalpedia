-- Prove2me | Definitions.Def_OAIQ262T259
-- name    : OAIQ262T259
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T22:10:47.702798+00:00
-- url     : https://prove2.me/theorems/f1483e3e-496d-4256-9d85-211756983f24
-- title:
--   Definitions bundle OAIQ262T259 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 1 definition and 43 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.actualSchwartz`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Construction_ActualInterpolation`, `Triangular_Construction_ActualTail`, `Triangular_Construction_CoefficientAddition`, `Triangular_Construction_ConcreteSchur`, `Triangular_Construction_CurvatureEnvelope`, `Triangular_Construction_CurvatureSums`, `Triangular_Construction_FarCurvature`, `Triangular_Construction_FiniteInterpolation`, `Triangular_Construction_FiniteRemainder`, `Triangular_Construction_Normalization`, `Triangular_Construction_TailInterpolation`, `Triangular_Signs_FarSigns`, `Triangular_Signs_RemainderPre`, `Triangular_Taylor_CurvatureData00`, `Triangular_Taylor_CurvatureData01`, `Triangular_Taylor_TaylorExp`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T253`, `OAIQ262T254`, `OAIQ262T255`, `OAIQ262T256`, `OAIQ262T257` and `OAIQ262T258` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T261`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T253
import Definitions.Def_OAIQ262T254
import Definitions.Def_OAIQ262T255
import Definitions.Def_OAIQ262T256
import Definitions.Def_OAIQ262T257
import Definitions.Def_OAIQ262T258

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

lemma correctionTail_equation (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) :
    correctionTail e r s = splitD e (correctionTail e r s) +
      splitK e (correctionFinite e r s)+s :=
  solution_equations _ _ _ _ _ _ ((splitOperator_norm e).trans_lt (splitQ_lt e))
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_ActualTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma actualTail_equations {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualTail 0 z hz hzB = Doperator (actualTail 1 z hz hzB)+Coperator (actualFiniteError 1 z hz hzB)-
      Aoperator (actualFiniteError 0 z hz hzB)+tailTarget z hz hzB+
      CallOperator (finiteApprox 1 (actualParameter z))-AallOperator (finiteApprox 0 (actualParameter z))+
      (3/500:ℝ) • tailFixedColumn 22 ∧
    actualTail 1 z hz hzB = Doperator (actualTail 0 z hz hzB)+Coperator (actualFiniteError 0 z hz hzB)-
      Aoperator (actualFiniteError 1 z hz hzB)+
      CallOperator (finiteApprox 0 (actualParameter z))-AallOperator (finiteApprox 1 (actualParameter z))-
      (3/500:ℝ) • tailFixedColumn 22 := by
  have hp := correctionTail_equation 0 (finiteResidual z) (approximationTailResidual 0 z hz hzB)
  have hm := correctionTail_equation 1 (finiteResidual z) (approximationTailResidual 1 z hz hzB)
  change actualTailSplit 0 z hz hzB=Doperator (actualTailSplit 0 z hz hzB)+
    (Coperator-Aoperator) (actualFiniteSplit 0 z hz hzB)+approximationTailResidual 0 z hz hzB at hp
  change actualTailSplit 1 z hz hzB=(-Doperator) (actualTailSplit 1 z hz hzB)+
    (-Coperator-Aoperator) (actualFiniteSplit 1 z hz hzB)+approximationTailResidual 1 z hz hzB at hm
  constructor <;> ext i
  all_goals
    have hp' := congrArg (fun u : TailCoefficients => u i) hp
    have hm' := congrArg (fun u : TailCoefficients => u i) hm
    simp only [actualFiniteError,actualTail,approximationTailResidual,
      Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte,
      map_smul,map_add,map_sub,map_neg,sub_apply,neg_apply,
      lp.coeFn_add,lp.coeFn_sub,lp.coeFn_neg,lp.coeFn_smul,
      Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul] at hp' hm' ⊢
    linarith
lemma actualTail_full_equations {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualTail 0 z hz hzB = Doperator (actualTail 1 z hz hzB)+
      CallOperator (actualTrigonometric 1 z hz hzB)-AallOperator (actualTrigonometric 0 z hz hzB)+
      tailTarget z hz hzB+(3/500:ℝ) • tailFixedColumn 22 ∧
    actualTail 1 z hz hzB = Doperator (actualTail 0 z hz hzB)+
      CallOperator (actualTrigonometric 0 z hz hzB)-AallOperator (actualTrigonometric 1 z hz hzB)-
      (3/500:ℝ) • tailFixedColumn 22 := by
  rcases actualTail_equations hz hzB with ⟨h0,h1⟩
  simp only [actualTrigonometric,map_add,CallOperator_extend,AallOperator_extend]
  constructor
  · rw [h0]; abel
  · rw [h1]; abel
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_TailInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma actual_tail_negative {z : ℝ} (hz : 0<z) (hzB : z≤Z) (p : TailNode × Fin 2) :
    (negativeJet h p.1.val.val p.2
      (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 p.1.val.val)
      (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 1 p.1.val.val)).re=
        -gaussianTarget h z p.1.val.val p.2 ∧
    (negativeJet h p.1.val.val p.2
      (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 p.1.val.val)
      (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 1 p.1.val.val)).re=0 := by
  have h0 := congrArg (fun w : TailCoefficients => w p) (actualTail_full_equations hz hzB).1
  have h1 := congrArg (fun w : TailCoefficients => w p) (actualTail_full_equations hz hzB).2
  simp only [lp.coeFn_add,lp.coeFn_sub,lp.coeFn_smul,Pi.add_apply,Pi.sub_apply,
    Pi.smul_apply,smul_eq_mul] at h0 h1
  change _=_+_ -_ +gaussianTarget h z p.1.val.val p.2+(3/500)*tailFixedColumn 22 p at h0
  simp only [pairJJet_negative,add_re,actualInput,Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte,
    inputJJet_tail_direct_negative,inputJJet_tail_transformed]
  constructor <;> linarith
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
lemma actualTrigonometric_shift (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (i : Fin 20) :
    actualTrigonometric side z hz hzB ⟨i.val+2,by omega⟩=
      (finiteSolution side *ᵥ actualParameter z) i+actualFiniteError side z hz hzB i := by
  change finiteApprox side (actualParameter z) _+extendFiniteError (actualFiniteError side z hz hzB) _=_
  rw [finiteApprox_shift,extendFiniteError_shift]
lemma actual_finite_negative {z : ℝ} (hz : 0<z) (hzB : z≤Z) (i : Fin 20) :
    (negativeJet H (rowNode i).val (rowDerivative i)
      (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 (rowNode i).val)
      (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 1 (rowNode i).val)).re=
      -gaussianTarget H z (rowNode i).val (rowDerivative i) ∧
    (negativeJet H (rowNode i).val (rowDerivative i)
      (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 (rowNode i).val)
      (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 1 (rowNode i).val)).re=0 := by
  have h0 := congrArg (fun u : FiniteCoefficients => u i) (actualFiniteError_equations hz hzB).1
  have h1 := congrArg (fun u : FiniteCoefficients => u i) (actualFiniteError_equations hz hzB).2
  simp only [lp.coeFn_add,Pi.add_apply] at h0 h1
  have hf0 := congrArg (fun A : Matrix (Fin 20) (Fin 8) ℝ => (A *ᵥ actualParameter z) i) finiteSolution_equations.1
  have hf1 := congrArg (fun A : Matrix (Fin 20) (Fin 8) ℝ => (A *ᵥ actualParameter z) i) finiteSolution_equations.2
  simp only [Matrix.add_mulVec,←Matrix.mulVec_mulVec,Pi.add_apply] at hf0 hf1
  have hy := Yf_residual z i
  simp only [pairJJet_negative,add_re,actualInput_row_transformed,Pi.add_apply]
  have hd (side : Fin 2) :
      (negativeJet H (rowNode i).val (rowDerivative i)
        (inputJJet (actualInput side z hz hzB) 0 0 (rowNode i).val)
        (inputJJet (actualInput side z hz hzB) 0 1 (rowNode i).val)).re=
        -((finiteSolution side *ᵥ actualParameter z) i+actualFiniteError side z hz hzB i) := by
    rw [actualInput,inputJJet_row_direct_negative,actualTrigonometric_shift]
  simp only [hd]
  change _= -gaussianTarget H z (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ ∧ _=0
  constructor <;> linarith
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
lemma actual_node_negative {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Node) :
    ∃ v : ℝ,∀ d : Fin 2,
      (negativeJet v n.val d
        (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 n.val)
        (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 1 n.val)).re= -gaussianTarget v z n.val d ∧
      (negativeJet v n.val d
        (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 n.val)
        (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 1 n.val)).re=0 := by
  by_cases hn : n.val∈FiniteNodes
  · refine ⟨H,?_⟩
    intro d
    obtain ⟨i,hi,hd⟩ := rowNode_cover n hn d
    have hh := actual_finite_negative hz hzB i
    simpa only [hi,hd] using hh
  · refine ⟨h,?_⟩
    intro d
    exact actual_tail_negative hz hzB (⟨n,hn⟩,d)
lemma actual_interpolation {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Node) :
    actualJ 0 z hz hzB n.val=gaussianG z n.val ∧ deriv (actualJ 0 z hz hzB) n.val=deriv (gaussianG z) n.val ∧
    actualJ 1 z hz hzB n.val=0 ∧ deriv (actualJ 1 z hz hzB) n.val=0 := by
  obtain ⟨v,hv⟩ := actual_node_negative hz hzB n
  have h0 := negativeJet_injective v n
    (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 n.val)
    (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 1 n.val)
    (gaussianG z n.val:ℂ) ((deriv (gaussianG z) (n.val:ℝ):ℝ):ℂ)
    ((hv 0).1.trans (negativeJet_gaussian hz v n.val 0).symm)
    ((hv 1).1.trans (negativeJet_gaussian hz v n.val 1).symm)
  have hn0 (d : Fin 2) : negativeJet v n.val d 0 0=0 := by simp [negativeJet]
  have h1 := negativeJet_injective v n
    (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 n.val)
    (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 1 n.val) 0 0
    (by simpa only [hn0,zero_re] using (hv 0).2) (by simpa only [hn0,zero_re] using (hv 1).2)
  have hd0 := ((hasDerivAt_pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 n.val).real_of_complex).deriv
  have hd1 := ((hasDerivAt_pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 n.val).real_of_complex).deriv
  change deriv (actualJ 0 z hz hzB) n.val=(pairJJet _ _ 1 n.val).re at hd0
  change deriv (actualJ 1 z hz hzB) n.val=(pairJJet _ _ 1 n.val).re at hd1
  exact ⟨h0.1,hd0.trans h0.2,h1.1,hd1.trans h1.2⟩
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_CoefficientAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma actualJ_split (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualJ side z hz hzB = finiteJ side (actualParameter z)+
      pairJ (coefficientInput 0 (extendFiniteError (actualFiniteError side z hz hzB)) (actualTail side z hz hzB))
        (coefficientInput 0 (extendFiniteError (actualFiniteError (otherSide side) z hz hzB)) (actualTail (otherSide side) z hz hzB)) := by
  funext s
  simp only [Pi.add_apply,actualJ,actualInput,actualTrigonometric,finiteJ,finiteJJet_pair,pairJ,pairJJet,inputJJet_split,gamma_actual_constant]
  simp only [add_re]
  ring
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
lemma curvatureData00_3_mem (j : Fin 31) : (curvatureData00_3 j).Mem (curvatureWave 0 0 (curvaturePoint 3) (frequency j)) := by
  rw [← curvatureData00_3_calc]
  exact curvatureBox_mem 0 0 3 j (curvatureData00_3_pre j)
lemma curvatureData00_4_mem (j : Fin 31) : (curvatureData00_4 j).Mem (curvatureWave 0 0 (curvaturePoint 4) (frequency j)) := by
  rw [← curvatureData00_4_calc]
  exact curvatureBox_mem 0 0 4 j (curvatureData00_4_pre j)
lemma curvatureTable00_mem (i : Fin 5) (j : Fin 31) : (curvatureTable00 i j).Mem (curvatureWave 0 0 (curvaturePoint i) (frequency j)) := by
  fin_cases i
  · exact curvatureData00_0_mem j
  · exact curvatureData00_1_mem j
  · exact curvatureData00_2_mem j
  · exact curvatureData00_3_mem j
  · exact curvatureData00_4_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_CurvatureData01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData01_0_mem (j : Fin 31) : (curvatureData01_0 j).Mem (curvatureWave 0 1 (curvaturePoint 0) (frequency j)) := by
  rw [← curvatureData01_0_calc]
  exact curvatureBox_mem 0 1 0 j (curvatureData01_0_pre j)
lemma curvatureData01_1_mem (j : Fin 31) : (curvatureData01_1 j).Mem (curvatureWave 0 1 (curvaturePoint 1) (frequency j)) := by
  rw [← curvatureData01_1_calc]
  exact curvatureBox_mem 0 1 1 j (curvatureData01_1_pre j)
lemma curvatureData01_2_mem (j : Fin 31) : (curvatureData01_2 j).Mem (curvatureWave 0 1 (curvaturePoint 2) (frequency j)) := by
  rw [← curvatureData01_2_calc]
  exact curvatureBox_mem 0 1 2 j (curvatureData01_2_pre j)
lemma curvatureData01_3_mem (j : Fin 31) : (curvatureData01_3 j).Mem (curvatureWave 0 1 (curvaturePoint 3) (frequency j)) := by
  rw [← curvatureData01_3_calc]
  exact curvatureBox_mem 0 1 3 j (curvatureData01_3_pre j)
lemma curvatureData01_4_mem (j : Fin 31) : (curvatureData01_4 j).Mem (curvatureWave 0 1 (curvaturePoint 4) (frequency j)) := by
  rw [← curvatureData01_4_calc]
  exact curvatureBox_mem 0 1 4 j (curvatureData01_4_pre j)
lemma curvatureTable01_mem (i : Fin 5) (j : Fin 31) : (curvatureTable01 i j).Mem (curvatureWave 0 1 (curvaturePoint i) (frequency j)) := by
  fin_cases i
  · exact curvatureData01_0_mem j
  · exact curvatureData01_1_mem j
  · exact curvatureData01_2_mem j
  · exact curvatureData01_3_mem j
  · exact curvatureData01_4_mem j
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
lemma curvatureTail0_bound : rawTailCurvature 0 < (26500:ℝ) := by
  have hh := RI.mem_mul (RI.mem_add (curvatureTable00_mem 0 30) (curvatureTable01_mem 0 15)) (RI.mem_point 60)
  rw [curvatureTail0_calc] at hh
  have hh' := ri_mem_lt hh 26500 1 (by norm_num) (by decide +kernel)
  simpa [rawTailCurvature,mul_comm] using hh'
lemma curvatureTail1_bound : rawTailCurvature 1 < (1160:ℝ) := by
  have hh := RI.mem_mul (RI.mem_add (curvatureTable00_mem 1 30) (curvatureTable01_mem 1 30)) (RI.mem_point 60)
  rw [curvatureTail1_calc] at hh
  have hh' := ri_mem_lt hh 1160 1 (by norm_num) (by decide +kernel)
  simpa [rawTailCurvature,mul_comm] using hh'
lemma curvatureTail2_bound : rawTailCurvature 2 < (800:ℝ) := by
  have hh := RI.mem_mul (RI.mem_add (curvatureTable00_mem 2 30) (curvatureTable01_mem 2 30)) (RI.mem_point 60)
  rw [curvatureTail2_calc] at hh
  have hh' := ri_mem_lt hh 800 1 (by norm_num) (by decide +kernel)
  simpa [rawTailCurvature,mul_comm] using hh'
lemma curvatureConstant3_bound : rawConstantCurvature (curvaturePoint 3) < (122/100000:ℝ) := by
  have hh := RI.mem_divNat (RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable01_mem 3 j) (fourierNorm_mem j))) (by norm_num : 0<2)
  rw [curvatureConstant3_calc] at hh
  have hb := ri_mem_lt hh 122 100000 (by norm_num) (by decide +kernel)
  simpa only [rawConstantCurvature, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
lemma curvatureTail3_bound : rawTailCurvature 3 < (800:ℝ) := by
  have hh := RI.mem_mul (RI.mem_add (curvatureTable00_mem 3 30) (curvatureTable01_mem 3 30)) (RI.mem_point 60)
  rw [curvatureTail3_calc] at hh
  have hh' := ri_mem_lt hh 800 1 (by norm_num) (by decide +kernel)
  simpa [rawTailCurvature,mul_comm] using hh'
lemma curvatureTail4_bound : rawTailCurvature 4 < (800:ℝ) := by
  have hh := RI.mem_mul (RI.mem_add (curvatureTable00_mem 4 30) (curvatureTable01_mem 4 30)) (RI.mem_point 60)
  rw [curvatureTail4_calc] at hh
  have hh' := ri_mem_lt hh 800 1 (by norm_num) (by decide +kernel)
  simpa [rawTailCurvature,mul_comm] using hh'
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

lemma tailCurvatureCap_sum (i : Fin 5) :
    (119/2)*(tailCurvatureCap 0 i+tailCurvatureCap 1 i)≤tailCurvatureEnvelope i := by
  have he : 60*(tailCurvatureCap 0 i+tailCurvatureCap 1 i)=rawTailCurvature i := by
    fin_cases i <;> (first | (simp [tailCurvatureCap,rawTailCurvature,frequency]; all_goals first | (norm_num [tailCurvatureCap,rawTailCurvature,frequency]; done) | rfl | decide) | (norm_num [tailCurvatureCap,rawTailCurvature,frequency]; done) | norm_num [tailCurvatureCap,rawTailCurvature,frequency])
  have hb : rawTailCurvature i<tailCurvatureEnvelope i := by
    fin_cases i
    · exact curvatureTail0_bound
    · exact curvatureTail1_bound
    · exact curvatureTail2_bound
    · exact curvatureTail3_bound
    · exact curvatureTail4_bound
  nlinarith [tailCurvatureCap_nonneg 0 i,tailCurvatureCap_nonneg 1 i]
lemma pairJ_curvature (a b : TrigonometricCoefficients) (w v : TailCoefficients)
    (i : Fin 5) {s aL aT : ℝ} (hs : curvaturePoint i≤ s)
    (ha : ‖a‖≤aL) (hb : ‖b‖≤aL) (hw : ‖w‖≤aT) (hv : ‖v‖≤aT) :
    |iteratedDeriv 2 (pairJ (coefficientInput 0 a w) (coefficientInput 0 b v)) s|/2≤
      aL*finiteCurvatureEnvelope i+aT*tailCurvatureEnvelope i := by
  rw [←pairJJet_iterated]
  have hTa := tailSpectral_curvature a w 0 i hs
  have hTb := tailSpectral_curvature b v 1 i hs
  have hLa := finiteSpectral_curvature 0 a w 0 i hs
  have hLb := finiteSpectral_curvature 0 b v 1 i hs
  have hh := Complex.abs_re_le_norm (pairJJet (coefficientInput 0 a w) (coefficientInput 0 b v) 2 s)
  have hN := norm_add_le (inputJJet (coefficientInput 0 a w) 0 2 s) (inputJJet (coefficientInput 0 b v) 1 2 s)
  have hNa := norm_add_le (tailSpectral (coefficientInput 0 a w) (waveFunctionJet 0 0 2 s)) (finiteSpectral (coefficientInput 0 a w) (waveFunctionJet 1 0 2 s))
  have hNb := norm_add_le (tailSpectral (coefficientInput 0 b v) (waveFunctionJet 0 1 2 s)) (finiteSpectral (coefficientInput 0 b v) (waveFunctionJet 1 1 2 s))
  have hL0 := mul_le_mul_of_nonneg_right ha (finiteCurvatureCap_nonneg 0 i)
  have hL1 := mul_le_mul_of_nonneg_right hb (finiteCurvatureCap_nonneg 1 i)
  have hT0 := mul_le_mul_of_nonneg_right hw (tailCurvatureCap_nonneg 0 i)
  have hT1 := mul_le_mul_of_nonneg_right hv (tailCurvatureCap_nonneg 1 i)
  have hLf := mul_le_mul_of_nonneg_left (finiteCurvatureCap_sum i) ((norm_nonneg a).trans ha)
  have hTf := mul_le_mul_of_nonneg_left (tailCurvatureCap_sum i) ((norm_nonneg w).trans hw)
  change |(pairJJet _ _ 2 s).re|/2≤_
  dsimp only [pairJJet,inputJJet] at hh hN ⊢
  nlinarith
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

lemma transformedP_curvature {s : ℝ} (hs : 29/2 ≤ s) :
    |iteratedDeriv 2 transformedP s|/2 ≤ 2/1000 := by
  rw [←transformedP_jet]
  have hh := abs_re_le_norm (spectralPCLM (waveFunctionJet 0 1 2 s))
  have hn := norm_sum_le (s:=Finset.univ) (fun j : Fin 31 => fourierCoeff j*(waveFunctionJet 0 1 2 (s:ℂ)) ⟨frequency j,frequency_mem j⟩)
  have he (j : Fin 31) :
      ‖fourierCoeff j*(waveFunctionJet 0 1 2 (s:ℂ)) ⟨frequency j,frequency_mem j⟩‖=
        curvatureWave 0 1 s (frequency j)*‖fourierCoeff j‖ := by
    rw [norm_mul,waveFunctionJet_apply,norm_finiteWaveJet_two]
    ring
  simp only [he] at hn
  change ‖spectralPCLM (waveFunctionJet 0 1 2 s)‖ ≤ _ at hn
  have hb := (rawConstantCurvature_antitone hs).trans curvatureConstant3_bound.le
  change rawConstantCurvature s ≤ 122/100000 at hb
  dsimp only [rawConstantCurvature] at hb
  nlinarith
lemma actualJ_decompose (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    actualJ side z hz hzB=sideConstant side • realP+actualJ0 side z hz hzB := by
  funext s
  simp only [actualJ,actualInput,pairJ,pairJJet,actualJ0,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul]
  rw [inputJJet_constant (if side.val=0 then -(3/500) else 3/500) _ _ 0,
    inputJJet_constant (if (otherSide side).val=0 then -(3/500) else 3/500) _ _ 1]
  simp only [add_re]
  rw [(spectralP_direct _).1,P_ofReal]
  simp only [ofReal_re,mul_re,ofReal_im,zero_mul,sub_zero,transformedP,sideConstant]
  ring
lemma actualJ0_curvature (side : Fin 2) {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (i : Fin 5) (hs : curvaturePoint i ≤ s) (hs14 : 29/2 ≤ s) :
    |iteratedDeriv 2 (actualJ0 side z hz hzB) s|/2 ≤
      (301/100)*finiteCurvatureEnvelope i+(3/1000000000)*tailCurvatureEnvelope i+(3/500)*(2/1000) := by
  let f := pairJ (coefficientInput 0 (actualTrigonometric side z hz hzB) (actualTail side z hz hzB))
    (coefficientInput 0 (actualTrigonometric (otherSide side) z hz hzB) (actualTail (otherSide side) z hz hzB))
  have hf : ContDiff ℝ 2 f := (pairJ_contDiff _ _).of_le (by norm_num)
  have hg : ContDiff ℝ 2 (sideConstant (otherSide side) • transformedP) := by
    change ContDiff ℝ 2 (fun s => sideConstant (otherSide side)*transformedP s)
    simpa only [smul_eq_mul] using (transformedP_contDiff.const_smul (sideConstant (otherSide side))).of_le (show (2:WithTop ℕ∞) ≤ ⊤ by exact le_top)
  have hl (side : Fin 2) : ‖actualTrigonometric side z hz hzB‖ ≤ 301/100 := by
    have hh := actualTrigonometric_norm side hz hzB
    linarith
  have ht (side : Fin 2) : ‖actualTail side z hz hzB‖ ≤ (3/1000000000:ℝ) := by
    simpa only [show (10:ℝ)^9=1000000000 by norm_num] using (actualTail_norm side hz hzB).le
  have hh := pairJ_curvature _ _ _ _ i hs (hl side) (hl (otherSide side)) (ht side) (ht (otherSide side))
  have hT := transformedP_curvature hs14
  change |iteratedDeriv 2 (f+sideConstant (otherSide side) • transformedP) s|/2 ≤ _
  rw [iteratedDeriv_add hf.contDiffAt hg.contDiffAt,iteratedDeriv_const_smul ((transformedP_contDiff.of_le (by norm_num)).contDiffAt)]
  simp only [smul_eq_mul]
  have hc : |sideConstant (otherSide side)|=(3/500:ℝ) := by unfold sideConstant; split_ifs <;> norm_num
  have ha := abs_add_le (iteratedDeriv 2 f s) (sideConstant (otherSide side)*iteratedDeriv 2 transformedP s)
  rw [abs_mul,hc] at ha
  change |iteratedDeriv 2 f s|/2 ≤ _ at hh
  nlinarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExpTable_mem (q br : Fin 2) (n : Fin 7) (j : Fin 31) :
    (taylorExpTable q br n j).Mem (exp (taylorPhase q br (frequency j)*(nearNode n:ℂ))) := by
  fin_cases q <;> fin_cases br <;> fin_cases n
  · exact taylorExp0_0_1_mem j
  · exact taylorExp0_0_3_mem j
  · exact taylorExp0_0_4_mem j
  · exact taylorExp0_0_7_mem j
  · exact taylorExp0_0_9_mem j
  · exact taylorExp0_0_12_mem j
  · exact taylorExp0_0_13_mem j
  · exact taylorExp0_1_1_mem j
  · exact taylorExp0_1_3_mem j
  · exact taylorExp0_1_4_mem j
  · exact taylorExp0_1_7_mem j
  · exact taylorExp0_1_9_mem j
  · exact taylorExp0_1_12_mem j
  · exact taylorExp0_1_13_mem j
  · exact taylorExp1_0_1_mem j
  · exact taylorExp1_0_3_mem j
  · exact taylorExp1_0_4_mem j
  · exact taylorExp1_0_7_mem j
  · exact taylorExp1_0_9_mem j
  · exact taylorExp1_0_12_mem j
  · exact taylorExp1_0_13_mem j
  · exact taylorExp1_1_1_mem j
  · exact taylorExp1_1_3_mem j
  · exact taylorExp1_1_4_mem j
  · exact taylorExp1_1_7_mem j
  · exact taylorExp1_1_9_mem j
  · exact taylorExp1_1_12_mem j
  · exact taylorExp1_1_13_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderPre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainder_ratio_lt_one (q br : Fin 2) (n : Fin 7) (j : Fin 31) :
    nearRadius n*‖taylorPhase q br (frequency j)‖/24<1 := by
  have hh := (RI.mem_sub ri1_mem (RI.mem_divNat
    (RI.mem_mul (nearRadiusBox_mem n) (taylorNormTable_mem q br j)) (by norm_num : 0<24))).1
  have hp : (0:ℝ)<((RI.point 1).sub (((nearRadiusBox n).mul (taylorNormTable q br j)).divNat 24)).lo :=
    by exact_mod_cast remainder_all_pre q br n j
  have hs := AtomicTriangular.Interval.scale_pos
  nlinarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma finiteWave_error (q br : Fin 2) (n : Fin 7) (j : Fin 31) {v : ℝ} (hv : |v|≤nearRadius n) :
    ‖complexError (fun k s => finiteWaveJet q br (frequency j) k s) (nearNode n) v‖≤
      remainderWave q br (nearNode n) (nearRadius n) (frequency j) := by
  have he : (fun (k : ℕ) (s : ℝ) => finiteWaveJet q br (frequency j) k s)=
      (fun (k : ℕ) (s : ℝ) => taylorAmplitude q br (frequency j)*(Complex.exp (taylorPhase q br (frequency j)*(s:ℂ))*(taylorPhase q br (frequency j))^k)) := by
    funext k s; simp only [finiteWaveJet,mul_assoc]
  rw [he,complexError_mul,complexError,complexDeleted_exp,complexTaylor_exp,norm_mul]
  have hb := Envelope.expDeleted_error (taylorPhase q br (frequency j)) (nearNode n) v (nearRadius n)
    (nearRadius_nonneg n) hv (remainder_ratio_lt_one q br n j)
  have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg (taylorAmplitude q br (frequency j)))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (simp only [remainderWave,curvatureWave,Complex.norm_exp,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]; ring)
lemma remainderWave_nonneg (q br : Fin 2) (n : Fin 7) (j : Fin 31) :
    0 ≤ remainderWave q br (nearNode n) (nearRadius n) (frequency j) := by
  unfold remainderWave
  have hp := sub_pos.mpr (remainder_ratio_lt_one q br n j)
  have hy := nearRadius_nonneg n
  have hc := curvatureWave_nonneg q br (nearNode n) (frequency j)
  positivity
lemma rawRemainderColumn_nonneg (br : Fin 2) (n : Fin 7) (c : Fin 22) :
    0 ≤ rawRemainderColumn br n c := Finset.sum_nonneg fun j _ => mul_nonneg (remainderWave_nonneg 1 br n j) (norm_nonneg _)
lemma atom_remainder_bound (S : Fin 31 → ℂ) (q br : Fin 2) (n : Fin 7) {v : ℝ} (hv : |v|≤nearRadius n) :
    ‖complexError (fun k s => ∑ j : Fin 31,S j*finiteWaveJet q br (frequency j) k s) (nearNode n) v‖≤
      ∑ j : Fin 31,remainderWave q br (nearNode n) (nearRadius n) (frequency j)*‖S j‖ := by
  rw [complexError_sum]
  simp only [complexError_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right (finiteWave_error q br n j hv) (norm_nonneg _)
lemma finite_input_error (C : ℝ) (a : TrigonometricCoefficients) (br : Fin 2) (n : Fin 7) {v M : ℝ}
    (hv : |v|≤nearRadius n) (hM : ∀ c : Fin 22,rawRemainderColumn br n c≤M) :
    ‖complexError (fun k s => inputJJet (coefficientInput C a 0) br k s) (nearNode n) v‖≤
      |C| *rawRemainderConstant br n+‖a‖*M := by
  simp only [inputJJet_zero_tail]
  rw [complexError_add,complexError_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (atom_remainder_bound fourierCoeff 0 br n hv) (abs_nonneg _)
  · rw [complexError_sum]
    simp only [complexError_mul]
    calc
      _ ≤ ∑ c : Fin 22,‖(a c:ℂ)*complexError (fun k s => ∑ j : Fin 31,finiteColumn ⟨c.val,by omega⟩ j*finiteWaveJet 1 br (frequency j) k s) (nearNode n) v‖ := norm_sum_le _ _
      _ ≤ ∑ c : Fin 22,|a c| *M := by
        apply Finset.sum_le_sum
        intro c _
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((atom_remainder_bound _ 1 br n hv).trans (hM c)) (abs_nonneg _)
      _ = ‖a‖*M := by rw [←Finset.sum_mul,AtomicTriangular.L1Kernel.l1_norm,tsum_fintype]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_FarSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma actualJ0_jets (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (n : Node) :
    actualJ0 side z hz hzB n.val=actualJ side z hz hzB n.val ∧
      deriv (actualJ0 side z hz hzB) n.val=deriv (actualJ side z hz hzB) n.val := by
  have hp := realP_jet_zero n
  have hv := congrFun (actualJ_decompose side hz hzB) (n.val:ℝ)
  have hd := ((realP_contDiff.differentiable (by norm_num) (n.val:ℝ)).hasDerivAt.const_mul (sideConstant side)).add
    ((actualJ0_contDiff side hz hzB).differentiable (by norm_num) (n.val:ℝ)).hasDerivAt
  change HasDerivAt (sideConstant side • realP+actualJ0 side z hz hzB) _ _ at hd
  rw [←actualJ_decompose side hz hzB] at hd
  constructor
  · simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hp.1,mul_zero,zero_add] using hv.symm
  · simpa only [hp.2,mul_zero,zero_add] using hd.deriv.symm
lemma actualJ0_deleted (side : Fin 2) {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Node) (i : Fin 5) (hs : curvaturePoint i ≤ s) (hm : curvaturePoint i ≤ (n.val:ℝ))
    (hs14 : 29/2 ≤ s) (hm14 : 29/2 ≤ (n.val:ℝ)) :
    |deletedSecond (actualJ0 side z hz hzB) n.val s| ≤ farK i := by
  have hh := deletedSecond_bound ((actualJ0_contDiff side hz hzB).of_le (by norm_num))
    (m:=(n.val:ℝ)) (s:=s) (C:=2*farK i) (by
      intro t ht
      have hi : curvaturePoint i ≤ t := (le_min hm hs).trans ht.1
      have h14 : 29/2 ≤ t := (le_min hm14 hs14).trans ht.1
      have hc := actualJ0_curvature side hz hzB i hi h14
      change |iteratedDeriv 2 (actualJ0 side z hz hzB) t|/2 ≤ farK i at hc
      linarith)
  simpa using hh
end AtomicTriangular.Construction
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
def actualSchwartz (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z ≤ Z) : 𝓢(Plane,ℝ) :=
  (normalizingDen z)⁻¹ • pairSchwartz (actualInput side z hz hzB) (actualInput (otherSide side) z hz hzB)
lemma actualSchwartz_apply (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (x : Plane) :
    actualSchwartz side z hz hzB x=Real.exp (-Real.pi*h*radial x)*actualJ side z hz hzB (radial x)/normalizingDen z := by
  simp only [actualSchwartz,smul_apply,smul_eq_mul,pairSchwartz_radialJ,actualJ]
  ring
lemma actualSchwartz_radial (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    Radial (actualSchwartz side z hz hzB) := by
  intro x y hxy
  simp only [actualSchwartz_apply,radial,hxy]
lemma actualSchwartz_fourier_side (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (x : Plane) :
    realFourier (actualSchwartz side z hz hzB) x=(actualSchwartz (otherSide side) z hz hzB x:ℂ) := by
  unfold actualSchwartz
  simp only [realFourier,smul_apply,smul_eq_mul,ofReal_mul]
  change 𝓕 (((((normalizingDen z)⁻¹:ℝ):ℂ)) • (fun x => (pairSchwartz (actualInput side z hz hzB) (actualInput (otherSide side) z hz hzB) x:ℂ))) x=_
  rw [complex_fourier_smul]
  change (((normalizingDen z)⁻¹:ℝ):ℂ)*realFourier (pairSchwartz (actualInput side z hz hzB) (actualInput (otherSide side) z hz hzB)) x=_
  rw [pairSchwartz_fourier]
  fin_cases side <;> rfl
lemma actualSchwartz_fourier {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (x : Plane) :
    realFourier (actualSchwartz 0 z hz hzB) x=(actualSchwartz 1 z hz hzB x:ℂ) :=
  actualSchwartz_fourier_side 0 hz hzB x
lemma actualSchwartz_node {α : ℝ} (hα : 1 ≤ α) (x : Plane) (n : Node) (hx : radial x=n.val) :
    actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x = AtomicTriangular.gaussian α x ∧
      actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x=0 := by
  have hj := actual_interpolation (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le n
  rw [actualSchwartz_apply,actualSchwartz_apply,←gaussian_normalization hα x,hx,hj.1,hj.2.2.1]
  simp
end AtomicTriangular.Construction
end

end OAI
end


