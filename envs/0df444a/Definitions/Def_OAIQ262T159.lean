-- Prove2me | Definitions.Def_OAIQ262T159
-- name    : OAIQ262T159
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T20:19:50.312544+00:00
-- url     : https://prove2.me/theorems/c5d22b24-e71a-4c5f-96fe-030bb6e7ee90
-- title:
--   Definitions bundle OAIQ262T159 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 28 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Construction_DirectCoordinates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/DirectCoordinates.lean), [`Triangular_Construction_DirectWaveJets`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/DirectWaveJets.lean), [`Triangular_Construction_FiniteCoordinates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/FiniteCoordinates.lean), [`Triangular_Construction_FiniteProjection`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/FiniteProjection.lean), [`Triangular_Construction_NodeJets`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/NodeJets.lean), [`Triangular_Construction_TailCoordinates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/TailCoordinates.lean), [`Triangular_Signs_DeletedAccuracy`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/DeletedAccuracy.lean), [`Triangular_Signs_RemainderData0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData0.lean), [`Triangular_Signs_RemainderPre`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderPre.lean), [`Triangular_Taylor_TaylorWave000`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave000.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T137`, `OAIQ262T144`, `OAIQ262T145`, `OAIQ262T146`, `OAIQ262T147` and `OAIQ262T148` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T194`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T137
import Definitions.Def_OAIQ262T144
import Definitions.Def_OAIQ262T145
import Definitions.Def_OAIQ262T146
import Definitions.Def_OAIQ262T147
import Definitions.Def_OAIQ262T148

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

lemma dBasis_cBasis (n : Node) : dBasis n = fun s => (s-(n.val:ℂ))*cBasis n s := by
  funext s
  by_cases hs : s = (n.val:ℂ)
  · simp [hs,dBasis_node]
  · rw [dBasis_eq n hs,cBasis_eq n hs]
    field_simp
lemma deriv_dBasis_at_node (n : Node) : deriv (dBasis n) n.val = cBasis n n.val := by
  have hh := (((hasDerivAt_id (n.val:ℂ)).sub_const (n.val:ℂ)).mul
    ((differentiable_cBasis n _).hasDerivAt)).deriv
  rw [dBasis_cBasis n]
  simpa using! hh

lemma cBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) : cBasis n m.val = 0 := by
  rw [cBasis_eq n (by exact_mod_cast hmn),P_node,zero_div]

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
lemma spectralD_direct (n : Node) (s : ℂ) :
    spectralDCLM n (waveFunctionJet 0 0 0 s)=dBasis n s ∧
    spectralDCLM n (waveFunctionJet 0 0 1 s)=deriv (dBasis n) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,spectralDCLM_apply,spectralD_phase]
  · have he : (fun s => spectralDCLM n (phaseFunction s))=dBasis n := funext fun s => by rw [spectralDCLM_apply,spectralD_phase]
    have hh := ((spectralDCLM n).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma atomC_direct (a : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.cCoefficient a) (waveFunctionJet 0 0 0 s)=finiteC a s ∧
    atomSpectral (FiniteCertificate.cCoefficient a) (waveFunctionJet 0 0 1 s)=deriv (finiteC a) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,atomSpectral_finiteC_phase]
  · have he : (fun s => atomSpectral (FiniteCertificate.cCoefficient a) (phaseFunction s))=finiteC a := funext (atomSpectral_finiteC_phase a)
    have hh := ((atomSpectral (FiniteCertificate.cCoefficient a)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma atomD_direct (a : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.dCoefficient a) (waveFunctionJet 0 0 0 s)=finiteD a s ∧
    atomSpectral (FiniteCertificate.dCoefficient a) (waveFunctionJet 0 0 1 s)=deriv (finiteD a) s := by
  constructor
  · rw [waveFunctionJet_zero_phase,atomSpectral_finiteD_phase]
  · have he : (fun s => atomSpectral (FiniteCertificate.dCoefficient a) (phaseFunction s))=finiteD a := funext (atomSpectral_finiteD_phase a)
    have hh := ((atomSpectral (FiniteCertificate.dCoefficient a)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_phaseFunction s)).deriv
    simp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.symm
lemma waveFunctionJet_direct_one (q : Fin 2) (s : ℂ) :
    waveFunctionJet q 0 1 s= exp (-(Real.pi:ℂ)*(damping q-h)*s) •
      (waveFunctionJet 0 0 1 s-(Real.pi*(damping q-h):ℂ) • phaseFunction s) := by
  have he : waveFunctionJet q 0 0 = fun t => exp (-(Real.pi:ℂ)*(damping q-h)*t) • phaseFunction t := funext (waveFunctionJet_direct_zero q)
  have hh := (((hasDerivAt_id s).const_mul (-(Real.pi:ℂ)*(damping q-h))).cexp.smul (hasDerivAt_phaseFunction s)).deriv
  have hj := (hasDerivAt_waveFunctionJet q 0 0 s).deriv
  rw [he] at hj
  change deriv (fun t => exp (-(Real.pi:ℂ)*(damping q-h)*t) • phaseFunction t) s = _ at hh
  rw [←hj,hh]
  simp only [id_eq,mul_one]
  module
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
lemma damped_wave_re (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (n : ℤ) :
    (T (waveFunctionJet q 0 0 n)).re=Real.exp (-Real.pi*(damping q-h)*n)*(T (waveFunctionJet 0 0 0 n)).re ∧
    (T (waveFunctionJet q 0 1 n)).re=Real.exp (-Real.pi*(damping q-h)*n)*
      ((T (waveFunctionJet 0 0 1 n)).re-Real.pi*(damping q-h)*(T (waveFunctionJet 0 0 0 n)).re) := by
  have he : exp (-(Real.pi:ℂ)*(damping q-h)*(n:ℂ))=(Real.exp (-Real.pi*(damping q-h)*n):ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; rfl
  constructor
  · rw [waveFunctionJet_direct_zero,map_smul,←waveFunctionJet_zero_phase,he]
    simp only [smul_eq_mul,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
  · rw [waveFunctionJet_direct_one,map_smul,map_sub,map_smul,←waveFunctionJet_zero_phase,he]
    simp only [smul_eq_mul,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,sub_re,mul_im,sub_im,mul_zero,add_zero]
lemma negativeJet_direct_re (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (negativeJet v n d (T (waveFunctionJet q 0 0 n)) (T (waveFunctionJet q 0 1 n))).re=
      Real.exp (Real.pi*(v-damping q)*n)/(Q n)*
        (if d.val=0 then -(T (waveFunctionJet 0 0 0 n)).re else
          (D n-Real.pi*(v-damping q))*(T (waveFunctionJet 0 0 0 n)).re-(T (waveFunctionJet 0 0 1 n)).re) := by
  rw [negativeJet_re,(damped_wave_re T q n).1,(damped_wave_re T q n).2]
  have he : Real.exp (Real.pi*(v-h)*n)*Real.exp (-Real.pi*(damping q-h)*n)=
      Real.exp (Real.pi*(v-damping q)*n) := by rw [←Real.exp_add]; congr 1; ring
  split_ifs
  · linear_combination (-(T (waveFunctionJet 0 0 0 n)).re/(Q n))*he
  · linear_combination (((D n-Real.pi*(v-damping q))*(T (waveFunctionJet 0 0 0 n)).re-(T (waveFunctionJet 0 0 1 n)).re)/(Q n))*he

lemma negativeJet_direct_linear (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (T (waveFunctionJet q 0 0 n)) (T (waveFunctionJet q 0 1 n))=
      T (directJetFunction q v n d) := by
  unfold directJetFunction negativeJet
  split_ifs <;> simp only [map_smul,map_neg,map_sub,smul_eq_mul]
lemma spectralP_directJet (q : Fin 2) (v : ℝ) (n : Node) (d : Fin 2) :
    (spectralPCLM (directJetFunction q v n.val d)).re=0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralP_direct _).1,(spectralP_direct _).2,P_node,deriv_P_node]
  split_ifs <;> simp
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma atomC_directJet (a : Fin 15) (v : ℝ) (n : Node) (d : Fin 2) :
    (atomSpectral (FiniteCertificate.cCoefficient a) (directJetFunction 1 v n.val d)).re=
      if n.val%36=residue a then Real.exp (Real.pi*(v-H)*n.val)*
        (if d.val=0 then -1 else -Real.pi*(v-H)) else 0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(atomC_direct a _).1,(atomC_direct a _).2]
  simp only [damping,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  by_cases hm : n.val%36=residue a
  · rw [(finiteC_matching_jets a n.val hm).1,finiteC_deriv_re a n.val hm,ite_eq_left hm]
    split_ifs <;> field_simp [Q_node_ne n]
    ring
  · rw [(finiteC_other_jets a n hm).1,(finiteC_other_jets a n hm).2,ite_eq_right hm]
    split_ifs <;> simp
lemma atomD_directJet (a : Fin 15) (v : ℝ) (n : Node) (d : Fin 2) :
    (atomSpectral (FiniteCertificate.dCoefficient a) (directJetFunction 1 v n.val d)).re=
      if n.val%36=residue a then Real.exp (Real.pi*(v-H)*n.val)*
        (if d.val=0 then 0 else -1) else 0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(atomD_direct a _).1,(atomD_direct a _).2]
  simp only [damping,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  by_cases hm : n.val%36=residue a
  · rw [(finiteD_matching_jets a n.val hm).1,(finiteD_matching_jets a n.val hm).2,
      (finiteC_matching_jets a n.val hm).1,ite_eq_left hm]
    split_ifs <;> simp only [zero_re,neg_zero,mul_zero,zero_sub]
    field_simp [Q_node_ne n]
  · rw [(finiteD_other_jets a n hm).1,(finiteD_other_jets a n hm).2,ite_eq_right hm]
    split_ifs <;> simp
lemma finiteColumn_directJet (c : Fin 22) (v : ℝ) (n : Node) (d : Fin 2) :
    (atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 v n.val d)).re=
      if n.val%36=residue ⟨c.val/2,by omega⟩ then Real.exp (Real.pi*(v-H)*n.val)*
        (if c.val%2=0 then (if d.val=0 then -1 else -Real.pi*(v-H))
         else (if d.val=0 then 0 else -1)) else 0 := by
  unfold finiteColumn
  simp only [show c.val<22 from c.isLt,↓reduceDIte]
  by_cases hc : c.val%2=0
  · simp only [hc,↓reduceIte]
    exact atomC_directJet _ _ _ _
  · simp only [hc,↓reduceIte]
    exact atomD_directJet _ _ _ _
lemma finiteColumn_tail_directJet (c : Fin 22) (p : TailNode × Fin 2) :
    (atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 h p.1.val.val p.2)).re= -AallKernel p c := by
  rw [finiteColumn_directJet]
  unfold AallKernel repetitionKernel repetitionEntry
  have he : h-H= -eta := by norm_num [h,H,eta]
  simp only [he,mul_neg]
  split_ifs <;> ring_nf
lemma finiteSpectral_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (v : ℝ) (n : ℤ) (d : Fin 2) :
    (finiteSpectral (coefficientInput C a w) (directJetFunction 1 v n d)).re=
      ∑ c : Fin 22,a c*(atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 v n d)).re := by
  rw [finiteSpectral_coefficient]
  simp only [sum_apply,smul_apply,smul_eq_mul,re_sum,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
lemma finiteSpectral_tail_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (p : TailNode × Fin 2) :
    (finiteSpectral (coefficientInput C a w) (directJetFunction 1 h p.1.val.val p.2)).re= -AallOperator a p := by
  rw [finiteSpectral_directJet]
  simp_rw [finiteColumn_tail_directJet,mul_neg]
  rw [Finset.sum_neg_distrib]
  congr 1
  unfold AallOperator
  erw [AtomicTriangular.L1Kernel.operator_apply,tsum_fintype]
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
lemma inputJJet_direct_negative (a : InputCoefficients) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (inputJJet a 0 0 n) (inputJJet a 0 1 n)=
      tailSpectral a (directJetFunction 0 v n d)+finiteSpectral a (directJetFunction 1 v n d) := by
  unfold inputJJet
  rw [negativeJet_add,negativeJet_direct_linear,negativeJet_direct_linear]
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
lemma finiteColumn_row_directJet (c : Fin 22) (i : Fin 20) :
    (atomSpectral (finiteColumn ⟨c.val,by omega⟩) (directJetFunction 1 H (rowNode i).val (rowDerivative i))).re=
      if c=⟨i.val+2,by omega⟩ then -1 else 0 := by
  rw [finiteColumn_directJet]
  simp only [sub_self,mul_zero,zero_mul,Real.exp_zero,one_mul,rowDerivative]
  have hh := finite_column_matching i c
  have hc0 : c.val%2<2 := Nat.mod_lt _ (by norm_num)
  have hi0 : i.val%2<2 := Nat.mod_lt _ (by norm_num)
  simp only [Fin.ext_iff]
  split_ifs <;> norm_num at * <;> (try omega)
  all_goals split_ifs <;> norm_num at * <;> try omega
  all_goals simp_all only [↓reduceIte]
  all_goals
    split_ifs <;> norm_num at *
    omega
lemma finiteSpectral_row_directJet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (i : Fin 20) :
    (finiteSpectral (coefficientInput C a w) (directJetFunction 1 H (rowNode i).val (rowDerivative i))).re=
      -a ⟨i.val+2,by omega⟩ := by
  rw [finiteSpectral_directJet]
  simp only [finiteColumn_row_directJet,mul_ite,mul_neg,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_0_6_calc (j : Fin 31) : taylorWaveBox 0 0 0 6 j = tw0_0_0_6 j := by
  revert j
  decide +kernel
lemma tw0_0_0_9_calc (j : Fin 31) : taylorWaveBox 0 0 0 9 j = tw0_0_0_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData0_00_calc (j : Fin 31) : remainderBox 0 0 0 j (taylorNormTable 0 0 j)=remainderData0_00 j := by
  revert j
  decide +kernel
lemma remainderData0_01_calc (j : Fin 31) : remainderBox 0 1 0 j (taylorNormTable 0 1 j)=remainderData0_01 j := by
  revert j
  decide +kernel
lemma remainderData0_10_calc (j : Fin 31) : remainderBox 1 0 0 j (taylorNormTable 1 0 j)=remainderData0_10 j := by
  revert j
  decide +kernel
lemma remainderData0_11_calc (j : Fin 31) : remainderBox 1 1 0 j (taylorNormTable 1 1 j)=remainderData0_11 j := by
  revert j
  decide +kernel
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
lemma remainder_all_pre (q br : Fin 2) (n : Fin 7) (j : Fin 31) :
    0<((RI.point 1).sub (((nearRadiusBox n).mul (taylorNormTable q br j)).divNat 24)).lo := by
  fin_cases n <;> fin_cases q <;> fin_cases br
  · exact (remainderData0_00_pre j).2
  · exact (remainderData0_01_pre j).2
  · exact (remainderData0_10_pre j).2
  · exact (remainderData0_11_pre j).2
  · exact (remainderData1_00_pre j).2
  · exact (remainderData1_01_pre j).2
  · exact (remainderData1_10_pre j).2
  · exact (remainderData1_11_pre j).2
  · exact (remainderData2_00_pre j).2
  · exact (remainderData2_01_pre j).2
  · exact (remainderData2_10_pre j).2
  · exact (remainderData2_11_pre j).2
  · exact (remainderData3_00_pre j).2
  · exact (remainderData3_01_pre j).2
  · exact (remainderData3_10_pre j).2
  · exact (remainderData3_11_pre j).2
  · exact (remainderData4_00_pre j).2
  · exact (remainderData4_01_pre j).2
  · exact (remainderData4_10_pre j).2
  · exact (remainderData4_11_pre j).2
  · exact (remainderData5_00_pre j).2
  · exact (remainderData5_01_pre j).2
  · exact (remainderData5_10_pre j).2
  · exact (remainderData5_11_pre j).2
  · exact (remainderData6_00_pre j).2
  · exact (remainderData6_01_pre j).2
  · exact (remainderData6_10_pre j).2
  · exact (remainderData6_11_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_DeletedAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma finiteJ_contDiff (side : Fin 2) (e : Fin 8 → ℝ) : ContDiff ℝ ⊤ (finiteJ side e) := by
  have he : finiteJ side e=pairJ (coefficientInput ((gamma side *ᵥ e) 2) (finiteApprox side e) 0)
      (coefficientInput ((gamma (otherSide side) *ᵥ e) 2) (finiteApprox (otherSide side) e) 0) := by
    funext s; exact congrArg Complex.re (finiteJJet_pair side e 0 s)
  rw [he]
  exact pairJ_contDiff _ _
end AtomicTriangular.Construction
end

end OAI
end


