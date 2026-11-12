-- Prove2me | Definitions.Def_OAIQ262T088
-- name    : OAIQ262T088
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:50:30.972201+00:00
-- url     : https://prove2.me/theorems/47716c00-5678-4fcf-baa8-ff2b7ba76114
-- title:
--   Definitions bundle OAIQ262T088 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 2 definitions and 22 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.psiTableD`, `OAI.AtomicTriangular.FiniteCertificate.targetExpInput`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_TargetInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/TargetInterval.lean), [`Triangular_Construction_BlockOperators`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean), [`Triangular_Construction_TailJetVector`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/TailJetVector.lean), [`Triangular_Envelope_Analytic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/Analytic.lean), [`Triangular_Envelope_EnvelopeBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeBoxes.lean), [`Triangular_Envelope_EnvelopePsiC`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiC.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean), [`Triangular_Envelope_JetEnvelopeAnalytic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/JetEnvelopeAnalytic.lean), [`Triangular_Envelope_KernelBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/KernelBounds.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005`, `OAIQ262T006`, `OAIQ262T007`, `OAIQ262T008` and `OAIQ262T012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T137`, `OAIQ262T138`, `OAIQ262T139`, `OAIQ262T142` and `OAIQ262T143`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T006
import Definitions.Def_OAIQ262T007
import Definitions.Def_OAIQ262T008
import Definitions.Def_OAIQ262T012

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma damping_Xwave_lower (q : Fin 2) {t : ℝ} (ht0 : 0≤t) (ht : t≤5/6) :
    1≤Real.pi*damping q*Xwave (damping q) t := by
  have hx := Xwave_antitone (damping_pos q) ht0 ht
  have hl : 1<3*damping q*Xwave (damping q) (5/6) := by
    fin_cases q <;> (first | (simp [damping,h,H,Xwave,waveDen]; all_goals first | (norm_num [damping,h,H,Xwave,waveDen]; done) | rfl | decide) | (norm_num [damping,h,H,Xwave,waveDen]; done) | norm_num [damping,h,H,Xwave,waveDen])
  have hp := Real.pi_gt_three
  have hq := damping_pos q
  have hxpos := Xwave_pos hq t
  calc
    1 ≤ 3*damping q*Xwave (damping q) (5/6) := hl.le
    _ ≤ 3*damping q*Xwave (damping q) t := mul_le_mul_of_nonneg_left hx (by positivity)
    _ ≤ Real.pi*damping q*Xwave (damping q) t := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp.le hq.le) hxpos.le

lemma jetEnvelope_monotone {q v : Fin 2} {n : ℤ} (hn : 1≤n) (hQ : 0<Q n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t≤5/6) :
    jetEnvelope (damping q) (damping v) n s ≤jetEnvelope (damping q) (damping v) n t := by
  have ht0 : 0≤t := hs.trans hst
  have hx := Xwave_pos (damping_pos q) t
  have hxy := Xwave_antitone (damping_pos q) hs hst
  have hb := damping_Xwave_lower q ht0 ht
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hδ : 1≤(Real.pi*damping q*n)*Xwave (damping q) t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (le_of_lt hx),damping_pos q,Real.pi_pos]
  have hh := Envelope.sqrt_exp_antitone (a:=1+|D n|) (p:=Real.pi)
    (c:=(damping v)^2) (d:=4/3-2*damping q*damping v) hx hxy
    (by positivity) Real.pi_pos.le (sq_nonneg _) hδ
  have he (x : ℝ) : Real.exp (-Real.pi*(damping q*x-damping v)*n) =
      Real.exp (Real.pi*damping v*n)*Real.exp (-(Real.pi*damping q*n)*x) := by
    rw [←Real.exp_add]
    congr 1
    ring
  unfold jetEnvelope
  rw [he,he]
  convert! mul_le_mul_of_nonneg_left hh (show 0 ≤ Real.exp (Real.pi*damping v*n)/Q n from
    div_nonneg (Real.exp_pos _).le hQ.le) using 1 <;> first | (with_reducible_and_instances rfl) | ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma ri0_mem : (RI.point 0).Mem (0:ℝ) := by simpa using RI.mem_point 0
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_JetEnvelopeAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex
namespace AtomicTriangular.Construction
lemma normJetEnvelope_monotone {q v : Fin 2} {n : ℤ} (hn : 1≤n) (hQ : 0<Q n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 5 / 6) :
    normJetEnvelope (damping q) (damping v) n s≤normJetEnvelope (damping q) (damping v) n t := by
  rw [normJetEnvelope_eq (damping_pos q),normJetEnvelope_eq (damping_pos q)]
  exact jetEnvelope_monotone hn hQ hs hst ht
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_TailJetVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
lemma jetVector_norm_bound (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    ‖jetVector k v n t‖  ≤  normJetEnvelope k v n t := by
  rw [PiLp.norm_eq_of_L1]
  exact jetMultiplier_pair_bound k v t n hQ

lemma tailJetVector_bound (q v : Fin 2) (m n : ℤ) (hm : 1 ≤ m) (hQ : 0<Q m) (c : Fin 2) :
    ‖tailJetVector (damping q) (damping v) m n c‖  ≤ 
      ∑ i : Fin 15, normJetEnvelope (damping q) (damping v) m (frequency ⟨i.val+16,by omega⟩) * fullTailW i c := by
  have hh (i : Fin 15) (x : ℝ) (h1 : (i.val:ℝ)/18 ≤ |x|) (h2 : |x| ≤ (i.val+1:ℕ)/18) :
      ‖jetVector (damping q) (damping v) m x‖  ≤ 
      normJetEnvelope (damping q) (damping v) m (frequency ⟨i.val+16,by omega⟩) := by
    apply (jetVector_norm_bound _ _ _ _ hQ).trans
    rw [←normJetEnvelope_abs _ _ x m (damping_pos q),finiteEndpoint]
    apply normJetEnvelope_monotone hm hQ (abs_nonneg x) h2
    have hi : ((i.val+1:ℕ):ℝ) ≤ 15 := by exact_mod_cast (show i.val+1 ≤ 15 by omega)
    linarith
  fin_cases c
  · exact spectralCVector_bound n _ (continuous_jetVector (damping_pos q) _ _) _ hh
  · exact spectralDVector_bound n _ (continuous_jetVector (damping_pos q) _ _) _ hh
end AtomicTriangular.Construction
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
lemma envelopeExpC43_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 43))).exp.re=envelopeExpC43 j := by
  revert j
  decide +kernel
lemma envelopeExpC43_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 43))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC45_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 45))).exp.re=envelopeExpC45 j := by
  revert j
  decide +kernel
lemma envelopeExpC45_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 45))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC48_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 48))).exp.re=envelopeExpC48 j := by
  revert j
  decide +kernel
lemma envelopeExpC48_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 48))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC49_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 49))).exp.re=envelopeExpC49 j := by
  revert j
  decide +kernel
lemma envelopeExpC49_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 49))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC52_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 52))).exp.re=envelopeExpC52 j := by
  revert j
  decide +kernel
lemma envelopeExpC52_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 52))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC55_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 55))).exp.re=envelopeExpC55 j := by
  revert j
  decide +kernel
lemma envelopeExpC55_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 55))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC57_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 57))).exp.re=envelopeExpC57 j := by
  revert j
  decide +kernel
lemma envelopeExpC57_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 57))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
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
def psiTableD : Fin 15 → Fin 31 → RI := ![psiD36,psiD37,psiD39,psiD40,psiD43,psiD45,psiD48,psiD49,psiD52,psiD55,psiD57,psiD25,psiD27,psiD28,psiD31]
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
lemma finiteNode_Qpos (i : Fin 10) : 0<Q (finiteNode i) := by
  have hh := FiniteCertificate.Q_node_bounds _ (finiteNode_node i).2
  linarith [hh.1]
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
def targetExpInput (q : Fin 2) (n : ℤ) : RI :=
  ((targetRateBox q).mul (RI.point n)).add ((RI.point (1-n)).mul targetZBox.invPos)
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
lemma Ckernel_summable (i : Fin 20) : Summable (fun p => |Ckernel p i|) :=
  (tail_atom_column_bounds 1 0 _).1
end AtomicTriangular.Construction
end

end OAI
end


