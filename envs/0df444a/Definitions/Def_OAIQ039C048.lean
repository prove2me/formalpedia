-- Prove2me | Definitions.Def_OAIQ039C048
-- name    : OAIQ039C048
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:11:08.081003+00:00
-- url     : https://prove2.me/theorems/23a4df36-2ca3-4265-adbb-9352f27c6066
-- title:
--   Definitions bundle OAIQ039C048 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 3 definitions and 13 theorems. The definitions and types are `OAI.Kadison.LittleGrothendieck.sequenceLinear`, `OAI.Kadison.LittleGrothendieck.sequenceMap`, `OAI.Kadison.TracialGNS.zeroSpace`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_DyadicSpectral`, `Commutator_EndpointGNS`, `Commutator_LittleGrothendieckSequence`, `Commutator_ProjectionWeighted`, `Commutator_SelfAdjointSpectral`, `Commutator_SpectralCutoff`, `Commutator_SpectralStep`.
--
--   **Imports.** It imports the bundles `OAIQ039C030`, `OAIQ039C032`, `OAIQ039C035`, `OAIQ039C037` and `OAIQ039C038` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C057` and `OAIQ039C058`; the statement `OAI.Kadison.TracialGNS.word_multiplicity_both`; the proofs of `OAI.Kadison.AtomicFactor.Decomposition.finite_dimensional`, `OAI.Kadison.CentralAverage.exists_center_average`, `OAI.Kadison.ColumnModule.hom_column_sq`, `OAI.Kadison.FreeBlocks.sumConjugation_levelWord`, `OAI.Kadison.TracialGNS.word_multiplicity_both` and `OAI.Kadison.TracialSequence.projection_rep_lift`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C030
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C035
import Definitions.Def_OAIQ039C037
import Definitions.Def_OAIQ039C038

section
-- module Solutions.OAIQ039_CM.Commutator_SpectralCutoff
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma halfCut_mul_shift {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    halfCut T*(T+T-(1 : H →L[ℂ] H))=(T+T-(1 : H →L[ℂ] H))⁺ := by
  let b := T+T-(1 : H →L[ℂ] H)
  have hb : IsSelfAdjoint b := (hT.add hT).sub (IsSelfAdjoint.one _)
  change rightSupport b⁺*b=b⁺
  have hp : rightSupport b⁺*b⁺=b⁺ := by
    simpa only [CFC.abs_of_nonneg _ (CFC.posPart_nonneg b)] using initial_mul_abs b⁺
  have hn : rightSupport b⁺*b⁻=0 :=
    rightSupport_mul_eq_zero_of_nonneg (CFC.posPart_nonneg b) (CFC.posPart_mul_negPart b)
  nth_rw 2 [←CFC.posPart_sub_negPart b hb]
  rw [mul_sub,hp,hn,sub_zero]

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicSpectral
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology BigOperators

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma binaryRemainder_nonneg {T : H →L[ℂ] H} (hT : 0≤T) : 0≤binaryRemainder T := by
  let p := halfCut T
  have hp := isProjection_halfCut T
  have hc := halfCut_commute (IsSelfAdjoint.of_nonneg hT)
  have he : binaryRemainder T=(T+T-1)⁺+(1-p)*(T+T) := by
    rw [←halfCut_mul_shift (IsSelfAdjoint.of_nonneg hT)]
    change T+T-p=p*(T+T-1)+(1-p)*(T+T)
    noncomm_ring
  rw [he]
  exact add_nonneg (CFC.posPart_nonneg _) (Commute.mul_nonneg
    (sub_nonneg.mpr hp.le_one) (add_nonneg hT hT)
    (((Commute.one_left T).sub_left hc).add_right ((Commute.one_left T).sub_left hc)))

lemma binaryRemainder_le_one {T : H →L[ℂ] H} (hT : 0≤T) (hT1 : T≤1) :
    binaryRemainder T≤1 := by
  let b := T+T-1
  let p := halfCut T
  have hb : IsSelfAdjoint b := ((IsSelfAdjoint.of_nonneg hT).add
    (IsSelfAdjoint.of_nonneg hT)).sub (IsSelfAdjoint.one _)
  have hp := isProjection_halfCut T
  have hc := halfCut_commute (IsSelfAdjoint.of_nonneg hT)
  have hnb : b⁻=p*b-b := by
    rw [show p*b=b⁺ from halfCut_mul_shift (IsSelfAdjoint.of_nonneg hT)]
    calc
      b⁻=b⁺-(b⁺-b⁻) := by abel
      _=b⁺-b := by rw [CFC.posPart_sub_negPart b hb]
  have he : 1-binaryRemainder T=p*((1-T)+(1-T))+b⁻ := by
    rw [hnb]
    change 1-(T+T-p)=p*((1-T)+(1-T))+(p*(T+T-1)-(T+T-1))
    noncomm_ring
  apply sub_nonneg.mp
  rw [he]
  exact add_nonneg (Commute.mul_nonneg hp.nonneg (add_nonneg (sub_nonneg.mpr hT1)
    (sub_nonneg.mpr hT1)) ((Commute.one_right p).sub_right hc |>.add_right
      ((Commute.one_right p).sub_right hc))) (CFC.negPart_nonneg b)

lemma dyadicRemainder_bounds {T : H →L[ℂ] H} (hT : 0≤T) (hT1 : T≤1) (n : ℕ) :
    0≤dyadicRemainder T n ∧ dyadicRemainder T n≤1 := by
  induction n with
  | zero => exact ⟨hT,hT1⟩
  | succ n ih => exact ⟨binaryRemainder_nonneg ih.1,binaryRemainder_le_one ih.1 ih.2⟩

lemma dyadicStep_norm_error {T : H →L[ℂ] H} (hT : 0≤T) (hT1 : T≤1) (n : ℕ) :
    ‖T-dyadicStep T n‖≤(2:ℝ)⁻¹^n := by
  rw [dyadicStep_remainder,norm_smul,Real.norm_of_nonneg (by positivity)]
  have hb := dyadicRemainder_bounds hT hT1 n
  exact mul_le_of_le_one_right (by positivity) ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hb.1).mpr hb.2)

theorem exists_positive_spectral_sum (M : VonNeumannAlgebra H)
    {T : H →L[ℂ] H} (hTM : T∈M) (hT : 0≤T) (hT1 : T≤1) {ε : ℝ} (hε : 0<ε) :
    ∃ n : ℕ, ∃ p : Fin n → H →L[ℂ] H, ∃ c : Fin n → ℝ,
      (∀ i,p i∈M ∧ IsStarProjection (p i)) ∧
      (∀ i j,Commute (p i) (p j)) ∧ ‖T-∑ i,c i • p i‖<ε := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2:ℝ)⁻¹<1)
  refine ⟨n,fun i => halfCut (dyadicRemainder T i.val),fun i => (2:ℝ)⁻¹^(i.val+1),
    fun i => ⟨halfCut_mem M (dyadicRemainder_mem M hTM i.val),isProjection_halfCut _⟩,
    fun i j => dyadicCuts_commute (IsSelfAdjoint.of_nonneg hT) i.val j.val,?_⟩
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (2:ℝ)⁻¹^(i+1) • halfCut (dyadicRemainder T i))]
  exact (dyadicStep_norm_error hT hT1 n).trans_lt hn

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

abbrev zeroSpace : PreHilbert := ⟨centeredSpace (vacuum τ)⟩

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_LittleGrothendieckSequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter Set UniformSpace Completion

namespace Kadison.LittleGrothendieck

open HilbertSequence

variable {A E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def sequenceLinear (ω : Ultrafilter ℕ) (T : A →L[ℂ] E) :
    (ℕ →ᵇ A) →ₗ[ℂ] Pre ω E where
  toFun x := ⟨T.compLeftContinuousBounded ℕ x⟩
  map_add' x y := by
    apply (equiv ω E).injective
    exact map_add (T.compLeftContinuousBounded ℕ) x y
  map_smul' z x := by
    apply (equiv ω E).injective
    exact map_smul (T.compLeftContinuousBounded ℕ) z x

@[simp] lemma sequenceLinear_seq (ω : Ultrafilter ℕ) (T : A →L[ℂ] E)
    (x : ℕ →ᵇ A) (n : ℕ) : (sequenceLinear ω T x).seq n=T (x n) := rfl

lemma sequenceLinear_bound (ω : Ultrafilter ℕ) (T : A →L[ℂ] E) (x : ℕ →ᵇ A) :
    ‖sequenceLinear ω T x‖≤‖T‖*‖x‖ := by
  apply le_of_tendsto (tendsto_norm ω E (sequenceLinear ω T x))
  exact Filter.Eventually.of_forall (fun n => (T.le_opNorm (x n)).trans
    (mul_le_mul_of_nonneg_left (x.norm_coe_le_norm n) (norm_nonneg _)))

def sequenceMap (ω : Ultrafilter ℕ) (T : A →L[ℂ] E) :
    (ℕ →ᵇ A) →L[ℂ] Space ω E :=
  (toComplₗᵢ : Pre ω E →ₗᵢ[ℂ] Space ω E).toContinuousLinearMap.comp
    ((sequenceLinear ω T).mkContinuous ‖T‖ (sequenceLinear_bound ω T))

@[simp] lemma sequenceMap_apply (ω : Ultrafilter ℕ) (T : A →L[ℂ] E)
    (x : ℕ →ᵇ A) : sequenceMap ω T x=(sequenceLinear ω T x : Space ω E) := rfl

end Kadison.LittleGrothendieck

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionWeighted
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.SpectralPartition

variable {R : Type*} [Ring R] [StarRing R] [Module ℝ R]

theorem exists_weighted_partition (n : ℕ) (p : Fin n → R) (c : Fin n → ℝ)
    (hp : ∀ i,IsStarProjection (p i)) (hc : ∀ i j,Commute (p i) (p j)) :
    ∃ (J : Type) (_ : Fintype J) (e : J → R) (d : J → ℝ),
      (∀ j,IsStarProjection (e j)) ∧
      (∀ j k,j≠k → e j*e k=0) ∧ (∑ j,e j)=1 ∧
      (∑ i,c i • p i)=∑ j,d j • e j ∧
      (∀ a : R,(∀ i,Commute a (p i)) → ∀ j,Commute a (e j)) := by
  classical
  obtain ⟨J,hJ,e,he,ho,hs,hr,ha⟩ := exists_partition n p hp hc
  let : Fintype J := hJ
  choose χ hχ using hr
  refine ⟨J,hJ,e,(fun j => ∑ i,if χ i j then c i else 0),he,ho,hs,?_,ha⟩
  calc
    (∑ i,c i • p i)=∑ i,∑ j,if χ i j then c i • e j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hχ i,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hh : χ i j=true <;> simp [hh]
    _=∑ j,∑ i,if χ i j then c i • e j else 0 := Finset.sum_comm
    _=∑ j,(∑ i,if χ i j then c i else 0) • e j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hh : χ i j=true <;> simp [hh]

end Kadison.SpectralPartition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SelfAdjointSpectral
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_selfadjoint_spectral_sum (M : VonNeumannAlgebra H)
    {T : H →L[ℂ] H} (hTM : T∈M) (hT : IsSelfAdjoint T) {ε : ℝ} (hε : 0<ε) :
    ∃ n : ℕ, ∃ p : Fin n → H →L[ℂ] H, ∃ c : Fin n → ℝ,
      (∀ i,p i∈M ∧ IsStarProjection (p i)) ∧
      (∀ i j,Commute (p i) (p j)) ∧ ‖T-∑ i,c i • p i‖<ε := by
  classical
  let r : ℝ := 2*‖T‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  let S : H →L[ℂ] H := r⁻¹ • (T+‖T‖ • (1 : H →L[ℂ] H))
  have hh : ‖T‖ • (1 : H →L[ℂ] H)∈M :=
    (M.toSubalgebra.restrictScalars ℝ).smul_mem M.one_mem ‖T‖
  have hSM : S∈M :=
    (M.toSubalgebra.restrictScalars ℝ).smul_mem (M.add_mem hTM hh) r⁻¹
  have hb := normalized_positive_general hT
  obtain ⟨n,p,c,hp,hc,he⟩ := exists_positive_spectral_sum M hSM hb.1 hb.2 (div_pos hε hr)
  let q : Fin (n+1) → H →L[ℂ] H := Fin.cons 1 p
  let d : Fin (n+1) → ℝ := Fin.cons (-‖T‖) (fun i => r*c i)
  refine ⟨n+1,q,d,?_,?_,?_⟩
  · intro i
    refine Fin.cases ⟨M.one_mem,IsStarProjection.one _⟩ (fun j => hp j) i
  · intro i j
    refine Fin.cases (Commute.one_left _) (fun i => ?_) i
    exact Fin.cases (Commute.one_right _) (fun j => hc i j) j
  · have heq : T-∑ i,d i • q i=r • (S-∑ i,c i • p i) := by
      rw [Fin.sum_univ_succ]
      simp only [d,q,Fin.cons_zero,Fin.cons_succ,smul_sub,Finset.smul_sum,smul_smul]
      have hid : r • S=T+‖T‖ • (1 : H →L[ℂ] H) := by
        dsimp [S]; rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
      rw [hid]
      module
    rw [heq,norm_smul,Real.norm_of_nonneg hr.le]
    exact (mul_lt_mul_of_pos_left he hr).trans_eq (mul_div_cancel₀ ε hr.ne')

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SpectralStep
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.SpectralPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_spectral_step (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hTM : T∈M) (hT : IsSelfAdjoint T) {ε : ℝ} (hε : 0<ε) :
    ∃ (J : Type) (_ : Fintype J) (p : J → H →L[ℂ] H) (c : J → ℝ),
      (∀ j,p j∈M ∧ IsStarProjection (p j)) ∧
      (∀ j k,j≠k → p j*p k=0) ∧ (∑ j,p j)=1 ∧
      ‖T-∑ j,c j • p j‖<ε := by
  classical
  obtain ⟨n,p,c,hp,hc,he⟩ := Polar.exists_selfadjoint_spectral_sum M hTM hT hε
  obtain ⟨J,hJ,e,d,hproj,horth,hsum,heq,hcomm⟩ := exists_weighted_partition n p c
    (fun i => (hp i).2) hc
  let : Fintype J := hJ
  refine ⟨J,hJ,e,d,?_,horth,hsum,?_⟩
  · intro j
    refine ⟨?_,hproj j⟩
    change e j∈M.toStarSubalgebra.carrier
    rw [←M.centralizer_centralizer']
    intro a ha
    exact (hcomm a (fun i => (ha (p i) (hp i).1).symm) j).eq
  · rwa [←heq]

theorem exists_spectral_step_subtype (M : VonNeumannAlgebra H) (T : M)
    (hT : IsSelfAdjoint T) {ε : ℝ} (hε : 0<ε) :
    ∃ (J : Type) (_ : Fintype J) (p : J → M) (c : J → ℝ),
      (∀ j,IsStarProjection (p j)) ∧
      (∀ j k,j≠k → p j*p k=0) ∧ (∑ j,p j)=1 ∧
      ‖T-∑ j,(c j:ℂ) • p j‖<ε := by
  classical
  obtain ⟨J,hJ,p,c,hp,ho,hs,he⟩ := exists_spectral_step M T T.property
    (hT.map M.toStarSubalgebra.subtype) hε
  let : Fintype J := hJ
  let q : J → M := fun j => ⟨p j,(hp j).1⟩
  refine ⟨J,hJ,q,c,?_,?_,?_,?_⟩
  · intro j
    constructor
    · exact Subtype.ext (hp j).2.isIdempotentElem.eq
    · exact Subtype.ext (hp j).2.isSelfAdjoint.star_eq
  · intro j k hjk
    exact Subtype.ext (ho j k hjk)
  · apply Subtype.ext
    change M.toStarSubalgebra.subtype (∑ j,q j)=M.toStarSubalgebra.subtype 1
    rw [map_sum,map_one]
    exact hs
  · change ‖(T : H →L[ℂ] H)-((∑ j,(c j:ℂ) • q j : M) : H →L[ℂ] H)‖<ε
    change ‖(T : H →L[ℂ] H)-M.toStarSubalgebra.subtype (∑ j,(c j:ℂ) • q j)‖<ε
    simp only [map_sum,Complex.coe_smul]
    exact he

end Kadison.SpectralPartition

end

end
end

end OAI
end


