-- Prove2me | Definitions.Def_OAIQ067A002
-- name    : OAIQ067A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:22:46.157687+00:00
-- url     : https://prove2.me/theorems/481f0e13-b1b6-4ef5-8fb7-14e495f4d49c
-- title:
--   Definitions bundle OAIQ067A002 of the split of OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 279 declarations of OpenAI's Lean: 156 definitions, 2 inductive types or structures, 3 instances and 118 theorems. The definitions and types are `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.boltzmannAtom`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.edgeExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.messageExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.siteExpression`, `OAI.FixedClauseThreshold.Computability.SingleIncident`, `OAI.FixedClauseThreshold.Computability.TrialEvaluation`, `OAI.FixedClauseThreshold.Computability.TrialEvaluation.certified`, `OAI.FixedClauseThreshold.Computability.TrialEvaluation.upper`, `OAI.FixedClauseThreshold.Computability.TrialSeparation`, `OAI.FixedClauseThreshold.Computability.TripleClasses`, `OAI.FixedClauseThreshold.Computability.activeClass`, `OAI.FixedClauseThreshold.Computability.activeMask`, `OAI.FixedClauseThreshold.Computability.auxiliaryPoissonProbability`, `OAI.FixedClauseThreshold.Computability.averagedEdgeExpression`, `OAI.FixedClauseThreshold.Computability.averagedSiteExpression`, `OAI.FixedClauseThreshold.Computability.baseMask`, `OAI.FixedClauseThreshold.Computability.batchKillProbability`, `OAI.FixedClauseThreshold.Computability.batchKills`, `OAI.FixedClauseThreshold.Computability.branchEntry`, `OAI.FixedClauseThreshold.Computability.branchWeights`, `OAI.FixedClauseThreshold.Computability.candidateAlive`, `OAI.FixedClauseThreshold.Computability.candidateBlock`, `OAI.FixedClauseThreshold.Computability.candidateFixedBlock`, `OAI.FixedClauseThreshold.Computability.candidatePermutation`, `OAI.FixedClauseThreshold.Computability.candidateResidual`, `OAI.FixedClauseThreshold.Computability.candidateStep`, `OAI.FixedClauseThreshold.Computability.certificateProgram`, `OAI.FixedClauseThreshold.Computability.certificateTest`, `OAI.FixedClauseThreshold.Computability.chooseChildren`, `OAI.FixedClauseThreshold.Computability.classBaseMask`, `OAI.FixedClauseThreshold.Computability.classClause`, `OAI.FixedClauseThreshold.Computability.classIncidentMask`, `OAI.FixedClauseThreshold.Computability.clauseClassesEquiv`, `OAI.FixedClauseThreshold.Computability.clauseMask`, `OAI.FixedClauseThreshold.Computability.clausePermutation`, `OAI.FixedClauseThreshold.Computability.compiledTrialsRatPrimcodable`, `OAI.FixedClauseThreshold.Computability.decodeTree`, `OAI.FixedClauseThreshold.Computability.decodeTrial`, `OAI.FixedClauseThreshold.Computability.deletedVariables`, `OAI.FixedClauseThreshold.Computability.deletionBudgetMask` and 118 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `PeriodicLattice_Arithmetic`, `PeriodicLattice_EffectiveReals`, `RandomSAT_CenterBounds`, `RandomSAT_ClauseProcess`, `RandomSAT_Clauses`, `RandomSAT_FiniteMean`, `RandomSAT_Forcing`, `RandomSAT_Interpolation`, `RandomSAT_Main`, `RandomSAT_Replacement`, `RandomSAT_Variance`, `RapidForcing_ArithmeticAutomation`, `RapidForcing_BoundsPrograms`, `RapidForcing_FormulaPrograms`, `RapidForcing_RatPrimrec`, `RapidForcing_RawMachine`, `SATComputability_ActiveClauses`, `SATComputability_ActiveProcess`, `SATComputability_ActualFreeMoment`, `SATComputability_ArithmeticSyntax`, `SATComputability_AuxiliaryEnergy`, `SATComputability_BatchKilling`, `SATComputability_CandidateEncoding`, `SATComputability_CandidateMasks`, `SATComputability_CandidateProcess`, `SATComputability_CandidateSurvival`, `SATComputability_CavityExpressions`, `SATComputability_CertificateSearch`, `SATComputability_ClassMasks`, `SATComputability_ClauseClasses`, `SATComputability_ClauseProcess`, `SATComputability_ClauseRestoration`, `SATComputability_CompiledTrials`, `SATComputability_DeletionEnergy`, `SATComputability_DisorderEnumeration`, `SATComputability_DyadicBlocks`, `SATComputability_DyadicMoment`, `SATComputability_EffectiveSums`, `SATComputability_EffectiveTrialValues`, `SATComputability_FiniteEnumeration`, `SATComputability_FiniteTrialEvaluation`, `SATComputability_HierarchyBounds`, `SATComputability_HierarchyEncoding`, `SATComputability_HierarchyEvaluator`, `SATComputability_HierarchyExpectation`, `SATComputability_HierarchyProgram`, `SATComputability_HierarchySemantics`, `SATComputability_HierarchyTable`, `SATComputability_IncidentMasks`, `SATComputability_IncidentObstruction`, `SATComputability_LowerBounds`, `SATComputability_LowerProgram`, `SATComputability_MaskDelay`, `SATComputability_MaskDeletionTimes`, `SATComputability_MaskLifetime`, `SATComputability_MaskPermutations`, `SATComputability_ObstructionMoment`, `SATComputability_PacketExpressions`, `SATComputability_PhysicalExpressions`, `SATComputability_PoissonEvaluation`, `SATComputability_PoissonKernel`, `SATComputability_PoissonKilling`, `SATComputability_PoissonSATProbability`, `SATComputability_PoissonSemigroup`, `SATComputability_RelaxedCandidates`, `SATComputability_RestoredCandidates`, `SATComputability_RestoredProcessMoment`, `SATComputability_SupercriticalEnergy`, `SATComputability_TrialDescriptions`, `SATComputability_TrialDisorder`, `SATComputability_UpperCertificates`.
--
--   **Imports.** It imports the published bundles `Def_DilutedSpin`, `Def_OAIQ041D000` and `Def_SATComputability`; the bundles `OAIQ067A000` and `OAIQ067A001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ067A003` and `OAIQ067A004`; the statements `OAI.FixedClauseThreshold.Computability.auxiliaryPoissonProbability_supercritical_sat`, `OAI_FixedClauseThreshold_Computability_deletion_increment_linear`, `OAI.FixedClauseThreshold.Computability.deletion_increment_linear_sat`, `OAI.FixedClauseThreshold.Computability.exists_lowerProgram_sat`, `OAI_FixedClauseThreshold_Computability_negative_pressure_of_violation_density`, `OAI.FixedClauseThreshold.Computability.negative_pressure_of_violation_density_sat`, `OAI_FixedClauseThreshold_Computability_relaxedPoissonMinimum_subcritical`, `OAI.FixedClauseThreshold.Computability.relaxedPoissonMinimum_subcritical_sat`, `OAI_FixedClauseThreshold_Computability_restored_process_moment`, `OAI.FixedClauseThreshold.Computability.restored_process_moment_sat`, `OAI_FixedClauseThreshold_Computability_satTrialEvaluation_sound`, `OAI.FixedClauseThreshold.Computability.satTrialEvaluation_sound_sat`, `OAI.FixedClauseThreshold.Computability.threshold_program_sat`, `OAI_FixedClauseThreshold_auxiliaryProbability_center_lower`, `OAI.FixedClauseThreshold.auxiliaryProbability_center_lower_sat`, `OAI_FixedClauseThreshold_center_lower_of_auxiliary_probability`, `OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability_sat`, `OAI.FixedClauseThreshold.limitingCenter_bounds_sat`, `OAI_FixedClauseThreshold_limitingCenter_lt_cap`, `OAI.FixedClauseThreshold.limitingCenter_lt_cap_sat`, `OAI.FixedClauseThreshold.limitingCenter_pos_sat` and `OAI.FixedClauseThreshold.subcritical_limit_sat`; the proofs of `OAI.FixedClauseThreshold.Computability.auxiliaryPoissonProbability_supercritical_sat`, `OAI_FixedClauseThreshold_Computability_deletion_increment_linear`, `OAI.FixedClauseThreshold.Computability.deletion_increment_linear_sat`, `OAI_FixedClauseThreshold_Computability_exists_lowerProgram`, `OAI.FixedClauseThreshold.Computability.exists_lowerProgram_sat`, `OAI.FixedClauseThreshold.Computability.main`, `OAI_FixedClauseThreshold_Computability_negative_pressure_of_violation_density`, `OAI.FixedClauseThreshold.Computability.negative_pressure_of_violation_density_sat`, `OAI_FixedClauseThreshold_Computability_relaxedPoissonMinimum_subcritical`, `OAI.FixedClauseThreshold.Computability.relaxedPoissonMinimum_subcritical_sat`, `OAI_FixedClauseThreshold_Computability_restored_process_moment`, `OAI.FixedClauseThreshold.Computability.restored_process_moment_sat`, `OAI_FixedClauseThreshold_Computability_satTrialEvaluation_sound`, `OAI.FixedClauseThreshold.Computability.satTrialEvaluation_sound_sat`, `OAI_FixedClauseThreshold_Computability_threshold_program`, `OAI.FixedClauseThreshold.Computability.threshold_program_sat`, `OAI_FixedClauseThreshold_auxiliaryProbability_center_lower`, `OAI.FixedClauseThreshold.auxiliaryProbability_center_lower_sat`, `OAI_FixedClauseThreshold_center_lower_of_auxiliary_probability`, `OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability_sat`, `OAI.FixedClauseThreshold.limitingCenter_bounds_sat`, `OAI_FixedClauseThreshold_limitingCenter_lt_cap`, `OAI.FixedClauseThreshold.limitingCenter_lt_cap_sat`, `OAI.FixedClauseThreshold.limitingCenter_pos_sat`, `OAI.FixedClauseThreshold.properSATProbability_center_lower_sat`, `OAI.FixedClauseThreshold.properSATProbability_center_upper_sat` and `OAI.FixedClauseThreshold.subcritical_limit_sat`.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_SATComputability
import Definitions.Def_OAIQ067A000
import Definitions.Def_OAIQ067A001

section
-- module Solutions.OAIQ067_SAT.PeriodicLattice_Arithmetic
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recursive arithmetic and effective profile syntax. -/

namespace PeriodicLattice

noncomputable section

attribute [fun_prop] Primrec
attribute [fun_prop] Primrec.id Primrec.const Primrec.comp Primrec.pair Primrec.fst Primrec.snd
attribute [fun_prop] RecursiveArithmetic.intOfNat RecursiveArithmetic.intNatAbs
attribute [fun_prop] RecursiveArithmetic.intNeg RecursiveArithmetic.factorial
namespace RecursiveArithmetic
@[fun_prop] theorem int_sub : Primrec (fun p : ℤ × ℤ => p.1 - p.2) := intSub

end RecursiveArithmetic

namespace RecursiveArithmetic

@[fun_prop] theorem ofDigits : Primrec (fun p : ℕ × List ℕ => Nat.ofDigits p.1 p.2) := by
  have hg : Primrec (fun p : (ℕ × List ℕ) × ℕ × ℕ => p.2.1 + p.1.1 * p.2.2) := by fun_prop
  exact (Primrec.list_foldr Primrec.snd (Primrec.const 0) hg.to₂).of_eq
    (fun p => by dsimp only; induction p.2 <;> simp_all [Nat.ofDigits])

end RecursiveArithmetic

end
end PeriodicLattice

end OAI
end

section
-- module Solutions.OAIQ067_SAT.PeriodicLattice_EffectiveReals
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Well-formed input encodings and effective real enclosures. -/

namespace PeriodicLattice

noncomputable section

namespace CertifiedReal
open Encodable Filter Topology

section
variable {A B : Type*} [Primcodable A] [Primcodable B]

attribute [local instance] OAI.PeriodicLattice.CertifiedReal.effectiveRealsLocal2
theorem Effective.comp {f : B → ℝ} (hf : Effective f) {g : A → B} (hg : Computable g) :
    Effective (fun a => f (g a)) := by
  obtain ⟨q,hq,he⟩ := hf
  exact ⟨fun an => q (g an.1,an.2), hq.comp ((hg.comp Computable.fst).pair Computable.snd),
    fun a n => he (g a) n⟩

theorem Effective.congr {f g : A → ℝ} (hf : Effective f) (h : ∀ a, f a = g a) : Effective g := by
  simpa only [funext h] using hf

end
end CertifiedReal

attribute [fun_prop] Computable
attribute [fun_prop] Computable.id Computable.const Computable.comp Computable.pair Computable.fst Computable.snd
attribute [fun_prop] Primrec.to_comp

namespace CertifiedReal
open Encodable Filter Topology
local instance effectiveRealsLocal3 : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable
section
variable {A B : Type*} [Primcodable A] [Primcodable B]

theorem Effective.add {f g : A → ℝ} (hf : Effective f) (hg : Effective g) :
    Effective (fun a => f a + g a) := by
  obtain ⟨q,hq,bq⟩ := hf
  obtain ⟨v,hv,bv⟩ := hg
  refine of_enclosures (q := fun an => q an + v an) (e := fun an => 2 * qerror an.2)
    (by fun_prop) (by fun_prop) ?_ ?_
  · intro a n
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, cast_qerror, two_mul, sub_add_sub_comm] using
      abs_add_le (f a - (q (a,n) : ℝ)) (g a - (v (a,n) : ℝ)) |>.trans (add_le_add (bq a n) (bv a n))
  · intro a
    simpa using error_tendsto.const_mul 2

theorem Effective.neg {f : A → ℝ} (hf : Effective f) : Effective (fun a => -f a) := by
  obtain ⟨q,hq,bq⟩ := hf
  refine ⟨fun an => -q an, by fun_prop, fun a n => ?_⟩
  rw [Rat.cast_neg, show -f a - -(q (a,n) : ℝ) = -(f a - (q (a,n) : ℝ)) by ring, abs_neg]
  exact bq a n

theorem Effective.sub {f g : A → ℝ} (hf : Effective f) (hg : Effective g) :
    Effective (fun a => f a - g a) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem Effective.mul {f g : A → ℝ} (hf : Effective f) (hg : Effective g) :
    Effective (fun a => f a * g a) := by
  obtain ⟨q,hq,bq⟩ := hf
  obtain ⟨v,hv,bv⟩ := hg
  refine of_enclosures (q := fun an => q an * v an)
    (e := fun an => qerror an.2 * (|q an| + |v an| + qerror an.2))
    (by fun_prop) (by fun_prop) ?_ ?_
  · intro a n
    simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_abs, cast_qerror]
    have bg : |g a| ≤ |(v (a,n) : ℝ)| + error n := by
      have := abs_add_le (g a - (v (a,n) : ℝ)) (v (a,n) : ℝ)
      have := this.trans (add_le_add (bv a n) le_rfl)
      rw [sub_add_cancel] at this
      exact this.trans_eq (add_comm _ _)
    calc
      |f a * g a - (q (a,n) : ℝ) * (v (a,n) : ℝ)| =
        |(f a - q (a,n)) * g a + (q (a,n) : ℝ) * (g a - v (a,n))| := by congr 1; ring
      _ ≤ |f a - (q (a,n) : ℝ)| * |g a| + |(q (a,n) : ℝ)| * |g a - (v (a,n) : ℝ)| := by
        simpa only [abs_mul] using abs_add_le ((f a - q (a,n)) * g a) ((q (a,n) : ℝ) * (g a - v (a,n)))
      _ ≤ error n * (|(v (a,n) : ℝ)| + error n) + |(q (a,n) : ℝ)| * error n := by
        exact add_le_add (mul_le_mul (bq a n) bg (abs_nonneg _) (error_pos n).le)
          (mul_le_mul_of_nonneg_left (bv a n) (abs_nonneg _))
      _ = _ := by ring
  · intro a
    have hqa := Effective.approximants_tendsto bq a
    have hva := Effective.approximants_tendsto bv a
    simpa using error_tendsto.mul ((hqa.abs.add hva.abs).add error_tendsto)

end
end CertifiedReal

end
end PeriodicLattice

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Clauses
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Signed variable sets, clause cardinalities, and the exact probability of killing
a nonempty solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem kills_iff {n k : ℕ} (S : Finset (Assignment n)) (σ₀ : Assignment n)
    (hσ₀ : σ₀ ∈ S) (C : ProperClause n k) :
    KillsSolutions S C ↔
      clauseSupport C ⊆ frozenCoordinates S σ₀ ∧
      ∀ i ∈ clauseSupport C, C.val i = some (!(σ₀ i)) := by
  constructor
  · intro h
    have hop (σ : Assignment n) (hσ : σ ∈ S) (i : Fin n)
        (hi : i ∈ clauseSupport C) : C.val i = some (!(σ i)) := by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((mem_clauseSupport C i).mp hi)
      have hne : b ≠ σ i := by
        intro heq
        exact h σ hσ ⟨i, hb.trans (congrArg some heq)⟩
      cases hb' : b <;> cases hv : σ i <;> simp_all
    refine ⟨?_, hop σ₀ hσ₀⟩
    intro i hi
    simp only [frozenCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
    intro σ hσ
    have heq := (hop σ hσ i hi).symm.trans (hop σ₀ hσ₀ i hi)
    simpa using heq
  · rintro ⟨hsub, hsign⟩ σ hσ ⟨i, hi⟩
    have his : i ∈ clauseSupport C := by
      rw [mem_clauseSupport, hi]
      rfl
    have hf : σ i = σ₀ i := by
      have hf := hsub his
      simp only [frozenCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact hf σ hσ
    have heq := hi.symm.trans (hsign i his)
    cases hv : σ₀ i <;> simp_all

def killingClauseEquiv {n k : ℕ} (S : Finset (Assignment n)) (σ₀ : Assignment n)
    (hσ₀ : σ₀ ∈ S) :
    {C : ProperClause n k // KillsSolutions S C} ≃
      ↥((frozenCoordinates S σ₀).powersetCard k) where
  toFun C := ⟨clauseSupport C.val, Finset.mem_powersetCard.mpr
    ⟨((kills_iff S σ₀ hσ₀ C.val).mp C.property).1, clauseSupport_card C.val⟩⟩
  invFun s := ⟨opposingClause σ₀ ⟨s.val, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp s.property).2⟩⟩, by
    apply (kills_iff S σ₀ hσ₀ _).mpr
    simp only [support_opposingClause]
    refine ⟨(Finset.mem_powersetCard.mp s.property).1, ?_⟩
    intro i hi
    simp [opposingClause, clauseFromSigns, hi]⟩
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (if i ∈ clauseSupport C.val then some (!(σ₀ i)) else none) = C.val.val i
    by_cases hi : i ∈ clauseSupport C.val
    · rw [ite_eq_left hi]
      exact (((kills_iff S σ₀ hσ₀ C.val).mp C.property).2 i hi).symm
    · rw [ite_eq_right hi]
      apply Eq.symm
      apply Option.not_isSome_iff_eq_none.mp
      simpa only [mem_clauseSupport] using hi
  right_inv s := by
    apply Subtype.ext
    exact support_opposingClause _ _

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Replacement
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Quantitative comparison of a shorter clause with a block of independent proper
clauses, uniformly over the background solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def blockUNSATProbability {n : ℕ} (k g : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformProbability (fun F : Formula n k g =>
    ¬ ∃ σ ∈ S, Satisfies σ F)

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_FiniteMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def uniformVariance {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  uniformMean (fun a => (f a - uniformMean f)^2)

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_ClauseProcess
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def clauseHeadSplit {v k : ℕ} (hk : 0 < k) (C : ProperClause (v + 1) k) :
    ProperClause v k ⊕ (ProperClause v (k - 1) × Bool) :=
  match hb : C.val 0 with
  | none => Sum.inl ⟨Fin.tail C.val, by
      have h := C.property
      conv_lhs at h => rw [← Fin.cons_self_tail C.val]
      rw [support_card_cons, hb] at h
      simpa using h⟩
  | some b => Sum.inr (⟨Fin.tail C.val, by
      have h := C.property
      conv_lhs at h => rw [← Fin.cons_self_tail C.val]
      rw [support_card_cons, hb] at h
      simp at h
      omega⟩, b)

def clauseHeadEquiv {v k : ℕ} (hk : 0 < k) :
    ProperClause (v + 1) k ≃ ProperClause v k ⊕ (ProperClause v (k - 1) × Bool) where
  toFun := clauseHeadSplit hk
  invFun := Sum.elim prependAbsent (fun p => prependPresent hk p.1 p.2)
  left_inv C := by
    apply Subtype.ext
    simp only [clauseHeadSplit]
    split <;> simp only [Sum.elim_inl, Sum.elim_inr, prependAbsent, prependPresent]
    all_goals simpa only [*] using Fin.cons_self_tail C.val
  right_inv C := by
    cases C with
    | inl C => rfl
    | inr C =>
      rcases C with ⟨C, b⟩
      rfl

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Forcing
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Deletion and erasure of a coordinate, permutation symmetry, and the integrated
forcing bound.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def deletedMean {v k : ℕ} (hk : 0 < k) (m : ℕ) (S : Finset (Assignment v)) : ℝ :=
  uniformMean (fun F : Formula (v + 1) k m =>
    alive (deletedSolutions S (fun i => clauseHeadSplit hk (F i))))

def erasedMean {v k : ℕ} (hk : 0 < k) (m : ℕ) (S : Finset (Assignment v)) : ℝ :=
  uniformMean (fun F : Formula (v + 1) k m =>
    alive (erasedSolutions S (fun i => clauseHeadSplit hk (F i))))

def headForcedMean (v k m : ℕ) : ℝ :=
  uniformMean (fun F : Formula (v + 1) k m =>
    if (0 : Fin (v + 1)) ∈ forcedVariables (restrictSolutions Finset.univ F)
      then (1 : ℝ) else 0)

def renameClause {n k : ℕ} (e : Fin n ≃ Fin n) (C : ProperClause n k) : ProperClause n k :=
  ⟨fun i => C.val (e i), by
    have h := Fintype.card_congr
      (e.subtypeEquivOfSubtype (p := fun i => (C.val i).isSome))
    simp only [Fintype.card_subtype] at h
    exact h.trans C.property⟩

def renameClauseEquiv {n k : ℕ} (e : Fin n ≃ Fin n) : ProperClause n k ≃ ProperClause n k where
  toFun := renameClause e
  invFun := renameClause e.symm
  left_inv C := by apply Subtype.ext; funext i; simp [renameClause]
  right_inv C := by apply Subtype.ext; funext i; simp [renameClause]

def renameAssignment {n : ℕ} (e : Fin n ≃ Fin n) (σ : Assignment n) : Assignment n :=
  fun i => σ (e i)

def renameFormula {n k m : ℕ} (e : Fin n ≃ Fin n) (F : Formula n k m) : Formula n k m :=
  fun i => renameClause e (F i)

def renameFormulaEquiv {n k m : ℕ} (e : Fin n ≃ Fin n) : Formula n k m ≃ Formula n k m :=
  Equiv.piCongrRight (fun _ => renameClauseEquiv e)

def forcedFractionMean (n k m : ℕ) : ℝ :=
  uniformMean (fun F : Formula n k m =>
    ((forcedVariables (restrictSolutions Finset.univ F)).card : ℝ) / n)

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Variance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Stopped satisfiable lifetimes, insertion delays, and the coordinate-omission
variance bound in terms of integrated forcing.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def lifetimeVariance {n : ℕ} (k m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformVariance (lifetime k m S)

def killingChance {n : ℕ} (k : ℕ) (S : Finset (Assignment n)) : ℝ :=
  alive S - survival k 1 S

def insertionDelay {n : ℕ} (k m : ℕ) (S : Finset (Assignment n))
    (C : ProperClause n k) (F : Formula n k m) : ℝ :=
  (alive S + lifetime k m S F) - (alive (addClause S C) + lifetime k m (addClause S C) F)

def insertionSecond {n : ℕ} (k m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformMean (fun C : ProperClause n k => uniformMean (fun F : Formula n k m =>
    insertionDelay k m S C F ^ 2))

def truncatedKilling {n : ℕ} (k M : ℕ) (S : Finset (Assignment n)) : ℝ :=
  min ((M : ℝ) * killingChance k S) 1

def occupation {n : ℕ} (k : ℕ) (f : Finset (Assignment n) → ℝ) :
    ℕ → Finset (Assignment n) → ℝ
  | 0, _ => 0
  | m + 1, S => f S + clauseAverage k (occupation k f m) S

def forcedFraction {n : ℕ} (S : Finset (Assignment n)) : ℝ :=
  ((forcedVariables S).card : ℝ) / n

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_CenterBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite union bounds, a matching criterion for satisfiability, and positive finite
bounds for the normalized centers.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

@[simp] theorem forcedVariables_singleton {n : ℕ} (σ : Assignment n) :
    forcedVariables ({σ} : Finset (Assignment n)) = Finset.univ := by
  ext i
  simp [forcedVariables]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Interpolation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Auxiliary ordered clauses allow repeated variables. Commuting finite averaging
operators give the fixed-count partition interpolation corresponding to the
marked-Poisson comparison.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def auxiliarySatisfies {n k : ℕ} (σ : Assignment n) (C : AuxiliaryClause n k) : Prop :=
  ∃ j, σ (C j).1 = (C j).2

def finiteClauseAverage {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) : ℝ := uniformMean (fun c => f (S.filter (sat c)))

def embedAuxiliaryClause {n v k : ℕ} (e : Fin v → Fin n) (C : AuxiliaryClause v k) :
    AuxiliaryClause n k := fun j => (e (C j).1, (C j).2)

def embeddedAverage {n v : ℕ} (e : Fin v → Fin n) (k : ℕ) :
    (Finset (Assignment n) → ℝ) → (Finset (Assignment n) → ℝ) :=
  finiteClauseAverage (fun C : AuxiliaryClause v k => fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C))

def auxiliaryAverage {n : ℕ} (k : ℕ) :
    (Finset (Assignment n) → ℝ) → (Finset (Assignment n) → ℝ) :=
  embeddedAverage (id : Fin n → Fin n) k

def auxiliarySurvival {n : ℕ} (k m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  ((auxiliaryAverage k)^[m] alive) S

def auxiliaryProbability (n k m : ℕ) : ℝ :=
  auxiliarySurvival k m (Finset.univ : Finset (Assignment n))

def embeddedForced {n v : ℕ} (S : Finset (Assignment n)) (e : Fin v → Fin n) : Finset (Fin v) :=
  Finset.univ.filter (fun i => e i ∈ forcedVariables S)

@[simp] theorem mem_embeddedForced {n v : ℕ} (S : Finset (Assignment n)) (e : Fin v → Fin n) (i : Fin v) :
    i ∈ embeddedForced S e ↔ e i ∈ forcedVariables S := by simp [embeddedForced]

@[simp] theorem embeddedForced_id {n : ℕ} (S : Finset (Assignment n)) :
    embeddedForced S (id : Fin n → Fin n) = forcedVariables S := by ext i; simp

def blockSet {r s : ℕ} (S : Finset (Assignment r)) (T : Finset (Assignment s)) :
    Finset (Assignment (r + s)) :=
  Finset.univ.filter (fun σ => (fun i => σ (Fin.castAdd s i)) ∈ S ∧
    (fun i => σ (Fin.natAdd r i)) ∈ T)

@[simp] theorem mem_blockSet {r s : ℕ} (S : Finset (Assignment r)) (T : Finset (Assignment s))
    (σ : Assignment (r + s)) : σ ∈ blockSet S T ↔
      (fun i => σ (Fin.castAdd s i)) ∈ S ∧ (fun i => σ (Fin.natAdd r i)) ∈ T := by
  simp [blockSet]

@[simp] theorem blockSet_univ (r s : ℕ) :
    blockSet (Finset.univ : Finset (Assignment r)) (Finset.univ : Finset (Assignment s)) =
      Finset.univ := by ext σ; simp

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Main
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
For every fixed clause size at least three, the proper-clause satisfiability
probability has a positive finite limiting threshold. No conclusion is asserted
at the critical density.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def limitingCenter (k : ℕ) : ℝ := Filter.limsup (fun n : ℕ => center n k) Filter.atTop

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_ArithmeticAutomation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Encodable Denumerable
namespace RapidForcing.EffectiveArithmetic

attribute [fun_prop] Primrec PrimrecPred Computable
attribute [fun_prop] Primrec.id Primrec.const Primrec.comp Primrec.fst Primrec.snd
  Primrec.pair Primrec.encode Primrec.decode Primrec.option_some Primrec.unpair
  Primrec.succ Primrec.pred Primrec.ite PrimrecPred.comp PrimrecPred.not PrimrecPred.and
  PrimrecPred.or Computable.id Computable.const Computable.comp Computable.fst Computable.snd
  Computable.pair Computable.encode Computable.decode Computable.option_some
attribute [fun_prop] primrec_int_ofNat primrec_int_negSucc primrec_int_natAbs
  primrec_int_toNat primrec_int_neg

@[fun_prop] lemma primrec_nat_pow : Primrec (fun p : ℕ × ℕ => p.1 ^ p.2) := by
  have h := Primrec.nat_rec' (f := fun p : ℕ × ℕ => p.2)
    (g := fun _ => 1) (h := fun p r => r.2 * p.1)
    (by fun_prop) (by fun_prop) (by unfold Primrec₂; fun_prop)
  apply h.of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih => simp only [pow_succ, ih]

@[fun_prop] lemma primrec_int_lt : PrimrecPred (fun p : ℤ × ℤ => p.1 < p.2) := by
  exact (PrimrecPred.not (primrec_int_le.comp (Primrec.snd.pair Primrec.fst))).of_eq
    (fun p => not_le)

end RapidForcing.EffectiveArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_RatPrimrec
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Encodable Denumerable
namespace RapidForcing.EffectiveArithmetic

@[fun_prop] lemma primrec_nat_coprime : PrimrecPred (fun p : ℕ × ℕ => p.1.Coprime p.2) := by
  simpa only [Nat.Coprime] using
    (Primrec.eq.comp primrec_nat_gcd (Primrec.const 1))

end RapidForcing.EffectiveArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_RawMachine
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Encodable
open scoped BigOperators
namespace RapidForcing
open EffectiveArithmetic
@[fun_prop] lemma compPred_nat_lt : CompPred (fun p : ℕ × ℕ => p.1 < p.2) := Primrec.nat_lt.decide.to_comp
@[fun_prop] lemma compPred_nat_le : CompPred (fun p : ℕ × ℕ => p.1 ≤ p.2) := Primrec.nat_le.decide.to_comp

end RapidForcing

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_FormulaPrograms
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Encodable Nat.Partrec
open scoped BigOperators
namespace RapidForcing.EffectiveArithmetic

@[fun_prop] lemma computable_rat_min : Computable (fun p : ℚ × ℚ => min p.1 p.2) := by
  simpa only [min_def] using (show Computable (fun p : ℚ × ℚ => if p.1 ≤ p.2 then p.1 else p.2) by fun_prop)

end RapidForcing.EffectiveArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_BoundsPrograms
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Encodable
open scoped BigOperators
namespace RapidForcing.EffectiveArithmetic

lemma computable_list_flatMap {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    {f : A → List B} {g : A → B → List C} (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).flatMap (g a)) := by
  have h := computable_list_foldr hf (Computable.const ([] : List C))
    (h := fun a p => g a p.1 ++ p.2)
    ((Primrec.list_append.to_comp.comp (hg.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂)
  exact h.of_eq (fun a => by induction f a <;> simp [*])
end RapidForcing.EffectiveArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RelaxedCandidates
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

def literalFalse {n : ℕ} (x : DeletionCandidate n) (l : SignedLiteral n) : Prop :=
  x l.1 = some (!l.2)

def frozenLiteral {n : ℕ} (U : Finset (DeletionCandidate n)) (l : SignedLiteral n) : Prop :=
  ∀ x ∈ U, literalFalse x l

noncomputable def frozenFraction {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (SignedLiteral n)).expect
    (fun l => if frozenLiteral U l then 1 else 0)

noncomputable def oneTestKill {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (Fin k → SignedLiteral n)).expect
    (fun c => if ∀ x ∈ U, ∀ l, literalFalse x (c l) then 1 else 0)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateEncoding
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset
open scoped Classical

def encodeDeletion {n : ℕ} (D : Finset (Fin n)) (s : Fin n → Bool) : DeletionCandidate n :=
  fun v => if v ∈ D then none else some (s v)

def deletedVariables {n : ℕ} (x : DeletionCandidate n) : Finset (Fin n) :=
  univ.filter (fun v => x v = none)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_BatchKilling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

def testKills {n k : ℕ} (U : Finset (DeletionCandidate n))
    (c : Fin k → SignedLiteral n) : Prop :=
  ∀ x ∈ U, ∀ l, literalFalse x (c l)

def batchKills {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (cs : Fin d → Fin k → SignedLiteral n) : Prop :=
  ∀ x ∈ U, ∃ j, ∀ l, literalFalse x (cs j l)

noncomputable def batchKillProbability {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (Fin d → Fin k → SignedLiteral n)).expect
    (fun cs => if batchKills U cs then 1 else 0)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateProcess
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

noncomputable def candidateResidual {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (cs : Fin d → Fin k → SignedLiteral n) : Finset (DeletionCandidate n) :=
  U.filter (fun x => ∀ j, ¬∀ l, literalFalse x (cs j l))

def candidateAlive {n : ℕ} (U : Finset (DeletionCandidate n)) : ℝ :=
  if U.Nonempty then 1 else 0

noncomputable def candidateStep {n : ℕ} [NeZero n] (k : ℕ)
    (f : Finset (DeletionCandidate n) → ℝ) (U : Finset (DeletionCandidate n)) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (Fin k → SignedLiteral n)).expect
    (fun c => f (U.filter (fun x => ¬∀ l, literalFalse x (c l))))

theorem candidateResidual_cons {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (c : Fin k → SignedLiteral n) (cs : Fin d → Fin k → SignedLiteral n) :
    candidateResidual U (Fin.cons c cs) =
      candidateResidual (U.filter (fun x => ¬∀ l, literalFalse x (c l))) cs := by
  ext x
  simp [candidateResidual, Fin.forall_fin_succ, and_assoc]

theorem candidateResidual_empty_iff {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (cs : Fin d → Fin k → SignedLiteral n) :
    candidateResidual U cs = ∅ ↔ batchKills U cs := by
  simp only [candidateResidual, Finset.filter_eq_empty_iff, batchKills]
  constructor
  · intro h x hx
    by_contra hn
    apply h hx
    intro j hj
    exact hn ⟨j, hj⟩
  · intro h x hx hn
    obtain ⟨j, hj⟩ := h x hx
    exact hn j hj

theorem candidateStep_iterate {n : ℕ} [NeZero n] (k d : ℕ)
    (f : Finset (DeletionCandidate n) → ℝ) (U : Finset (DeletionCandidate n)) :
    (candidateStep k)^[d] f U =
      (FiniteLaw.uniform : FiniteLaw (Fin d → Fin k → SignedLiteral n)).expect
        (fun cs => f (candidateResidual U cs)) := by
  induction d generalizing U with
  | zero => simp [candidateResidual, FiniteLaw.expect, FiniteLaw.uniform]
  | succ d ih =>
    rw [Function.iterate_succ_apply', candidateStep]
    simp_rw [ih]
    conv_rhs => rw [uniformFiniteLaw_pi, FiniteLaw.expect_pi_cons]
    rw [← uniformFiniteLaw_pi]
    apply FiniteLaw.expect_congr
    intro c
    apply FiniteLaw.expect_congr
    intro cs
    rw [candidateResidual_cons]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DeletionEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

noncomputable def minimumDeletions {n : ℕ} (U : Finset (DeletionCandidate n)) : ℕ :=
  if h : U.Nonempty then U.inf' h (fun x => (deletedVariables x).card) else n+1

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonKilling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem candidateAlive_nonneg {n : ℕ} (U : Finset (DeletionCandidate n)) :
    0 ≤ candidateAlive U := by unfold candidateAlive; split <;> norm_num

noncomputable def poissonKillProbability {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) (r : ℝ≥0) : ℝ :=
  ∫ d : ℕ, batchKillProbability U k d ∂poissonMeasure r

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonKernel
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

noncomputable def candidateFixedBlock {n : ℕ} [NeZero n]
    (k d : ℕ) (U : Finset (DeletionCandidate n)) : FiniteLaw (Finset (DeletionCandidate n)) where
  weight V := (FiniteLaw.uniform : FiniteLaw (Fin d → Fin k → SignedLiteral n)).expect
    (fun cs => if candidateResidual U cs = V then 1 else 0)
  nonneg V := FiniteLaw.expect_nonneg _ (fun _ => by split <;> norm_num)
  total := by
    classical
    rw [← FiniteLaw.expect_fintype_sum]
    simp

theorem candidateFixedBlock_expect {n : ℕ} [NeZero n]
    (k d : ℕ) (U : Finset (DeletionCandidate n))
    (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateFixedBlock k d U).expect f = (candidateStep k)^[d] f U := by
  classical
  rw [candidateStep_iterate]
  change (∑ V, FiniteLaw.expect _ _ * f V) = _
  simp_rw [← FiniteLaw.expect_mul_right]
  rw [← FiniteLaw.expect_fintype_sum]
  apply FiniteLaw.expect_congr
  intro cs
  simp

noncomputable def candidateBlock {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n)) :
    FiniteLaw (Finset (DeletionCandidate n)) :=
  poissonMixture r (fun d => candidateFixedBlock k d U)

theorem candidateBlock_kill {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n)) :
    (candidateBlock r k U).expect (fun V => if V = ∅ then 1 else 0) =
      poissonKillProbability U k r := by
  classical
  rw [candidateBlock, poissonMixture_expect]
  unfold poissonKillProbability
  congr 1
  funext d
  rw [candidateFixedBlock_expect, candidateStep_iterate]
  unfold batchKillProbability
  apply FiniteLaw.expect_congr
  intro cs
  exact if_congr (candidateResidual_empty_iff U cs) rfl rfl

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonSemigroup
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

noncomputable def poissonCandidateStep {n : ℕ} [NeZero n] (r : ℝ≥0) (k : ℕ)
    (f : Finset (DeletionCandidate n) → ℝ) (U : Finset (DeletionCandidate n)) : ℝ :=
  (candidateBlock r k U).expect f

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateSurvival
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem candidateBlock_expect_alive {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n)) :
    (candidateBlock r k U).expect candidateAlive = 1 - poissonKillProbability U k r := by
  have he : candidateAlive (n := n) = fun V => 1 - (if V = ∅ then 1 else 0) := by
    classical
    funext V
    by_cases h : V = ∅ <;> simp [candidateAlive, h, Finset.nonempty_iff_ne_empty]
  rw [he, FiniteLaw.expect_sub, FiniteLaw.expect_const, candidateBlock_kill]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CandidateMasks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped NNReal Classical

noncomputable def maskRun {n : ℕ} : (m : ℕ) → Finset (DeletionCandidate n) →
    (Fin m → Finset (DeletionCandidate n)) → Finset (DeletionCandidate n)
  | 0, U, _ => U
  | m+1, U, xs => maskRun m (U ∩ xs 0) (Fin.tail xs)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DyadicBlocks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

def dyadicBin {n : ℕ} [NeZero n] (j : ℕ) (U : Finset (DeletionCandidate n)) : Prop :=
  U.Nonempty ∧ dyadicLevel j ≤ poissonKillProbability U 2 60 ∧
    poissonKillProbability U 2 60 ≤ 2*dyadicLevel j

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MaskLifetime
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators NNReal Classical

noncomputable def maskLifetime {n : ℕ} : (m : ℕ) → Finset (DeletionCandidate n) →
    (Fin m → Finset (DeletionCandidate n)) → ℝ
  | 0, _, _ => 0
  | m+1, U, xs => candidateAlive U + maskLifetime m (U ∩ xs 0) (Fin.tail xs)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MaskDelay
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def maskDelayMoment {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k m : ℕ) (U I : Finset (DeletionCandidate n)) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin m => candidateBlock r k Finset.univ)).expect
    (fun xs => (maskLifetime m U xs - maskLifetime m (U ∩ I) xs)^(6/5 : ℝ))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DyadicMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped BigOperators NNReal Topology

theorem poissonKillProbability_le_one {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) (r : ℝ≥0) :
    poissonKillProbability U k r ≤ 1 := by
  have h := FiniteLaw.expect_nonneg (candidateBlock r k U) candidateAlive_nonneg
  rw [candidateBlock_expect_alive] at h
  linarith

theorem positive_killing_in_dyadic_bin {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (hU : U.Nonempty)
    (hq : 0 < poissonKillProbability U 2 60) : ∃ j, dyadicBin j U := by
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near_of_lt_one hq
    (poissonKillProbability_le_one U 2 60)
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨j+1, hU, ?_, ?_⟩
  · simpa only [dyadicLevel, inv_pow] using hj.le
  · have he : 2*dyadicLevel (j+1) = ((2 : ℝ)⁻¹)^j := by
      simp only [dyadicLevel, inv_pow, pow_succ]
      norm_num
      ring
    rwa [he]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ObstructionMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def dyadicIndex {n : ℕ} [NeZero n] (U : Finset (DeletionCandidate n)) : ℕ :=
  if h : U.Nonempty ∧ 0 < poissonKillProbability U 2 60 then
    Nat.find (positive_killing_in_dyadic_bin U h.1 h.2) else 0

noncomputable def dyadicCapBound {n : ℕ} [NeZero n]
    (M : ℕ) (U : Finset (DeletionCandidate n)) : ℝ :=
  if U.Nonempty ∧ 0 < poissonKillProbability U 2 60 then
    min ((M : ℝ)^(1/5 : ℝ)) (dyadicLifetimeBound (dyadicIndex U))
  else (M : ℝ)^(1/5 : ℝ)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_IncidentMasks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

noncomputable def unionMaskLaw {n : ℕ}
    (P Q : FiniteLaw (Finset (DeletionCandidate n))) : FiniteLaw (Finset (DeletionCandidate n)) :=
  finiteMap (P.bind (fun _ => Q)) (fun p => p.1 ∪ p.2)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MaskDeletionTimes
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

def deletionMask {n : ℕ} (D : Finset (Fin n)) : Finset (DeletionCandidate n) :=
  Finset.univ.filter (fun x => deletedVariables x ⊆ D)

def deletionBudgetMask (n r : ℕ) : Finset (DeletionCandidate n) :=
  Finset.univ.filter (fun x => (deletedVariables x).card ≤ r)

def freeDeletionBudgetMask (n r : ℕ) (v : Fin n) : Finset (DeletionCandidate n) :=
  (allowedDeletions n r).biUnion (fun D => deletionMask (insert v D))

noncomputable def fixedMaskDeletionTime {n m : ℕ}
    (xs : Fin m → Finset (DeletionCandidate n)) (D : Finset (Fin n)) : ℝ :=
  maskLifetime m (deletionMask D) xs

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RestoredCandidates
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

def restoreCandidate {n : ℕ} (b : Option Bool) (x : DeletionCandidate n) :
    DeletionCandidate (n+1) := Fin.cons b x

noncomputable def restoredMask {n : ℕ} (B F T : Finset (DeletionCandidate n)) :
    Finset (DeletionCandidate (n+1)) :=
  Finset.univ.filter (fun x => Fin.tail x ∈ B ∧
    match x 0 with
    | none => True
    | some false => Fin.tail x ∈ F
    | some true => Fin.tail x ∈ T)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ClauseRestoration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

noncomputable def clauseMask {n k : ℕ} (c : Fin k → SignedLiteral n) :
    Finset (DeletionCandidate n) :=
  Finset.univ.filter (fun x => ¬∀ l, literalFalse x (c l))

def liftLiteral {n : ℕ} (l : SignedLiteral n) : SignedLiteral (n+1) := (l.1.succ,l.2)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ClauseClasses
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

abbrev TripleClasses (A : Type*) :=
  Triple A ⊕ (Fin 3 × Bool × A × A) ⊕ (Fin 3 × Bool × Bool × A) ⊕ Triple Bool

def splitTriple {A : Type*} : Triple (Bool ⊕ A) → TripleClasses A
  | (.inr a,.inr b,.inr c) => .inl (a,b,c)
  | (.inl a,.inr b,.inr c) => .inr (.inl (0,a,b,c))
  | (.inr a,.inl b,.inr c) => .inr (.inl (1,b,a,c))
  | (.inr a,.inr b,.inl c) => .inr (.inl (2,c,a,b))
  | (.inr a,.inl b,.inl c) => .inr (.inr (.inl (0,b,c,a)))
  | (.inl a,.inr b,.inl c) => .inr (.inr (.inl (1,a,c,b)))
  | (.inl a,.inl b,.inr c) => .inr (.inr (.inl (2,a,b,c)))
  | (.inl a,.inl b,.inl c) => .inr (.inr (.inr (a,b,c)))

def joinTriple {A : Type*} : TripleClasses A → Triple (Bool ⊕ A)
  | .inl (a,b,c) => (.inr a,.inr b,.inr c)
  | .inr (.inl (i,b,a,c)) =>
      if i = 0 then (.inl b,.inr a,.inr c)
      else if i = 1 then (.inr a,.inl b,.inr c)
      else (.inr a,.inr c,.inl b)
  | .inr (.inr (.inl (i,a,b,c))) =>
      if i = 0 then (.inr c,.inl a,.inl b)
      else if i = 1 then (.inl a,.inr c,.inl b)
      else (.inl a,.inl b,.inr c)
  | .inr (.inr (.inr (a,b,c))) => (.inl a,.inl b,.inl c)

def tripleClassesEquiv (A : Type*) : Triple (Bool ⊕ A) ≃ TripleClasses A where
  toFun := splitTriple
  invFun := joinTriple
  left_inv := by
    rintro ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;> rfl
  right_inv := by
    rintro (⟨a,b,c⟩ | (⟨i,a,b,c⟩ | (⟨i,a,b,c⟩ | ⟨a,b,c⟩)))
    · rfl
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
    · rfl

def literalSplitEquiv (n : ℕ) : SignedLiteral (n+1) ≃ Bool ⊕ SignedLiteral n where
  toFun l := Fin.cases (.inl l.2) (fun j => .inr (j,l.2)) l.1
  invFun := fun l => match l with
    | .inl b => (0,b)
    | .inr (j,b) => (j.succ,b)
  left_inv := by
    rintro ⟨i,b⟩
    refine Fin.cases rfl (fun j => ?_) i
    rfl
  right_inv := by
    rintro (b | ⟨j,b⟩) <;> rfl

def tripleVectorEquiv (A : Type*) : (Fin 3 → A) ≃ Triple A where
  toFun f := (f 0,f 1,f 2)
  invFun t := ![t.1,t.2.1,t.2.2]
  left_inv := by intro f; funext i; fin_cases i <;> rfl
  right_inv := by rintro ⟨a,b,c⟩; rfl

def clauseClassesEquiv (n : ℕ) : (Fin 3 → SignedLiteral (n+1)) ≃ TripleClasses (SignedLiteral n) :=
  (Equiv.arrowCongr (Equiv.refl _) (literalSplitEquiv n)).trans
    ((tripleVectorEquiv _).trans (tripleClassesEquiv _))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ClassMasks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

def classClause {n : ℕ} (c : TripleClasses (SignedLiteral n)) : Fin 3 → SignedLiteral (n+1) :=
  (clauseClassesEquiv n).symm c

noncomputable def classBaseMask {n : ℕ} : TripleClasses (SignedLiteral n) → Finset (DeletionCandidate n)
  | .inl c => clauseMask ((tripleVectorEquiv _).symm c)
  | .inr _ => Finset.univ

noncomputable def classIncidentMask {n : ℕ} (v : Bool) :
    TripleClasses (SignedLiteral n) → Finset (DeletionCandidate n)
  | .inl _ => Finset.univ
  | .inr (.inl (_,b,c,d)) => if v = b then Finset.univ else clauseMask ![c,d]
  | .inr (.inr (.inl (_,a,b,c))) => if v = a ∨ v = b then Finset.univ else clauseMask ![c]
  | .inr (.inr (.inr (a,b,c))) => if v = a ∨ v = b ∨ v = c then Finset.univ else ∅

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ActiveClauses
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

def activeClass {n : ℕ} : ActiveClause n → TripleClasses (SignedLiteral n)
  | .inl c => .inl c
  | .inr (b,.inl (i,c,d)) => .inr (.inl (i,b,c,d))
  | .inr (b,.inr (.inl (i,c))) => .inr (.inr (.inl (i,b,b,c)))
  | .inr (b,.inr (.inr _)) => .inr (.inr (.inr (b,b,b)))

noncomputable def incidentMask {n : ℕ} : IncidentClass n → Finset (DeletionCandidate n)
  | .inl (_,c,d) => clauseMask ![c,d]
  | .inr _ => ∅

noncomputable def strongerClassMask {n : ℕ} : ActiveClause n → Finset (DeletionCandidate (n+1))
  | .inl c => restoredMask (clauseMask ((tripleVectorEquiv _).symm c)) Finset.univ Finset.univ
  | .inr (false,c) => restoredMask Finset.univ Finset.univ (incidentMask c)
  | .inr (true,c) => restoredMask Finset.univ (incidentMask c) Finset.univ

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RestoredProcessMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical NNReal

noncomputable def frontloadMask {n m : ℕ} (xs : Fin m → Finset (DeletionCandidate n)) :
    Finset (DeletionCandidate n) := maskRun m Finset.univ xs

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ClauseProcess
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

def splitActiveGrid (n M : ℕ) : ActiveClause n × Fin M ≃
    (Triple (SignedLiteral n) × Fin M) ⊕
      ((IncidentClass n × Fin M) ⊕ (IncidentClass n × Fin M)) where
  toFun p := match p.1 with
    | .inl a => .inl (a,p.2)
    | .inr (false,a) => .inr (.inl (a,p.2))
    | .inr (true,a) => .inr (.inr (a,p.2))
  invFun p := match p with
    | .inl (a,j) => (.inl a,j)
    | .inr (.inl (a,j)) => (.inr (false,a),j)
    | .inr (.inr (a,j)) => (.inr (true,a),j)
  left_inv := by rintro ⟨a,j⟩; rcases a with a | ⟨(_ | _),a⟩ <;> rfl
  right_inv := by rintro (⟨a,j⟩ | (⟨a,j⟩ | ⟨a,j⟩)) <;> rfl

noncomputable def maskGrid {A : Type*} [Fintype A] {n M : ℕ}
    (mask : A → Finset (DeletionCandidate n)) (c : A × Fin M → ℕ) :
    Fin M → Finset (DeletionCandidate n) := fun j => countsMask mask (fun a => c (a,j))

noncomputable def gridMaskLaw {A : Type*} [Fintype A] {n : ℕ}
    (M : ℕ) (r : ℝ≥0) (mask : A → Finset (DeletionCandidate n)) :
    FiniteLaw (Fin M → Finset (DeletionCandidate n)) :=
  finitePushforward (poissonCountLaw (A × Fin M) r) (maskGrid mask)
    (measurable_of_countable _)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_IncidentObstruction
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

abbrev SingleIncident (n : ℕ) := Fin 3 × SignedLiteral n × SignedLiteral n

def singleIncidentEquiv (n : ℕ) : SingleIncident n ≃ (Fin 2 → SignedLiteral n) × Fin 3 where
  toFun p := (![p.2.1,p.2.2],p.1)
  invFun p := (p.2,p.1 0,p.1 1)
  left_inv := by rintro ⟨i,a,b⟩; rfl
  right_inv := by
    rintro ⟨f,i⟩
    apply Prod.ext
    · funext j; fin_cases j <;> rfl
    · rfl

noncomputable def singleIncidentMask {n : ℕ} (p : SingleIncident n) :
    Finset (DeletionCandidate n) := clauseMask ![p.2.1,p.2.2]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ActiveProcess
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

noncomputable def activeMask {n : ℕ} (a : ActiveClause n) : Finset (DeletionCandidate (n+1)) :=
  clauseMask (classClause (activeClass a))

noncomputable def baseMask {n : ℕ} (a : Triple (SignedLiteral n)) : Finset (DeletionCandidate n) :=
  clauseMask ((tripleVectorEquiv _).symm a)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ActualFreeMoment
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

noncomputable def freeGap (n M r : ℕ) (xs : Fin M → Finset (DeletionCandidate (n+1))) : ℝ :=
  (maskLifetime M (freeDeletionBudgetMask (n+1) r 0) xs -
    maskLifetime M (deletionBudgetMask (n+1) r) xs)^(6/5 : ℝ)

noncomputable def restoredGap (n M r : ℕ)
    (base f t : Fin M → Finset (DeletionCandidate n)) : ℝ :=
  (maskLifetime M (deletionBudgetMask n r) base -
    maskLifetime M (deletionBudgetMask (n+1) r)
      (fun j => restoredMask (base j) (f j) (t j)))^(6/5 : ℝ)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ArithmeticSyntax
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Encodable Nat.Partrec RapidForcing.EffectiveProfile RapidForcing.EffectiveArithmetic
open PeriodicLattice.CertifiedReal Filter
open scoped Topology

attribute [local instance] OAI.FixedClauseThreshold.Computability.FiniteArithmetic.arithmeticSyntaxRatPrimcodable
attribute [local instance] OAI.FixedClauseThreshold.Computability.FiniteArithmetic.arithmeticSyntaxCodeEq
theorem expressionValue_effective : Effective expressionValue := by
  apply of_enclosures
    (q := fun p => (expressionBall p.1 p.2).center)
    (e := fun p => (expressionBall p.1 p.2).radius)
  · exact primrec_ball_center.to_comp.comp expressionBall_computable
  · exact primrec_ball_radius.to_comp.comp expressionBall_computable
  · intro a n
    simpa only [Ball.Covers, abs_sub_comm] using (expressionBall_encloses a).1 n
  · intro a
    exact (expressionBall_encloses a).2

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_AuxiliaryEnergy
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

def relaxedClauseEquiv (n : ℕ) : RelaxedClause n ≃ AuxiliaryClause n 3 where
  toFun c j := (c.1 j, c.2 j)
  invFun c := (fun j => (c j).1, fun j => (c j).2)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def relaxedFixedMinimum (n m : ℕ) : ℝ :=
  uniformMean (fun cs : Fin m → RelaxedClause n => (clauseMinimum cs : ℝ))

noncomputable def relaxedPoissonMinimum (n : ℕ) (a : ℝ≥0) : ℝ :=
  ∫ m : ℕ, relaxedFixedMinimum n m ∂poissonMeasure (a*n)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PhysicalExpressions
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Nat.Partrec DilutedSpinGlass RapidForcing.EffectiveArithmetic
open scoped BigOperators

theorem exp_binaryLogSumExpression (x y : Code) :
    Real.exp (expressionValue (binaryLogSumExpression x y)) =
      Real.exp (expressionValue x)+Real.exp (expressionValue y) := by
  rw [binaryLogSumExpression_value, Real.exp_log (by positivity)]

theorem signedExpression_value (x : Code) (b : Bool) :
    expressionValue (signedExpression x b) = expressionValue x * spin b := by
  cases b <;> simp [signedExpression, spin, expressionValue]

@[fun_prop] theorem logQExpression_computable :
    Computable (fun p : Code × Bool => logQExpression p.1 p.2) := by
  unfold logQExpression
  fun_prop

theorem exp_logQExpression (x : Code) (b : Bool) :
    Real.exp (expressionValue (logQExpression x b)) = q (expressionValue x) b := by
  have hp : 0 < Real.exp (-expressionValue x)+Real.exp (expressionValue x) := by positivity
  rw [logQExpression, expressionValue, signedExpression_value,
    show expressionValue (.rfind' (binaryLogSumExpression (.rfind' x) x)) =
      -expressionValue (binaryLogSumExpression (.rfind' x) x) from rfl,
    binaryLogSumExpression_value]
  change Real.exp (expressionValue x * spin b +
    -Real.log (Real.exp (-expressionValue x)+Real.exp (expressionValue x))) = _
  rw [← sub_eq_add_neg, Real.exp_sub, Real.exp_log hp]
  simp only [q, Real.cosh_eq]
  congr 1
  ring

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CavityExpressions
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Nat.Partrec DilutedSpinGlass RapidForcing.EffectiveArithmetic
open scoped BigOperators

noncomputable def boltzmannAtom {p : ℕ} (θ : ℚ) (xs : Fin p → Code)
    (s : Fin p → Bool) : Code :=
  .pair (rationalExpression θ)
    (sumExpressions (List.ofFn (fun i => logQExpression (xs i) (s i))))

attribute [local instance] OAI.FixedClauseThreshold.Computability.FiniteArithmetic.cavityExpressionsRatPrimcodable
@[fun_prop] theorem boltzmannAtom_computable (p : ℕ) :
    Computable (fun a : ℚ × (Fin p → Code) × (Fin p → Bool) =>
      boltzmannAtom a.1 a.2.1 a.2.2) := by
  have hv : Computable (fun a : ℚ × (Fin p → Code) × (Fin p → Bool) =>
      List.ofFn (fun i => logQExpression (a.2.1 i) (a.2.2 i))) := by
    apply Computable.list_ofFn
    intro i
    fun_prop
  unfold boltzmannAtom
  fun_prop

theorem exp_boltzmannAtom {p : ℕ} (θ : ℚ) (xs : Fin p → Code) (s : Fin p → Bool) :
    Real.exp (expressionValue (boltzmannAtom θ xs s)) =
      Real.exp (θ : ℝ) * ∏ i, q (expressionValue (xs i)) (s i) := by
  simp only [boltzmannAtom, expressionValue, rationalExpression_value,
    sumExpressions_value, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    Real.exp_add, Real.exp_sum, exp_logQExpression]

@[fun_prop] theorem clausePenalty_computable :
    Computable (fun p : ℚ × (Fin 3 → Bool) × (Fin 3 → Bool) =>
      clausePenalty p.1 p.2.1 p.2.2) := by
  have h : Computable (fun p : ℚ × (Fin 3 → Bool) × (Fin 3 → Bool) =>
      if p.2.2 0 ≠ p.2.1 0 ∧ p.2.2 1 ≠ p.2.1 1 ∧ p.2.2 2 ≠ p.2.1 2
      then -p.1 else 0) := by fun_prop
  exact h.of_eq (fun p => by simp [clausePenalty, Fin.forall_fin_succ])

theorem clausePenalty_cast (β : ℚ) (J s : Fin 3 → Bool) :
    (clausePenalty β J s : ℝ) = satInteraction (β : ℝ) J s := by
  unfold clausePenalty satInteraction
  split <;> simp

noncomputable def edgeExpression (β : ℚ) (J : Fin 3 → Bool) (xs : Fin 3 → Code) : Code :=
  binaryLogSumExpression
    (binaryLogSumExpression
      (binaryLogSumExpression (boltzmannAtom (clausePenalty β J ![false,false,false]) xs ![false,false,false])
        (boltzmannAtom (clausePenalty β J ![false,false,true]) xs ![false,false,true]))
      (binaryLogSumExpression (boltzmannAtom (clausePenalty β J ![false,true,false]) xs ![false,true,false])
        (boltzmannAtom (clausePenalty β J ![false,true,true]) xs ![false,true,true])))
    (binaryLogSumExpression
      (binaryLogSumExpression (boltzmannAtom (clausePenalty β J ![true,false,false]) xs ![true,false,false])
        (boltzmannAtom (clausePenalty β J ![true,false,true]) xs ![true,false,true]))
      (binaryLogSumExpression (boltzmannAtom (clausePenalty β J ![true,true,false]) xs ![true,true,false])
        (boltzmannAtom (clausePenalty β J ![true,true,true]) xs ![true,true,true])))

@[fun_prop] theorem edgeExpression_computable :
    Computable (fun p : ℚ × (Fin 3 → Bool) × (Fin 3 → Code) =>
      edgeExpression p.1 p.2.1 p.2.2) := by
  unfold edgeExpression
  fun_prop

noncomputable def messageExpression (β : ℚ) (J : Fin 3 → Bool)
    (xs : Fin 2 → Code) (ε : Bool) : Code :=
  binaryLogSumExpression
    (binaryLogSumExpression
      (boltzmannAtom (clausePenalty β J (extendSpins false false ε)) xs ![false,false])
      (boltzmannAtom (clausePenalty β J (extendSpins false true ε)) xs ![false,true]))
    (binaryLogSumExpression
      (boltzmannAtom (clausePenalty β J (extendSpins true false ε)) xs ![true,false])
      (boltzmannAtom (clausePenalty β J (extendSpins true true ε)) xs ![true,true]))

@[fun_prop] theorem messageExpression_computable :
    Computable (fun p : ℚ × (Fin 3 → Bool) × (Fin 2 → Code) × Bool =>
      messageExpression p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold messageExpression
  fun_prop

theorem messageExpression_value (β : ℚ) (J : Fin 3 → Bool)
    (xs : Fin 2 → Code) (ε : Bool) :
    expressionValue (messageExpression β J xs ε) =
      message (satInteraction (β : ℝ) J) (fun i => expressionValue (xs i)) ε := by
  rw [← Real.log_exp (expressionValue (messageExpression β J xs ε))]
  unfold messageExpression message
  congr 1
  simp only [exp_binaryLogSumExpression, exp_boltzmannAtom, clausePenalty_cast]
  simp_rw [sum_bool_vector_succ]
  simp only [Fintype.sum_unique]
  have ht (a b : Bool) (t : Fin 0 → Bool) : Fin.cons a (Fin.cons b t) = ![a,b] := by
    funext i
    fin_cases i <;> rfl
  simp only [ht, appendSpin_three, extendSpins]

noncomputable def siteExpression (β : ℚ) (data : List SiteExpressionDatum) : Code :=
  binaryLogMeanExpression
    (sumExpressions (data.map (fun z => messageExpression β z.1 z.2 false)))
    (sumExpressions (data.map (fun z => messageExpression β z.1 z.2 true)))

@[fun_prop] theorem siteExpression_computable :
    Computable (fun p : ℚ × List SiteExpressionDatum => siteExpression p.1 p.2) := by
  have hm (ε : Bool) : Computable (fun p : ℚ × List SiteExpressionDatum =>
      p.2.map (fun z => messageExpression p.1 z.1 z.2 ε)) := by
    apply computable_list_map Computable.snd
    unfold Computable₂
    fun_prop
  unfold siteExpression
  fun_prop

attribute [local irreducible] edgeExpression siteExpression

theorem edgeExpression_comp {A : Type} [Primcodable A]
    (β : A → ℚ) (J : A → Fin 3 → Bool) (xs : A → Fin 3 → Code)
    (hβ : Computable β) (hJ : Computable J) (hx : Computable xs) :
    Computable (fun a => edgeExpression (β a) (J a) (xs a)) := by
  exact edgeExpression_computable.comp (hβ.pair (hJ.pair hx))

theorem siteExpression_comp {A : Type} [Primcodable A]
    (β : A → ℚ) (data : A → List SiteExpressionDatum)
    (hβ : Computable β) (hd : Computable data) :
    Computable (fun a => siteExpression (β a) (data a)) := by
  exact siteExpression_computable.comp (hβ.pair hd)

theorem siteExpression_ofFn_value {k : ℕ} (β : ℚ)
    (J : Fin k → Fin 3 → Bool) (xs : Fin k → Fin 2 → Code) :
    expressionValue (siteExpression β (List.ofFn (fun j => (J j,xs j)))) =
      siteLog (fun j => satSample (β : ℝ) (J j)) 0
        (fun i => expressionValue (xs i.1 i.2)) := by
  simp only [siteExpression, binaryLogMeanExpression_value, sumExpressions_value,
    List.map_ofFn, List.sum_ofFn, Function.comp_def, messageExpression_value]
  simp only [siteLog, zero_mul, zero_add, satSample, Fintype.sum_bool]
  congr 2
  exact add_comm _ _

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CertificateSearch
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology
open RapidForcing.EffectiveArithmetic

@[fun_prop]
theorem tolerance_computable : Computable tolerance := by
  unfold tolerance
  fun_prop

def certificateTest (lower upper : ℕ → ℚ) (valid : ℕ → Bool)
    (r n : ℕ) : Option ℚ :=
  let i := n.unpair.1
  let j := n.unpair.2
  if valid j = true ∧ upper j - lower i ≤ 2 * tolerance r then
    some ((lower i + upper j) / 2)
  else none

def certificateProgram (lower upper : ℕ → ℚ) (valid : ℕ → Bool)
    (r : ℕ) : Part ℚ :=
  Nat.rfindOpt (certificateTest lower upper valid r)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_FiniteTrialEvaluation
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory
open scoped BigOperators

attribute [local instance] OAI.FixedClauseThreshold.Computability.finiteTrialEvaluationMeasurable
attribute [local instance] OAI.FixedClauseThreshold.Computability.finiteTrialEvaluationBorel
theorem finiteLogMean_eq {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (m : Fin r → ℝ) (t : ι → RationalTree r) :
    finiteLogMean r g m t = logMean r g m (fun i => rationalTreeValue r (t i)) := by
  classical
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [finiteLogMean, logMean, rationalTreeValue_asProbability]
    rw [FiniteLaw.integral_pi_asProbability]
    congr 2
    apply FiniteLaw.expect_congr
    intro a
    rw [ih]

theorem finiteTrialLog_eq {ι : Type} [Fintype ι] (r : ℕ)
    (t : RationalTree (r+1)) (m : Fin r → ℝ) (g : (ι → ℝ) → ℝ) :
    finiteTrialLog r t m g = trialLog r (rationalTreeValue (r+1) t) m g := by
  classical
  rw [trialLog, rationalTreeValue_asProbability, FiniteLaw.integral_pi_asProbability]
  apply FiniteLaw.expect_congr
  intro a
  exact finiteLogMean_eq r g m _

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_LowerBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology

instance decidableClauseSatisfaction {n k : ℕ} (σ : Assignment n)
    (C : ProperClause n k) : Decidable (SatisfiesClause σ C) := by
  unfold SatisfiesClause
  infer_instance

instance decidableFormulaSatisfaction {n k m : ℕ} (σ : Assignment n)
    (F : Formula n k m) : Decidable (Satisfies σ F) := by
  unfold Satisfies
  infer_instance

instance decidableSatisfiability {n k m : ℕ} (F : Formula n k m) :
    Decidable (Satisfiable F) := by
  unfold Satisfiable
  infer_instance

def rationalProbability (n k m : ℕ) : ℚ :=
  (Fintype.card {F : Formula n k m // Satisfiable F} : ℚ) /
    (Fintype.card (Formula n k m) : ℚ)

def rationalCenter (n k : ℕ) : ℚ :=
  (∑ j ∈ Finset.range (mainCap n k), rationalProbability n k (j + 1)) / n

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_FiniteEnumeration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open RapidForcing.EffectiveArithmetic

def encodeClause {n k : ℕ} (c : ProperClause n k) : List (Option Bool) :=
  List.ofFn c.val

def encodeFormula {n k m : ℕ} (f : Formula n k m) : List (List (Option Bool)) :=
  List.ofFn fun j => encodeClause (f j)

attribute [local irreducible] rationalProbability

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_HierarchyEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Encodable Denumerable Nat.Partrec FiniteArithmetic
open scoped BigOperators

noncomputable def branchEntry : Code → ℚ × Code
  | .comp w c => (decodedRational w, c)
  | _ => (0, .zero)

noncomputable def rawBranches : Code → List (ℚ × Code)
  | .pair c rest => branchEntry c :: rawBranches rest
  | _ => []

noncomputable def normalizedBranches (c : Code) : List (ℚ × Code) :=
  let bs := rawBranches c
  let s := (bs.map (fun b => |b.1|)).sum
  if s = 0 then [(1, .zero)] else bs.map (fun b => (|b.1|/s, b.2))

theorem normalizedBranches_nonneg (c : Code) :
    ∀ b ∈ normalizedBranches c, 0 ≤ b.1 := by
  dsimp only [normalizedBranches]
  split_ifs with hs
  · simp
  · intro b hb
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
    exact div_nonneg (abs_nonneg _) (List.sum_nonneg (fun _ hx => by
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      exact abs_nonneg _))

theorem normalizedBranches_sum (c : Code) :
    ((normalizedBranches c).map Prod.fst).sum = 1 := by
  dsimp only [normalizedBranches]
  split_ifs with hs
  · simp
  · simp only [List.map_map, Function.comp_def]
    simp only [div_eq_mul_inv]
    rw [List.sum_map_mul_right]
    exact mul_inv_cancel₀ hs

noncomputable def branchWeights (c : Code) :
    RationalWeights (Fin (normalizedBranches c).length) :=
  ⟨fun i => ((normalizedBranches c).get i).1, by
    constructor
    · intro i
      exact normalizedBranches_nonneg c _ (List.get_mem _ _)
    · have h : (List.ofFn (fun i : Fin (normalizedBranches c).length =>
          ((normalizedBranches c).get i).1)).sum = 1 := by
        simp only [List.get_eq_getElem]
        rw [List.ofFn_getElem_eq_map, normalizedBranches_sum]
      simpa only [List.sum_ofFn] using h⟩

noncomputable def decodeTree : (r : ℕ) → Code → RationalTree r
  | 0, c => decodedRational c
  | r+1, c => ⟨(normalizedBranches c).length, branchWeights c,
      fun i => decodeTree r ((normalizedBranches c).get i).2⟩

noncomputable def encodeTree : (r : ℕ) → RationalTree r → Code
  | 0, q => ofNat Code (@encode ℚ Rat.instEncodable q)
  | r+1, t => encodeBranches (List.ofFn (fun i : Fin t.1 =>
      (t.2.1.val i, encodeTree r (t.2.2 i))))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_HierarchyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Encodable Denumerable Nat.Partrec

theorem branchEntry_code_le (c : Code) : encode (branchEntry c).2 ≤ encode c := by
  cases c with
  | comp w c => exact (Code.encode_lt_comp w c).2.le
  | zero => rfl
  | succ => exact Nat.zero_le _
  | left => exact Nat.zero_le _
  | right => exact Nat.zero_le _
  | pair c d => exact Nat.zero_le _
  | prec c d => exact Nat.zero_le _
  | rfind' c => exact Nat.zero_le _

theorem rawBranches_code_le (c : Code) :
    ∀ b ∈ rawBranches c, encode b.2 ≤ encode c := by
  induction c with
  | pair c d _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with h | h
    · subst b
      exact (branchEntry_code_le c).trans (Code.encode_lt_pair c d).1.le
    · exact (ih b h).trans (Code.encode_lt_pair c d).2.le
  | zero | succ | left | right | comp _ _ _ _ | prec _ _ _ _ | rfind' _ _ =>
    simp only [rawBranches, List.not_mem_nil, false_implies, implies_true]

theorem normalizedBranches_code_le (c : Code) :
    ∀ b ∈ normalizedBranches c, encode b.2 ≤ encode c := by
  dsimp only [normalizedBranches]
  split_ifs
  · intro b hb
    have h : b = (1, Code.zero) := by simpa only [List.mem_singleton] using hb
    subst b
    exact Nat.zero_le _
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact rawBranches_code_le c x hx

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_HierarchyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
open PeriodicLattice.CertifiedReal
local instance hierarchyProgramRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

@[fun_prop] theorem branchEntry_computable : Computable branchEntry := by
  have h := Code.computable_recOn (c := id) Computable.id
    (z := fun _ => ((0 : ℚ), Code.zero)) (by fun_prop)
    (s := fun _ => ((0 : ℚ), Code.zero)) (by fun_prop)
    (l := fun _ => ((0 : ℚ), Code.zero)) (by fun_prop)
    (r := fun _ => ((0 : ℚ), Code.zero)) (by fun_prop)
    (pr := fun _ _ => ((0 : ℚ), Code.zero)) (by unfold Computable₂; fun_prop)
    (co := fun _ p => (decodedRational p.1, p.2.1)) (by unfold Computable₂; fun_prop)
    (pc := fun _ _ => ((0 : ℚ), Code.zero)) (by unfold Computable₂; fun_prop)
    (rf := fun _ _ => ((0 : ℚ), Code.zero)) (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun c => by cases c <;> rfl)

@[fun_prop] theorem rawBranches_computable : Computable rawBranches := by
  have h := Code.computable_recOn (c := id) Computable.id
    (z := fun _ => ([] : List (ℚ × Code))) (by fun_prop)
    (s := fun _ => ([] : List (ℚ × Code))) (by fun_prop)
    (l := fun _ => ([] : List (ℚ × Code))) (by fun_prop)
    (r := fun _ => ([] : List (ℚ × Code))) (by fun_prop)
    (pr := fun _ p => branchEntry p.1 :: p.2.2.2) (by unfold Computable₂; fun_prop)
    (co := fun _ _ => ([] : List (ℚ × Code))) (by unfold Computable₂; fun_prop)
    (pc := fun _ _ => ([] : List (ℚ × Code))) (by unfold Computable₂; fun_prop)
    (rf := fun _ _ => ([] : List (ℚ × Code))) (by unfold Computable₂; fun_prop)
  apply h.of_eq
  intro c
  induction c <;> simp_all only [rawBranches, id_eq]

attribute [local irreducible] rawBranches

@[fun_prop] theorem normalizedBranches_computable : Computable normalizedBranches := by
  have hm : Computable (fun c => (rawBranches c).map (fun b => |b.1|)) :=
    computable_list_map rawBranches_computable (by unfold Computable₂; fun_prop)
  have hs : Computable (fun c => ((rawBranches c).map (fun b => |b.1|)).sum) :=
    (computable_list_sum computable_rat_add).comp hm
  have hz : CompPred (fun c => ((rawBranches c).map (fun b => |b.1|)).sum = 0) := by
    unfold CompPred
    have he : Computable (fun p : ℚ × ℚ => decide (p.1 = p.2)) := by fun_prop
    exact he.comp (hs.pair (Computable.const 0))
  have hf : Computable (fun c => (rawBranches c).map (fun b =>
      (|b.1| / ((rawBranches c).map (fun x => |x.1|)).sum, b.2))) := by
    apply computable_list_map rawBranches_computable
    unfold Computable₂
    have hd : Computable (fun p : Code × (ℚ × Code) =>
        ((rawBranches p.1).map (fun x => |x.1|)).sum) := hs.comp Computable.fst
    fun_prop
  exact computable_ite hz (Computable.const [(1, Code.zero)]) hf

noncomputable def chooseChildren (cs : List Code) : List (ℚ × List Code) :=
  cs.foldr (fun c rest => (normalizedBranches c).flatMap (fun b =>
    rest.map (fun r => (b.1*r.1, b.2::r.2)))) [(1, [])]

@[fun_prop] theorem chooseChildren_computable : Computable chooseChildren := by
  have hs : Computable (fun p : Code × List (ℚ × List Code) =>
      (normalizedBranches p.1).flatMap (fun b =>
        p.2.map (fun r => (b.1*r.1, b.2::r.2)))) := by
    apply computable_list_flatMap (normalizedBranches_computable.comp Computable.fst)
    unfold Computable₂
    apply computable_list_map (Computable.snd.comp Computable.fst)
    unfold Computable₂
    fun_prop
  exact computable_list_foldr Computable.id (Computable.const [(1, [])])
    (hs.comp Computable.snd).to₂

theorem chooseChildren_nonneg (cs : List Code) : ∀ b ∈ chooseChildren cs, 0 ≤ b.1 := by
  induction cs with
  | nil => simp [chooseChildren]
  | cons c cs ih =>
    intro b hb
    obtain ⟨x, hx, hz⟩ := List.mem_flatMap.mp hb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact mul_nonneg (normalizedBranches_nonneg c x hx) (ih y hy)

theorem chooseChildren_sum (cs : List Code) : ((chooseChildren cs).map Prod.fst).sum = 1 := by
  induction cs with
  | nil => simp [chooseChildren]
  | cons c cs ih =>
    change (((normalizedBranches c).flatMap (fun b =>
      (chooseChildren cs).map (fun r => (b.1*r.1, b.2::r.2)))).map Prod.fst).sum = 1
    simp only [List.map_flatMap, sum_flatMap_eq, List.map_map, Function.comp_def,
      List.sum_map_mul_left, ih, mul_one]
    exact normalizedBranches_sum c

theorem chooseChildren_length (cs : List Code) :
    ∀ b ∈ chooseChildren cs, b.2.length = cs.length := by
  induction cs with
  | nil => simp [chooseChildren]
  | cons c cs ih =>
    intro b hb
    obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp hb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    simpa only [List.length_cons] using congrArg Nat.succ (ih y hy)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_HierarchyExpectation
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec
open scoped BigOperators

theorem normalizedBranches_expect (c : Code) (f : Code → ℝ) :
    ((normalizedBranches c).map (fun b => (b.1 : ℝ)*f b.2)).sum =
      (branchWeights c).toLaw.expect (fun i => f ((normalizedBranches c).get i).2) := by
  unfold DilutedSpinGlass.FiniteLaw.expect
  change _ = ∑ i : Fin (normalizedBranches c).length,
    (((normalizedBranches c).get i).1 : ℝ) * f ((normalizedBranches c).get i).2
  rw [← List.sum_ofFn]
  have h := congrArg (fun bs : List (ℚ × Code) =>
    (bs.map (fun b => (b.1 : ℝ)*f b.2)).sum) (List.ofFn_get (normalizedBranches c))
  simpa only [List.map_ofFn, Function.comp_def] using h.symm

theorem branchSum_cons (c : Code) (cs : List Code) (f : List Code → ℝ) :
    branchSum (chooseChildren (c::cs)) f =
      ((normalizedBranches c).map (fun b => (b.1 : ℝ) *
        branchSum (chooseChildren cs) (fun rest => f (b.2::rest)))).sum := by
  simp only [branchSum, chooseChildren, List.foldr_cons, List.map_flatMap,
    sum_flatMap_eq, List.map_map, Function.comp_def, Rat.cast_mul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro r _
  exact mul_assoc _ _ _

theorem chooseChildren_expect_ofFn {L : ℕ} (cs : Fin L → Code) (f : List Code → ℝ) :
    branchSum (chooseChildren (List.ofFn cs)) f =
      (FiniteLaw.pi (fun i : Fin L => (branchWeights (cs i)).toLaw)).expect
        (fun a => f (List.ofFn (fun i => ((normalizedBranches (cs i)).get (a i)).2))) := by
  induction L generalizing f with
  | zero => simp [branchSum, chooseChildren, FiniteLaw.expect, FiniteLaw.pi]
  | succ L ih =>
    rw [List.ofFn_succ, branchSum_cons]
    simp_rw [ih]
    rw [normalizedBranches_expect (cs 0) (fun d =>
      (FiniteLaw.pi (fun i : Fin L => (branchWeights (cs i.succ)).toLaw)).expect
        (fun a => f (d :: List.ofFn (fun i =>
          ((normalizedBranches (cs i.succ)).get (a i)).2)))), FiniteLaw.expect_pi_cons]
    apply FiniteLaw.expect_congr
    intro a
    apply FiniteLaw.expect_congr
    intro rest
    congr 1
    rw [List.ofFn_succ]
    rfl

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_HierarchyTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Nat.Partrec Encodable Denumerable FiniteArithmetic
open RapidForcing.EffectiveArithmetic
local instance hierarchyTableRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

attribute [local instance] OAI.FixedClauseThreshold.Computability.hierarchyTableCodeEq
attribute [local instance] OAI.FixedClauseThreshold.Computability.hierarchyTableListBEq
noncomputable def tableLookup (tab : ExpressionTable) (cs : List Code) : Code :=
  (tab.lookup cs).getD .zero

@[fun_prop] theorem tableLookup_computable :
    Computable (fun p : ExpressionTable × List Code => tableLookup p.1 p.2) := by
  unfold tableLookup
  exact (Primrec.option_getD.comp
    ((Primrec.listLookup (α := List Code) (β := Code)).comp Primrec.snd Primrec.fst)
    (Primrec.const Code.zero)).to_comp

theorem tableLookup_map (states : List (List Code)) (f : List Code → Code)
    {cs : List Code} (hcs : cs ∈ states) :
    tableLookup (states.map (fun ds => (ds, f ds))) cs = f cs := by
  unfold tableLookup
  rw [List.lookup_graph f hcs]
  rfl

noncomputable def layerExpression (m : ℚ) (tab : ExpressionTable) (cs : List Code) : Code :=
  .comp (rationalExpression m⁻¹)
    (logMixtureExpression ((chooseChildren cs).map (fun b =>
      (b.1, Code.comp (rationalExpression m) (tableLookup tab b.2)))))

@[fun_prop] theorem layerExpression_computable :
    Computable (fun p : ℚ × ExpressionTable × List Code => layerExpression p.1 p.2.1 p.2.2) := by
  have hl : Computable (fun p : ℚ × ExpressionTable × List Code =>
      (chooseChildren p.2.2).map (fun b =>
        (b.1, Code.comp (rationalExpression p.1) (tableLookup p.2.1 b.2)))) := by
    apply computable_list_map (chooseChildren_computable.comp (by fun_prop))
    unfold Computable₂
    fun_prop
  unfold layerExpression
  fun_prop

noncomputable def tableLayer (states : List (List Code)) (m : ℚ) (tab : ExpressionTable) :
    ExpressionTable := states.map (fun cs => (cs, layerExpression m tab cs))

@[fun_prop] theorem tableLayer_computable :
    Computable (fun p : List (List Code) × ℚ × ExpressionTable => tableLayer p.1 p.2.1 p.2.2) := by
  unfold tableLayer
  apply computable_list_map Computable.fst
  unfold Computable₂
  fun_prop

noncomputable def hierarchyTable (states : List (List Code)) (ms : List ℚ)
    (initial : ExpressionTable) : ExpressionTable :=
  ms.foldr (fun m tab => tableLayer states m tab) initial

@[fun_prop] theorem hierarchyTable_computable :
    Computable (fun p : List (List Code) × List ℚ × ExpressionTable =>
      hierarchyTable p.1 p.2.1 p.2.2) := by
  unfold hierarchyTable
  exact computable_list_foldr
    (f := fun p : List (List Code) × List ℚ × ExpressionTable => p.2.1)
    (g := fun p => p.2.2) (h := fun p q => tableLayer p.1 q.1 q.2)
    (by fun_prop) (by fun_prop) (by unfold Computable₂; fun_prop)

noncomputable def listLogMean : List ℚ → (List Code → ℝ) → List Code → ℝ
  | [], g, cs => g cs
  | m::ms, g, cs => Real.log (branchSum (chooseChildren cs)
      (fun ds => Real.exp ((m : ℝ)*listLogMean ms g ds))) / (m : ℝ)

theorem layerExpression_value (m : ℚ) (tab : ExpressionTable) (cs : List Code) :
    expressionValue (layerExpression m tab cs) =
      Real.log (branchSum (chooseChildren cs)
        (fun ds => Real.exp ((m : ℝ)*expressionValue (tableLookup tab ds)))) / (m : ℝ) := by
  have hw : ∀ b ∈ (chooseChildren cs).map (fun b =>
      (b.1, Code.comp (rationalExpression m) (tableLookup tab b.2))), 0 ≤ b.1 := by
    intro b hb
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    exact chooseChildren_nonneg cs d hd
  have hs : (((chooseChildren cs).map (fun b =>
      (b.1, Code.comp (rationalExpression m) (tableLookup tab b.2)))).map Prod.fst).sum = 1 := by
    simpa only [List.map_map, Function.comp_def] using chooseChildren_sum cs
  simp only [layerExpression, expressionValue, rationalExpression_value, Rat.cast_inv,
    logMixtureExpression_value _ hw hs, List.map_map, Function.comp_def, branchSum]
  ring

theorem chooseChildren_in_states {B L : ℕ} {cs : List Code}
    (hcs : cs ∈ hierarchyStates B L) :
    ∀ b ∈ chooseChildren cs, b.2 ∈ hierarchyStates B L := by
  obtain ⟨hL, hB⟩ := (mem_hierarchyStates B L cs).mp hcs
  intro b hb
  apply (mem_hierarchyStates B L b.2).mpr
  refine ⟨(chooseChildren_length cs b hb).trans hL, ?_⟩
  have hall : ∀ c ∈ cs, Encodable.encode c ≤ B := hB
  clear hL hcs hB
  induction cs generalizing b with
  | nil =>
    have he : b = (1, []) := by simpa only [chooseChildren, List.foldr_nil, List.mem_singleton] using hb
    simp [he]
  | cons c cs ih =>
    obtain ⟨x, hx, hymap⟩ := List.mem_flatMap.mp hb
    obtain ⟨y, hymem, rfl⟩ := List.mem_map.mp hymap
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact (normalizedBranches_code_le c x hx).trans (hall c (by simp))
    · exact ih y hymem (fun z hz => hall z (List.mem_cons_of_mem c hz)) d hd

theorem hierarchyTable_value (B L : ℕ) (ms : List ℚ) (initial : ExpressionTable)
    (g : List Code → ℝ)
    (hinit : ∀ cs ∈ hierarchyStates B L, expressionValue (tableLookup initial cs) = g cs)
    (cs : List Code) (hcs : cs ∈ hierarchyStates B L) :
    expressionValue (tableLookup (hierarchyTable (hierarchyStates B L) ms initial) cs) =
      listLogMean ms g cs := by
  induction ms generalizing cs with
  | nil => exact hinit cs hcs
  | cons m ms ih =>
    change expressionValue (tableLookup
      (tableLayer (hierarchyStates B L) m (hierarchyTable (hierarchyStates B L) ms initial)) cs) = _
    rw [tableLayer, tableLookup_map _ _ hcs,
      layerExpression_value, listLogMean]
    congr 2
    unfold branchSum
    congr 1
    apply List.map_congr_left
    intro b hb
    change (b.1 : ℝ) * Real.exp ((m : ℝ) * expressionValue
      (tableLookup (hierarchyTable (hierarchyStates B L) ms initial) b.2)) =
        (b.1 : ℝ) * Real.exp ((m : ℝ) * listLogMean ms g b.2)
    rw [ih b.2 (chooseChildren_in_states hcs b hb)]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_HierarchySemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic
attribute [local irreducible] normalizedBranches branchWeights

noncomputable def leafFields (L : ℕ) (cs : List Code) : Fin L → ℝ :=
  fun i => decodedRational (cs[i.val]?.getD .zero)

theorem leafFields_ofFn {L : ℕ} (cs : Fin L → Code) :
    leafFields L (List.ofFn cs) = fun i => (decodedRational (cs i) : ℝ) := by
  funext i
  simp [leafFields, i.isLt]

theorem listLogMean_eq_finite {L : ℕ} (ms : List ℚ) (g : (Fin L → ℝ) → ℝ)
    (cs : Fin L → Code) :
    listLogMean ms (fun ds => g (leafFields L ds)) (List.ofFn cs) =
      finiteLogMean ms.length g (fun i => (ms.get i : ℝ))
        (fun i => decodeTree ms.length (cs i)) := by
  induction ms generalizing cs with
  | nil =>
    change g (leafFields L (List.ofFn cs)) = g (fun i => (decodedRational (cs i) : ℝ))
    rw [leafFields_ofFn]
  | cons m ms ih =>
    rw [listLogMean, chooseChildren_expect_ofFn]
    simp_rw [ih]
    simp only [List.length_cons, finiteLogMean, decodeTree, List.get_eq_getElem,
      List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero, Fin.val_succ]
    rw [show (instDecidableEqFin L : DecidableEq (Fin L)) =
      (fun a b => Classical.propDecidable (a = b)) from Subsingleton.elim _ _]

theorem listTrialLog_eq_finite {L : ℕ} (ms : List ℚ) (g : (Fin L → ℝ) → ℝ)
    (root : Code) :
    branchSum (chooseChildren (List.replicate L root))
      (listLogMean ms (fun ds => g (leafFields L ds))) =
        finiteTrialLog ms.length (decodeTree (ms.length+1) root)
          (fun i => (ms.get i : ℝ)) g := by
  rw [← List.ofFn_const L root, chooseChildren_expect_ofFn]
  simp_rw [listLogMean_eq_finite]
  simp only [finiteTrialLog, decodeTree]
  rw [show (instDecidableEqFin L : DecidableEq (Fin L)) =
    (fun a b => Classical.propDecidable (a = b)) from Subsingleton.elim _ _]
  rfl

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_HierarchyEvaluator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Encodable Denumerable Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
local instance hierarchyEvaluatorRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

@[fun_prop] theorem codeAlphabet_computable : Computable codeAlphabet := by
  unfold codeAlphabet
  apply computable_list_map (by fun_prop)
  exact ((Primrec.ofNat Code).to_comp.comp Computable.snd).to₂

@[fun_prop] theorem hierarchyStates_computable :
    Computable (fun p : ℕ × ℕ => hierarchyStates p.1 p.2) := by
  unfold hierarchyStates
  exact words_primrec.to_comp.comp (codeAlphabet_computable.comp Computable.fst) Computable.snd

variable {A : Type}

attribute [local irreducible] hierarchyTable hierarchyStates chooseChildren
  tableLookup rationalExpression

noncomputable def trialExpression (leaf : A → List Code → Code) (a : A)
    (root : Code) (ms : List ℚ) (L : ℕ) : Code :=
  let states := hierarchyStates (encode root) L
  let tab := hierarchyTable states ms (states.map (fun ds => (ds, leaf a ds)))
  sumExpressions ((chooseChildren (List.replicate L root)).map (fun b =>
    Code.comp (rationalExpression b.1) (tableLookup tab b.2)))

theorem trialExpression_computable [Primcodable A] (leaf : A → List Code → Code)
    (hleaf : Computable (fun p : A × List Code => leaf p.1 p.2)) :
    Computable (fun p : A × Code × List ℚ × ℕ =>
      trialExpression leaf p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hc : Computable (fun p : Code × Code => p.1.comp p.2) :=
    Code.primrec₂_comp.to_comp
  have hr : Computable (fun p : ℕ × Code => List.replicate p.1 p.2) := by
    have h : Computable (fun p : ℕ × Code => (List.range p.1).map (fun _ => p.2)) := by
      apply computable_list_map (Primrec.list_range.to_comp.comp Computable.fst)
      unfold Computable₂
      fun_prop
    exact h.of_eq (fun p => by simp)
  have hi : Computable (fun p : A × Code × List ℚ × ℕ =>
      (hierarchyStates (encode p.2.1) p.2.2.2).map (fun ds => (ds, leaf p.1 ds))) := by
    apply computable_list_map (by fun_prop)
    unfold Computable₂
    fun_prop
  have ht : Computable (fun p : A × Code × List ℚ × ℕ =>
      hierarchyTable (hierarchyStates (encode p.2.1) p.2.2.2) p.2.2.1
        ((hierarchyStates (encode p.2.1) p.2.2.2).map (fun ds => (ds, leaf p.1 ds)))) := by
    fun_prop
  unfold trialExpression
  apply sumExpressions_computable.comp
  apply computable_list_map (by fun_prop)
  unfold Computable₂
  have hw : Computable (fun p : (A × Code × List ℚ × ℕ) × (ℚ × List Code) =>
      rationalExpression p.2.1) := rationalExpression_computable.comp (by fun_prop)
  have hl : Computable (fun p : (A × Code × List ℚ × ℕ) × (ℚ × List Code) =>
      tableLookup (hierarchyTable (hierarchyStates (encode p.1.2.1) p.1.2.2.2) p.1.2.2.1
        ((hierarchyStates (encode p.1.2.1) p.1.2.2.2).map (fun ds => (ds, leaf p.1.1 ds))))
          p.2.2) :=
    tableLookup_computable.comp ((ht.comp Computable.fst).pair (by fun_prop))
  exact hc.comp (hw.pair hl)

theorem trialExpression_value (leaf : A → List Code → Code) (a : A)
    (root : Code) (ms : List ℚ) (L : ℕ) :
    expressionValue (trialExpression leaf a root ms L) =
      branchSum (chooseChildren (List.replicate L root))
        (listLogMean ms (fun ds => expressionValue (leaf a ds))) := by
  have hroot : List.replicate L root ∈ hierarchyStates (encode root) L := by
    apply (mem_hierarchyStates _ _ _).mpr
    refine ⟨List.length_replicate, ?_⟩
    intro c hc
    have h := List.eq_of_mem_replicate hc
    subst c
    exact le_rfl
  simp only [trialExpression, sumExpressions_value, List.map_map,
    Function.comp_def, expressionValue, rationalExpression_value, branchSum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  congr 1
  apply hierarchyTable_value
  · intro cs hcs
    rw [tableLookup_map _ _ hcs]
  · exact chooseChildren_in_states hroot b hb

theorem trialExpression_eq_trialLog {L : ℕ} (leaf : A → List Code → Code) (a : A)
    (g : (Fin L → ℝ) → ℝ) (hleaf : ∀ ds, expressionValue (leaf a ds) = g (leafFields L ds))
    (root : Code) (ms : List ℚ) :
    expressionValue (trialExpression leaf a root ms L) =
      DilutedSpinGlass.trialLog ms.length
        (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
        (fun i => (ms.get i : ℝ)) g := by
  rw [trialExpression_value]
  have hg : (fun ds => expressionValue (leaf a ds)) = fun ds => g (leafFields L ds) :=
    funext hleaf
  rw [hg, listTrialLog_eq_finite, finiteTrialLog_eq]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PacketExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
local instance packetExpressionsRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def fieldExpression (cs : List Code) (i : ℕ) : Code :=
  rationalExpression (decodedRational (cs[i]?.getD .zero))

@[fun_prop] theorem fieldExpression_computable :
    Computable (fun p : List Code × ℕ => fieldExpression p.1 p.2) := by
  have hget : Computable (fun p : List Code × ℕ => p.1[p.2]?.getD Code.zero) :=
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
      (Primrec.const Code.zero)).to_comp
  unfold fieldExpression
  fun_prop

theorem fieldExpression_value (cs : List Code) (i : ℕ) :
    expressionValue (fieldExpression cs i) = (decodedRational (cs[i]?.getD .zero) : ℝ) := by
  exact rationalExpression_value _

attribute [local irreducible] fieldExpression edgeExpression siteExpression trialExpression

noncomputable def fieldVector (k : ℕ) (cs : List Code) : Fin k → Code :=
  fun i => fieldExpression cs i.val

@[fun_prop] theorem fieldVector_computable (k : ℕ) : Computable (fieldVector k) := by
  apply computable_fin_lambda
  intro i
  exact fieldExpression_computable.comp (Computable.id.pair (Computable.const i.val))

attribute [local irreducible] fieldVector

noncomputable def edgeLeaf (p : ℚ × (Fin 3 → Bool)) (cs : List Code) : Code :=
  edgeExpression p.1 p.2 (fieldVector 3 cs)

attribute [local irreducible] edgeLeaf

@[fun_prop] theorem edgeLeaf_computable :
    Computable (fun p : (ℚ × (Fin 3 → Bool)) × List Code => edgeLeaf p.1 p.2) := by
  have hf := (fieldVector_computable 3).comp
    (show Computable (fun p : (ℚ × (Fin 3 → Bool)) × List Code => p.2) from Computable.snd)
  unfold edgeLeaf
  exact edgeExpression_comp _ _ _ (by fun_prop) (by fun_prop) hf

noncomputable def edgeTrialExpression (β : ℚ) (J : Fin 3 → Bool)
  (root : Code) (ms : List ℚ) : Code := trialExpression edgeLeaf (β,J) root ms 3

@[fun_prop] theorem edgeTrialExpression_computable :
    Computable (fun p : ℚ × (Fin 3 → Bool) × Code × List ℚ =>
      edgeTrialExpression p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ht := trialExpression_computable edgeLeaf edgeLeaf_computable
  unfold edgeTrialExpression
  exact ht.comp (g := fun p : ℚ × (Fin 3 → Bool) × Code × List ℚ =>
    ((p.1,p.2.1),p.2.2.1,p.2.2.2,3)) (by fun_prop)

noncomputable def siteData (signs : List (Fin 3 → Bool)) (cs : List Code) :
    List SiteExpressionDatum :=
  (List.range signs.length).map (fun j =>
    (signs[j]?.getD (fun _ => false), fun i : Fin 2 => fieldExpression cs (2*j+i.val)))

attribute [local irreducible] siteData

@[fun_prop] theorem siteData_computable :
    Computable (fun p : List (Fin 3 → Bool) × List Code => siteData p.1 p.2) := by
  have hget : Computable (fun p : List (Fin 3 → Bool) × ℕ =>
      p.1[p.2]?.getD (fun _ => false)) :=
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
      (Primrec.const (fun _ : Fin 3 => false))).to_comp
  unfold siteData
  apply computable_list_map
    (f := fun p : List (Fin 3 → Bool) × List Code => List.range p.1.length)
    (g := fun p j => (p.1[j]?.getD (fun _ => false),
      fun i : Fin 2 => fieldExpression p.2 (2*j+i.val))) (by fun_prop)
  unfold Computable₂
  apply Computable.pair
  · exact hget.comp (g := fun p : (List (Fin 3 → Bool) × List Code) × ℕ =>
      (p.1.1,p.2)) ((Computable.fst.comp Computable.fst).pair Computable.snd)
  · apply computable_fin_lambda
    intro i
    exact fieldExpression_computable.comp
      (g := fun p : (List (Fin 3 → Bool) × List Code) × ℕ => (p.1.2,2*p.2+i.val))
      ((Computable.snd.comp Computable.fst).pair (by fun_prop))

theorem siteData_ofFn (signs : List (Fin 3 → Bool)) (cs : List Code) :
    siteData signs cs = List.ofFn (fun j : Fin signs.length =>
      (signs.get j, fun i : Fin 2 => fieldExpression cs (2*j.val+i.val))) := by
  apply List.ext_getElem
  · simp [siteData]
  · intro i hi hj
    have hi' : i < signs.length := by simpa only [List.length_ofFn] using hj
    simp [siteData, hi']

noncomputable def siteLeaf (p : ℚ × List (Fin 3 → Bool)) (cs : List Code) : Code :=
  siteExpression p.1 (siteData p.2 cs)

attribute [local irreducible] siteLeaf

@[fun_prop] theorem siteLeaf_computable :
    Computable (fun p : (ℚ × List (Fin 3 → Bool)) × List Code => siteLeaf p.1 p.2) := by
  have hd : Computable (fun p : (ℚ × List (Fin 3 → Bool)) × List Code =>
      siteData p.1.2 p.2) :=
    siteData_computable.comp
      (g := fun p : (ℚ × List (Fin 3 → Bool)) × List Code => (p.1.2,p.2))
      ((Computable.snd.comp Computable.fst).pair Computable.snd)
  have hb : Computable (fun p : (ℚ × List (Fin 3 → Bool)) × List Code => p.1.1) :=
    Computable.fst.comp Computable.fst
  unfold siteLeaf
  exact siteExpression_comp _ _ hb hd

theorem siteLeaf_value (p : ℚ × List (Fin 3 → Bool)) (cs : List Code) :
    expressionValue (siteLeaf p cs) =
      siteLog (fun j : Fin p.2.length => satSample (p.1 : ℝ) (p.2.get j)) 0
        (fun i => leafFields (p.2.length*2) cs (finProdFinEquiv i)) := by
  rw [siteLeaf, siteData_ofFn, siteExpression_ofFn_value]
  simp only [fieldExpression_value]
  have he : (fun i : Fin p.2.length × Fin 2 =>
      (decodedRational (cs[2*i.1.val+i.2.val]?.getD .zero) : ℝ)) =
      (fun i => leafFields (p.2.length*2) cs (finProdFinEquiv i)) := by
    funext i
    change (decodedRational (cs[2*i.1.val+i.2.val]?.getD .zero) : ℝ) =
      (decodedRational (cs[i.2.val+2*i.1.val]?.getD .zero) : ℝ)
    rw [Nat.add_comm (2*i.1.val)]
  rw [he]

noncomputable def siteTrialExpression (β : ℚ) (signs : List (Fin 3 → Bool))
    (root : Code) (ms : List ℚ) : Code :=
  trialExpression siteLeaf (β,signs) root ms (signs.length*2)

@[fun_prop] theorem siteTrialExpression_computable :
    Computable (fun p : ℚ × List (Fin 3 → Bool) × Code × List ℚ =>
      siteTrialExpression p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ht := trialExpression_computable siteLeaf siteLeaf_computable
  unfold siteTrialExpression
  exact ht.comp (g := fun p : ℚ × List (Fin 3 → Bool) × Code × List ℚ =>
    ((p.1,p.2.1),p.2.2.1,p.2.2.2,p.2.1.length*2)) (by fun_prop)

theorem siteTrialExpression_value (β : ℚ) (signs : List (Fin 3 → Bool))
    (root : Code) (ms : List ℚ) :
    expressionValue (siteTrialExpression β signs root ms) =
      trialLog ms.length (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
        (fun i => (ms.get i : ℝ))
          (siteLog (fun j : Fin signs.length => satSample (β : ℝ) (signs.get j)) 0) := by
  rw [siteTrialExpression, trialExpression_eq_trialLog siteLeaf (β,signs)
    (fun x => siteLog (fun j : Fin signs.length => satSample (β : ℝ) (signs.get j)) 0
      (fun i => x (finProdFinEquiv i)))
    (fun cs => siteLeaf_value (β,signs) cs)]
  exact trialLog_reindex finProdFinEquiv ms.length _ _ _

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_EffectiveSums
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PeriodicLattice.CertifiedReal

open Encodable Filter
open scoped Topology BigOperators
local instance effectiveSumsRatPrimcodable : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable

variable {A : Type*} [Primcodable A]

theorem Effective.sum_range {f : A → ℕ → ℝ}
    (hf : Effective (fun p : A × ℕ => f p.1 p.2))
    {m : A → ℕ} (hm : Computable m) :
    Effective (fun a => ∑ i ∈ Finset.range (m a), f a i) := by
  obtain ⟨q, hq, herror⟩ := hf
  apply of_enclosures
    (q := fun an => ∑ i ∈ Finset.range (m an.1), q ((an.1,i),an.2))
    (e := fun an => (m an.1 : ℚ)*qerror an.2)
  · apply computable_sum (hm.comp Computable.fst)
    unfold Computable₂
    fun_prop
  · fun_prop
  · intro a n
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, cast_qerror]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ Finset.range (m a), |f a i - (q ((a,i),n) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (m a), error n :=
        Finset.sum_le_sum (fun i _ => herror (a,i) n)
      _ = _ := by simp
  · intro a
    simpa only [Rat.cast_mul, Rat.cast_natCast, cast_qerror, mul_zero] using
      error_tendsto.const_mul (m a : ℝ)

theorem effective_limit {f : A → ℝ} {g : A → ℕ → ℝ}
    (hg : Effective (fun p : A × ℕ => g p.1 p.2))
    (tail : A × ℕ → ℚ) (htail : Computable tail)
    (hbound : ∀ a n, |f a - g a n| ≤ (tail (a,n) : ℝ))
    (hzero : ∀ a, Tendsto (fun n => (tail (a,n) : ℝ)) atTop (nhds 0)) :
    Effective f := by
  obtain ⟨q, hq, he⟩ := hg
  apply of_enclosures (q := fun an => q ((an.1,an.2),an.2))
    (e := fun an => tail an + qerror an.2)
  · fun_prop
  · fun_prop
  · intro a n
    simp only [Rat.cast_add, cast_qerror]
    exact (abs_sub_le _ _ _).trans (add_le_add (hbound a n) (he (a,n) n))
  · intro a
    simpa only [Rat.cast_add, cast_qerror, add_zero] using (hzero a).add error_tendsto

end PeriodicLattice.CertifiedReal

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonEvaluation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
local instance poissonEvaluationRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

theorem poisson_linear_tail (r : ℝ≥0) (f : ℕ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ k, |f k| ≤ C*((k : ℝ)+1)) (L : ℕ) :
    |(∫ k, f k ∂poissonMeasure r) -
      ∑ k ∈ Finset.range L, (Real.exp (-(r : ℝ))*(r : ℝ)^k/k.factorial)*f k| ≤
      C*Real.exp (3*(r : ℝ))/(2 : ℝ)^L := by
  let low : ℕ → ℝ := fun k => if k < L then f k else 0
  let high : ℕ → ℝ := fun k => if k < L then 0 else f k
  have hl : Integrable low (poissonMeasure r) :=
    poisson_linear_integrable r low hC (fun k => by
      dsimp only [low]
      split_ifs
      · exact hf k
      · simpa using mul_nonneg hC (by positivity : (0 : ℝ) ≤ (k : ℝ)+1))
  have hh : Integrable high (poissonMeasure r) :=
    poisson_linear_integrable r high hC (fun k => by
      dsimp only [high]
      split_ifs
      · simpa using mul_nonneg hC (by positivity : (0 : ℝ) ≤ (k : ℝ)+1)
      · exact hf k)
  have he : ∫ k, low k ∂poissonMeasure r =
      ∑ k ∈ Finset.range L, (Real.exp (-(r : ℝ))*(r : ℝ)^k/k.factorial)*f k := by
    rw [integral_poissonMeasure]
    rw [tsum_eq_sum (s := Finset.range L)]
    · apply Finset.sum_congr rfl
      intro k hk
      simp only [smul_eq_mul, low, ite_eq_left (Finset.mem_range.mp hk)]
    · intro k hk
      simp only [low, Finset.mem_range, not_lt] at hk ⊢
      simp [Nat.not_lt.mpr hk]
  have hs : f = fun k => low k + high k := by
    funext k
    dsimp [low, high]
    split_ifs <;> simp
  rw [← he, hs, integral_add hl hh, add_sub_cancel_left]
  apply (abs_integral_le_integral_abs).trans
  calc
    _ ≤ ∫ k : ℕ, C*(4 : ℝ)^k/(2 : ℝ)^L ∂poissonMeasure r := by
      apply integral_mono hh.abs
        (((poisson_power_integrable r (by norm_num : (0 : ℝ) ≤ 4)).const_mul C).div_const _)
      intro k
      dsimp only [high]
      split_ifs with hk
      · simp only [abs_zero]
        positivity
      · apply (hf k).trans
        apply (mul_le_mul_of_nonneg_left (nat_succ_le_two_pow_real k) hC).trans
        apply (le_div_iff₀ (by positivity)).mpr
        have hp : (2 : ℝ)^L ≤ (2 : ℝ)^k :=
          pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt hk)
        calc
          C*2^k*2^L ≤ C*2^k*2^k := mul_le_mul_of_nonneg_left hp (by positivity)
          _ = C*4^k := by rw [mul_assoc, ← mul_pow]; norm_num
    _ = _ := by
      rw [integral_div, integral_const_mul, poisson_power_integral r (by norm_num : (0 : ℝ) ≤ 4)]
      congr 2
      norm_num
      ring

@[fun_prop] theorem factorial_computable : Computable Nat.factorial := by
  have h := Computable.nat_rec (f := fun n : ℕ => n) (g := fun _ => (1 : ℕ))
    (h := fun _ p => (p.1+1)*p.2) Computable.id (Computable.const 1)
    (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun n => by induction n <;> simp_all [Nat.factorial_succ])

theorem effective_poisson_expectation {A : Type} [Primcodable A]
    (rate : A → ℚ) (hrate : Computable rate) (hnonneg : ∀ a, 0 ≤ rate a)
    (C : A → ℕ) (hC : Computable C) (f : A → ℕ → ℝ)
    (hf : PeriodicLattice.CertifiedReal.Effective (fun p : A × ℕ => f p.1 p.2))
    (hbound : ∀ a k, |f a k| ≤ (C a : ℝ)*((k : ℝ)+1)) :
    PeriodicLattice.CertifiedReal.Effective (fun a =>
      ∫ k, f a k ∂poissonMeasure ⟨rate a, by exact_mod_cast hnonneg a⟩) := by
  let rateNN : A → ℝ≥0 := fun a => ⟨rate a, by exact_mod_cast hnonneg a⟩
  let g : A → ℕ → ℝ := fun a L =>
    ∑ k ∈ Finset.range L, (Real.exp (-(rate a : ℝ))*(rate a : ℝ)^k/k.factorial)*f a k
  have ht : PeriodicLattice.CertifiedReal.Effective (fun p : A × ℕ =>
      (Real.exp (-(rate p.1 : ℝ))*(rate p.1 : ℝ)^p.2/p.2.factorial)*f p.1 p.2) := by
    have he := (PeriodicLattice.CertifiedReal.rational
      (show Computable (fun p : A × ℕ => -rate p.1) by fun_prop)).exp
    have hr := PeriodicLattice.CertifiedReal.rational
      (show Computable (fun p : A × ℕ => (rate p.1)^p.2/(p.2.factorial : ℚ)) by fun_prop)
    convert (he.mul hr).mul hf using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    push_cast
    ring
  have hg : PeriodicLattice.CertifiedReal.Effective (fun p : A × ℕ => g p.1 p.2) := by
    apply PeriodicLattice.CertifiedReal.Effective.sum_range (m := Prod.snd)
    · exact ht.comp (show Computable (fun p : (A × ℕ) × ℕ => (p.1.1,p.2)) by fun_prop)
    · exact Computable.snd
  let tail : A × ℕ → ℚ := fun p => (C p.1 : ℚ)*3^⌈3*rate p.1⌉₊/2^p.2
  apply PeriodicLattice.CertifiedReal.effective_limit hg tail
  · dsimp only [tail]
    fun_prop
  · intro a L
    have h := poisson_linear_tail (rateNN a) (f a) (Nat.cast_nonneg (C a)) (hbound a) L
    apply h.trans
    have hExp := exp_le_three_natCeil (3*rate a)
    change (C a : ℝ) * Real.exp (3*(rateNN a : ℝ))/(2 : ℝ)^L ≤ (tail (a,L) : ℝ)
    dsimp only [tail, rateNN]
    push_cast at hExp ⊢
    gcongr
    exact hExp
  · intro a
    dsimp only [tail]
    push_cast
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul
        ((C a : ℝ)*3^⌈3*rate a⌉₊)
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using h

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DisorderEnumeration
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
open scoped BigOperators Classical
local instance disorderEnumerationRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def averagedSiteExpression (β : ℚ) (root : Code) (ms : List ℚ) (k : ℕ) : Code :=
  .comp (rationalExpression ((8 : ℚ)^k)⁻¹)
    (sumExpressions ((words signAlphabet k).map (fun signs => siteTrialExpression β signs root ms)))

attribute [local irreducible] siteTrialExpression edgeTrialExpression

@[fun_prop] theorem averagedSiteExpression_computable :
    Computable (fun p : (ℚ × Code × List ℚ) × ℕ =>
      averagedSiteExpression p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hs : Computable (fun p : (ℚ × Code × List ℚ) × ℕ =>
      (words signAlphabet p.2).map (fun signs =>
        siteTrialExpression p.1.1 signs p.1.2.1 p.1.2.2)) := by
    apply computable_list_map (signWords_computable.comp Computable.snd)
    unfold Computable₂
    exact siteTrialExpression_computable.comp
      (g := fun p : ((ℚ × Code × List ℚ) × ℕ) × List (Fin 3 → Bool) =>
        (p.1.1.1,p.2,p.1.1.2.1,p.1.1.2.2)) (by fun_prop)
  unfold averagedSiteExpression
  fun_prop

theorem averagedSiteExpression_value (β : ℚ) (root : Code) (ms : List ℚ) (k : ℕ) :
    expressionValue (averagedSiteExpression β root ms k) =
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin 3 → Bool)).expect (fun signs =>
        trialLog ms.length (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
          (fun i => (ms.get i : ℝ)) (siteLog (fun j => satSample (β : ℝ) (signs j)) 0)) := by
  simp only [averagedSiteExpression, expressionValue, rationalExpression_value,
    sumExpressions_value, List.map_map, Function.comp_def, signAlphabet, sum_words]
  simp only [FiniteLaw.expect, FiniteLaw.uniform, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, Rat.cast_inv, Rat.cast_pow,
    Rat.cast_ofNat, ← Finset.mul_sum]
  norm_num
  apply Finset.sum_congr rfl
  intro J _
  rw [siteTrialExpression_value]
  simpa only [List.get_ofFn, List.get_eq_getElem, List.getElem_ofFn, Fin.cast] using
    trialLog_site_cast (List.length_ofFn (f := J)) (β : ℝ)
      (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
      (fun i => (ms.get i : ℝ)) J

noncomputable def averagedEdgeExpression (β : ℚ) (root : Code) (ms : List ℚ) : Code :=
  .comp (rationalExpression (1/8))
    (sumExpressions (signAlphabet.map (fun J => edgeTrialExpression β J root ms)))

@[fun_prop] theorem averagedEdgeExpression_computable :
    Computable (fun p : ℚ × Code × List ℚ => averagedEdgeExpression p.1 p.2.1 p.2.2) := by
  have hs : Computable (fun p : ℚ × Code × List ℚ =>
      signAlphabet.map (fun J => edgeTrialExpression p.1 J p.2.1 p.2.2)) := by
    apply computable_list_map (Computable.const signAlphabet)
    unfold Computable₂
    exact edgeTrialExpression_computable.comp
      (g := fun p : (ℚ × Code × List ℚ) × (Fin 3 → Bool) =>
        (p.1.1,p.2,p.1.2.1,p.1.2.2)) (by fun_prop)
  unfold averagedEdgeExpression
  fun_prop

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_TrialDisorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Nat.Partrec FiniteArithmetic
open scoped BigOperators NNReal Classical

noncomputable def packetSiteValue (β : ℚ) (root : Code) (ms : List ℚ) (k : ℕ) : ℝ :=
  expressionValue (averagedSiteExpression β root ms k)

noncomputable def packetEdgeValue (β : ℚ) (root : Code) (ms : List ℚ) : ℝ :=
  expressionValue (averagedEdgeExpression β root ms)

theorem packetSiteValue_bound {β : ℚ} (hβ : 0 ≤ β) (root : Code) (ms : List ℚ)
    (hm : ∀ i : Fin ms.length, 0 < ms.get i) (k : ℕ) :
    |packetSiteValue β root ms k| ≤ (β : ℝ)*(k : ℝ) := by
  rw [packetSiteValue, averagedSiteExpression_value]
  apply FiniteLaw.abs_expect_le
  intro J
  have hp : ∀ i : Fin ms.length, (0 : ℝ) < ms.get i := fun i => by exact_mod_cast hm i
  have hb := trial_site_bound ms.length (fun i => (ms.get i : ℝ)) hp
    (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
    (fun j => satSample (β : ℝ) (J j)) 0
  apply hb.trans
  simp only [abs_zero, zero_add, satSample]
  calc
    _ ≤ ∑ _j : Fin k, (β : ℝ) := Finset.sum_le_sum (fun j _ =>
      satInteraction_norm_le (by exact_mod_cast hβ) (J j))
    _ = _ := by simp [mul_comm]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_TrialDescriptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
local instance trialDescriptionsRatPrimcodable : Primcodable ℚ :=
  PeriodicLattice.RecursiveArithmetic.ratPrimcodable

theorem computable_list_all {A B : Type} [Primcodable A] [Primcodable B]
    {xs : A → List B} {test : A → B → Bool} (hxs : Computable xs) (htest : Computable₂ test) :
    Computable (fun a => (xs a).all (test a)) := by
  have ht : Computable (fun p : A × B => test p.1 p.2) := htest
  have h := computable_list_foldr hxs (Computable.const true)
    (h := fun a p => test a p.1 && p.2)
    (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun a => by induction xs a <;> simp_all)

@[fun_prop] theorem rationalAt_computable :
    Computable (fun p : List ℚ × ℕ => rationalAt p.1 p.2) :=
  (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
    (Primrec.const (0 : ℚ))).to_comp

@[fun_prop] theorem positiveExponents_computable : Computable positiveExponents := by
  apply computable_list_all Computable.id
  unfold Computable₂
  fun_prop

theorem positiveExponents_iff (ms : List ℚ) :
    positiveExponents ms = true ↔ ∀ i : Fin ms.length, 0 < ms.get i := by
  simp only [positiveExponents, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h i
    exact h _ (List.get_mem _ _)
  · intro h q hq
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hq
    exact h i

noncomputable def exponentCheck (ms : List ℚ) : Bool :=
  (List.range ms.length).all (fun i => decide (0 < rationalAt ms i ∧ rationalAt ms i < 1) &&
    (List.range ms.length).all (fun j => decide (j ≤ i ∨ rationalAt ms i < rationalAt ms j)))

attribute [local irreducible] rationalAt

@[fun_prop] theorem exponentCheck_computable : Computable exponentCheck := by
  have hi : Computable (fun ms : List ℚ => List.range ms.length) := by fun_prop
  have hj : Computable (fun p : List ℚ × ℕ =>
      (List.range p.1.length).all (fun j => decide (j ≤ p.2 ∨ rationalAt p.1 p.2 < rationalAt p.1 j))) := by
    apply computable_list_all (by fun_prop)
    unfold Computable₂
    fun_prop
  unfold exponentCheck
  apply computable_list_all hi
  unfold Computable₂
  fun_prop

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_EffectiveTrialValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Nat.Partrec FiniteArithmetic
open PeriodicLattice.CertifiedReal RapidForcing.EffectiveArithmetic
open scoped NNReal
local instance effectiveTrialValuesRatPrimcodable : Primcodable ℚ :=
  PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def guardedSiteExpression (t : TrialData) (k : ℕ) : Code :=
  if positiveExponents t.2.2.2 then
    averagedSiteExpression (t.2.1 : ℚ) t.2.2.1 t.2.2.2 k else .zero

attribute [local irreducible] averagedSiteExpression averagedEdgeExpression positiveExponents

@[fun_prop] theorem guardedSiteExpression_computable :
    Computable (fun p : TrialData × ℕ => guardedSiteExpression p.1 p.2) := by
  have he : Computable (fun p : TrialData × ℕ =>
      averagedSiteExpression (p.1.2.1 : ℚ) p.1.2.2.1 p.1.2.2.2 p.2) :=
    averagedSiteExpression_computable.comp
      (g := fun p : TrialData × ℕ => (((p.1.2.1 : ℚ),p.1.2.2.1,p.1.2.2.2),p.2))
      (by fun_prop)
  unfold guardedSiteExpression
  fun_prop

noncomputable def guardedSiteValue (t : TrialData) (k : ℕ) : ℝ :=
  expressionValue (guardedSiteExpression t k)

theorem guardedSiteValue_effective : Effective (fun p : TrialData × ℕ => guardedSiteValue p.1 p.2) :=
  expressionValue_effective.comp guardedSiteExpression_computable

theorem guardedSiteValue_bound (t : TrialData) (k : ℕ) :
    |guardedSiteValue t k| ≤ (t.2.1 : ℝ)*((k : ℝ)+1) := by
  unfold guardedSiteValue guardedSiteExpression
  split_ifs with h
  · have hp := (positiveExponents_iff t.2.2.2).mp h
    apply (packetSiteValue_bound (β := (t.2.1 : ℚ)) (by positivity)
      t.2.2.1 t.2.2.2 hp k).trans
    push_cast
    nlinarith [show (0 : ℝ) ≤ t.2.1 from Nat.cast_nonneg _]
  · simp only [expressionValue, abs_zero]
    positivity

noncomputable def trialRate (t : TrialData) : ℚ := 3 * max 0 t.1

@[fun_prop] theorem trialRate_computable : Computable trialRate := by
  unfold trialRate
  fun_prop

theorem trialRate_nonneg (t : TrialData) : 0 ≤ trialRate t := by
  unfold trialRate
  positivity

noncomputable def trialDensityNN (t : TrialData) : ℝ≥0 :=
  ⟨(max 0 t.1 : ℚ), by exact_mod_cast le_max_left (0 : ℚ) t.1⟩

noncomputable def trialValue (t : TrialData) : ℝ :=
  Real.log 2 +
    (∫ k, guardedSiteValue t k ∂poissonMeasure (trialDensityNN t * 3)) -
      2*(max 0 t.1 : ℚ)*packetEdgeValue (t.2.1 : ℚ) t.2.2.1 t.2.2.2

attribute [local irreducible] guardedSiteValue packetEdgeValue

theorem siteExpectation_effective : Effective (fun t : TrialData =>
    ∫ k, guardedSiteValue t k ∂poissonMeasure (trialDensityNN t * 3)) := by
  have hs := effective_poisson_expectation trialRate trialRate_computable trialRate_nonneg
    (fun t : TrialData => t.2.1) (by fun_prop) guardedSiteValue
    guardedSiteValue_effective guardedSiteValue_bound
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  congr 1
  congr 1
  apply Subtype.ext
  change ((max 0 t.1 : ℚ) : ℝ)*3 = ((3*max 0 t.1 : ℚ) : ℝ)
  push_cast
  ring

theorem edgePacket_effective :
    Effective (fun t : TrialData => packetEdgeValue (t.2.1 : ℚ) t.2.2.1 t.2.2.2) := by
  simpa only [packetEdgeValue] using expressionValue_effective.comp
    (averagedEdgeExpression_computable.comp
      (g := fun t : TrialData => ((t.2.1 : ℚ),t.2.2.1,t.2.2.2)) (by fun_prop))

theorem trialValue_effective : Effective trialValue := by
  have hlog : Effective (fun _t : TrialData => Real.log 2) :=
    (rational (Computable.const (2 : ℚ))).log (fun _ => by norm_num)
  have ha : Effective (fun t : TrialData => ((2*(max 0 t.1) : ℚ) : ℝ)) :=
    rational (by fun_prop)
  apply ((hlog.add siteExpectation_effective).sub (ha.mul edgePacket_effective)).congr
  intro t
  simp only [trialValue, Rat.cast_mul, Rat.cast_ofNat]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_UpperCertificates
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology
open RapidForcing.EffectiveArithmetic

structure TrialEvaluation where
  density : ℕ → ℚ
  valid : ℕ → Bool
  value : ℕ → ℝ
  approximate : ℕ × ℕ → ℚ
  density_computable : Computable density
  valid_computable : Computable valid
  approximate_computable : Computable approximate
  density_positive : ∀ j, valid j = true → 0 < density j
  approximation_error : ∀ j s, valid j = true →
    |(approximate (j, s) : ℝ) - value j| ≤ (tolerance s : ℝ)

def TrialEvaluation.certified (T : TrialEvaluation) (n : ℕ) : Bool :=
  decide (T.valid n.unpair.1 = true ∧
    T.approximate (n.unpair.1, n.unpair.2) + tolerance n.unpair.2 < 0)

def TrialEvaluation.upper (T : TrialEvaluation) (n : ℕ) : ℚ :=
  T.density n.unpair.1

structure TrialSeparation (T : TrialEvaluation) (α : ℝ) : Prop where
  sound : ∀ j, T.valid j = true → T.value j < 0 → α ≤ (T.density j : ℝ)
  complete : ∀ a : ℚ, α < (a : ℝ) →
    ∃ j, T.valid j = true ∧ T.density j = a ∧ T.value j < 0

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CompiledTrials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec PeriodicLattice.CertifiedReal
open scoped NNReal

local instance compiledTrialsRatPrimcodable : Primcodable ℚ :=
  PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def decodeTrial (j : ℕ) : TrialData :=
  (Encodable.decode j).getD (0,0,.zero,[])

@[fun_prop] theorem decodeTrial_computable : Computable decodeTrial := by
  unfold decodeTrial
  fun_prop

noncomputable def trialDataValid (t : TrialData) : Bool :=
  decide (0 < t.1 ∧ 0 < t.2.1) && exponentCheck t.2.2.2

@[fun_prop] theorem trialDataValid_computable : Computable trialDataValid := by
  unfold trialDataValid
  fun_prop

theorem trialDataValid_iff (t : TrialData) : trialDataValid t = true ↔
    0 < t.1 ∧ 0 < t.2.1 ∧ exponentCheck t.2.2.2 = true := by
  simp only [trialDataValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

noncomputable def trialApproximation : TrialData × ℕ → ℚ :=
  Classical.choose trialValue_effective

theorem trialApproximation_computable : Computable trialApproximation :=
  (Classical.choose_spec trialValue_effective).1

theorem trialApproximation_error (t : TrialData) (s : ℕ) :
    |trialValue t - (trialApproximation (t,s) : ℝ)| ≤ error s :=
  (Classical.choose_spec trialValue_effective).2 t s

noncomputable def satTrialEvaluation : TrialEvaluation where
  density j := (decodeTrial j).1
  valid j := trialDataValid (decodeTrial j)
  value j := trialValue (decodeTrial j)
  approximate p := trialApproximation (decodeTrial p.1, 2^p.2)
  density_computable := by fun_prop
  valid_computable := by fun_prop
  approximate_computable := trialApproximation_computable.comp (by fun_prop)
  density_positive j hj := ((trialDataValid_iff _).mp hj).1
  approximation_error j s _ := by
    rw [abs_sub_comm]
    apply (trialApproximation_error _ _).trans
    simp only [error, tolerance, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat]
    rw [one_div]
    apply inv_anti₀ (by positivity)
    push_cast
    exact le_add_of_nonneg_right (by norm_num)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_LowerProgram
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter RapidForcing.EffectiveArithmetic
open scoped Topology

def lowerProgram (C N s : ℕ) : ℚ :=
  rationalCenter ((N + s + 1)^12) 3 - (C : ℚ) / (s + 1)

attribute [local irreducible] rationalCenter

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MaskPermutations
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

noncomputable section

local instance maskPermutationsDecidableEq (n : ℕ) : DecidableEq (DeletionCandidate n) :=
  Classical.decEq _

def candidatePermutation {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (DeletionCandidate n) where
  toFun x v := x (e.symm v)
  invFun x v := x (e v)
  left_inv x := by funext v; simp
  right_inv x := by funext v; simp

def literalPermutation {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (SignedLiteral n) :=
  e.prodCongr (Equiv.refl Bool)

noncomputable def renameMask {n : ℕ} (e : Equiv.Perm (Fin n))
    (U : Finset (DeletionCandidate n)) : Finset (DeletionCandidate n) :=
  U.image (candidatePermutation e)

def clausePermutation {n : ℕ} (e : Equiv.Perm (Fin n)) (k : ℕ) :
    Equiv.Perm (Fin k → SignedLiteral n) where
  toFun c j := literalPermutation e (c j)
  invFun c j := (literalPermutation e).symm (c j)
  left_inv c := by funext j; exact (literalPermutation e).symm_apply_apply _
  right_inv c := by funext j; exact (literalPermutation e).apply_symm_apply _

end

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonSATProbability
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology Classical

noncomputable def auxiliaryPoissonProbability (n : ℕ) (a : ℝ≥0) : ℝ :=
  ∫ m : ℕ, auxiliaryProbability n 3 m ∂poissonMeasure (a*n)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SupercriticalEnergy
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped NNReal Topology

noncomputable def deletionLifetimeMean (n r : ℕ) [NeZero n] : ℝ :=
  (FiniteLaw.pi (fun _ : Fin (20*n) => candidateBlock (n := n) 1 3 Finset.univ)).expect
    (maskLifetime (20*n) (deletionBudgetMask n r))

end FixedClauseThreshold.Computability

end OAI
end


