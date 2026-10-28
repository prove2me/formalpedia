-- Prove2me | Definitions.Def_OAIQ067A001
-- name    : OAIQ067A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:17:47.801646+00:00
-- url     : https://prove2.me/theorems/b0387aea-c4fe-4f06-a3bb-1d189e6eda1a
-- title:
--   Definitions bundle OAIQ067A001 of the split of OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 149 declarations of OpenAI's Lean: 91 definitions, 1 inductive type or structure, 7 instances and 50 theorems. The definitions and types are `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.clausePenalty`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.extendSpins`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.InterpolationAdmissible`, `OAI.FixedClauseThreshold.Computability.RationalTree`, `OAI.FixedClauseThreshold.Computability.RationalWeights`, `OAI.FixedClauseThreshold.Computability.RationalWeights.toAtomic`, `OAI.FixedClauseThreshold.Computability.RationalWeights.toLaw`, `OAI.FixedClauseThreshold.Computability.RelaxedClause`, `OAI.FixedClauseThreshold.Computability.TrialData`, `OAI.FixedClauseThreshold.Computability.UnitExponents`, `OAI.FixedClauseThreshold.Computability.allowedDeletions`, `OAI.FixedClauseThreshold.Computability.bestDeletionTime`, `OAI.FixedClauseThreshold.Computability.branchSum`, `OAI.FixedClauseThreshold.Computability.clauseAlphabet`, `OAI.FixedClauseThreshold.Computability.clauseAtomRate`, `OAI.FixedClauseThreshold.Computability.clauseHolds`, `OAI.FixedClauseThreshold.Computability.clauseMinimum`, `OAI.FixedClauseThreshold.Computability.clauseWords`, `OAI.FixedClauseThreshold.Computability.codeAlphabet`, `OAI.FixedClauseThreshold.Computability.countsMask`, `OAI.FixedClauseThreshold.Computability.deletionMomentConstant`, `OAI.FixedClauseThreshold.Computability.deletionSatisfiable`, `OAI.FixedClauseThreshold.Computability.deletionSlope`, `OAI.FixedClauseThreshold.Computability.dyadicBlock`, `OAI.FixedClauseThreshold.Computability.dyadicLevel`, `OAI.FixedClauseThreshold.Computability.dyadicLifetimeBound`, `OAI.FixedClauseThreshold.Computability.dyadicMomentCoefficient`, `OAI.FixedClauseThreshold.Computability.dyadicMultiplicity`, `OAI.FixedClauseThreshold.Computability.dyadicTruncation`, `OAI.FixedClauseThreshold.Computability.encodeBranches`, `OAI.FixedClauseThreshold.Computability.enumeratedProbability`, `OAI.FixedClauseThreshold.Computability.exponentContinuityMeasurable`, `OAI.FixedClauseThreshold.Computability.exponentTail`, `OAI.FixedClauseThreshold.Computability.finiteKernelStep`, `OAI.FixedClauseThreshold.Computability.finiteLogMean`, `OAI.FixedClauseThreshold.Computability.finiteMap`, `OAI.FixedClauseThreshold.Computability.finitePushforward`, `OAI.FixedClauseThreshold.Computability.finiteTrialEvaluationMeasurable`, `OAI.FixedClauseThreshold.Computability.finiteTrialLog`, `OAI.FixedClauseThreshold.Computability.formulaHolds` and 52 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `PeriodicLattice_Arithmetic`, `PeriodicLattice_TorusDerivatives`, `RandomSAT_Binomial`, `RandomSAT_CenterBounds`, `RandomSAT_Clauses`, `RandomSAT_Convergence`, `RandomSAT_Interpolation`, `RandomSAT_Replacement`, `RandomSAT_Transfer`, `RapidForcing_ArithmeticAutomation`, `RapidForcing_ExprCoding`, `RapidForcing_FormulaPrograms`, `RapidForcing_RawMachine`, `RapidForcing_SyntaxComputable`, `RapidForcing_TypedPrograms`, `SATComputability_CavityExpressions`, `SATComputability_CertificateSearch`, `SATComputability_DeletionIncrement`, `SATComputability_DeletionScaling`, `SATComputability_DisorderEnumeration`, `SATComputability_DyadicBlocks`, `SATComputability_DyadicMoment`, `SATComputability_EffectiveTrialValues`, `SATComputability_ExponentContinuity`, `SATComputability_FiniteEnumeration`, `SATComputability_FinitePushforward`, `SATComputability_FiniteTrialEvaluation`, `SATComputability_HierarchyBounds`, `SATComputability_HierarchyEncoding`, `SATComputability_HierarchyExpectation`, `SATComputability_HierarchyProgram`, `SATComputability_HierarchyTable`, `SATComputability_IncidentMasks`, `SATComputability_IncidentRates`, `SATComputability_InterpolationInputs`, `SATComputability_MarkovOccupation`, `SATComputability_PoissonCountProducts`, `SATComputability_PoissonEvaluation`, `SATComputability_PoissonKernel`, `SATComputability_PoissonKilling`, `SATComputability_PoissonMaskCounts`, `SATComputability_RationalHierarchy`, `SATComputability_RationalWeights`, `SATComputability_RelaxedEnergy`, `SATComputability_RelaxedPressure`, `SATComputability_RootEnergy`, `SATComputability_SATModel`, `SATComputability_SATVariational`, `SATComputability_SignLaw`, `SATComputability_SignMoment`, `SATComputability_TrialDescriptions`, `SATComputability_UniformDelayConstant`, `SATComputability_UniformFreeMoment`, `SATComputability_VariableDeletion`.
--
--   **Imports.** It imports the published bundles `Def_DilutedSpin`, `Def_OAIQ041D000` and `Def_SATComputability`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ067A002`, `OAIQ067A003`, `OAIQ067A004` and `OAIQ067A005`; the statements `OAI_DilutedSpinGlass_ConcreteReservoir_scoreError_tendsto`, `OAI_DilutedSpinGlass_PhysicalRoot_normalizedParameterError_tendsto`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_conditional_replacement_firstMoment_sat`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField_sat`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedLog_combination_nonpos_sat`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoisson_cavity_separable_sat`, `OAI_FixedClauseThreshold_Computability_auxiliaryPoissonProbability_supercritical`, `OAI_FixedClauseThreshold_Computability_exists_lowerProgram`, `OAI_FixedClauseThreshold_Computability_threshold_program`, `OAI_FixedClauseThreshold_limitingCenter_bounds`, `OAI_FixedClauseThreshold_limitingCenter_pos` and `OAI_FixedClauseThreshold_subcritical_limit`; the proofs of `OAI_DilutedSpinGlass_HeterogeneousMarks_independentInsertion_tail`, `OAI_DilutedSpinGlass_HeterogeneousMarks_sameInsertionAverage_tail`, `OAI_DilutedSpinGlass_PrescribedTree_marker_history_joint`, `OAI_DilutedSpinGlass_PrescribedTree_matrixHistory_first_pair`, `OAI_DilutedSpinGlass_PrescribedTree_matrix_three_copy_pointwise`, `OAI_DilutedSpinGlass_PrescribedTree_root_matrix_three_copy`, `OAI_DilutedSpinGlass_ReducedTopology_root_averaged_projectionShiftError_le`, `OAI_DilutedSpinGlass_ReducedTopology_scheduledMarkerDefect_covariance`, `OAI_DilutedSpinGlass_ReducedTopology_scheduled_root_multileaf`, `OAI_DilutedSpinGlass_UniversalDictionary_FullShapeControl_singleton_regular`, `OAI_DilutedSpinGlass_UniversalDictionary_integrable_rootHistory`, `OAI_DilutedSpinGlass_UniversalDictionary_regular_node_pointwise`, `OAI_DilutedSpinGlass_UniversalDictionary_reservoirShapeError_tendsto`, `OAI_DilutedSpinGlass_UniversalDictionary_rootHistory_polarization`, `OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_datumRoot_conditional_replacement_firstMoment`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_conditional_replacement_firstMoment_sat`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField_sat`, `OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_integral_mixedLog_combination_nonpos`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedLog_combination_nonpos_sat`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoisson_cavity_separable_sat`, `OAI_FixedClauseThreshold_Computability_auxiliaryPoissonProbability_supercritical`, `OAI_FixedClauseThreshold_limitingCenter_bounds`, `OAI_FixedClauseThreshold_limitingCenter_pos`, `OAI_FixedClauseThreshold_properSATProbability_center_lower`, `OAI_FixedClauseThreshold_properSATProbability_center_upper` and `OAI_FixedClauseThreshold_subcritical_limit`.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_SATComputability

section
-- module Solutions.OAIQ067_SAT.PeriodicLattice_TorusDerivatives
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation derivatives and smooth periodic lifts. -/

namespace PeriodicLattice

noncomputable section

namespace TorusCalculus

open scoped ContDiff Topology
open Filter Set _root_.MeasureTheory

@[simp] theorem single_zero (i : Fin 3) : EuclideanSpace.single i (0 : ℝ) = 0 := by
  ext j
  simp only [PiLp.single_apply, PiLp.zero_apply]
  split <;> rfl

end TorusCalculus

end
end PeriodicLattice

end OAI
end

section
-- module Solutions.OAIQ067_SAT.PeriodicLattice_Arithmetic
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
namespace RecursiveArithmetic
@[fun_prop] theorem nat_mod : Primrec (fun p : ℕ × ℕ => p.1 % p.2) := Primrec.nat_mod
@[fun_prop] theorem nat_max : Primrec (fun p : ℕ × ℕ => max p.1 p.2) := Primrec.nat_max
@[fun_prop] theorem natSucc : Primrec Nat.succ := Primrec.succ

@[fun_prop] theorem list_cons {α : Type*} [Primcodable α] :
    Primrec (fun p : α × List α => p.1 :: p.2) := Primrec.list_cons

@[fun_prop] theorem list_append {α : Type*} [Primcodable α] :
    Primrec (fun p : List α × List α => p.1 ++ p.2) := Primrec.list_append

@[fun_prop] theorem natListSum : Primrec (List.sum : List ℕ → ℕ) :=
  (Primrec.list_foldr Primrec.id (Primrec.const 0) (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    (fun l => by dsimp only; induction l <;> simp_all)

@[fun_prop] theorem natListProd : Primrec (List.prod : List ℕ → ℕ) :=
  (Primrec.list_foldr Primrec.id (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    (fun l => by dsimp only; induction l <;> simp_all)

end RecursiveArithmetic

namespace RecursiveArithmetic
@[fun_prop] theorem bool_cond {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Bool} {f g : α → β} (hp : Primrec p) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => if p a then f a else g a) :=
  (Primrec.cond hp hf hg).of_eq (fun a => by cases p a <;> rfl)

@[fun_prop] theorem listMap {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → List β} {g : α × β → γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).map (fun b => g (a,b))) := Primrec.list_map hf hg

@[fun_prop] theorem listFlatMap {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → List β} {g : α × β → List γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).flatMap (fun b => g (a,b))) := Primrec.list_flatMap hf hg
end RecursiveArithmetic

namespace RecursiveArithmetic
@[fun_prop] theorem listLength {α : Type*} [Primcodable α] : Primrec (List.length : List α → ℕ) :=
  Primrec.list_length

@[fun_prop] theorem sumRange {α : Type*} [Primcodable α] {f : α → ℕ} {g : α → ℕ → ℕ}
    (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => ∑ i ∈ Finset.range (f a), g a i) := by
  have hh := natListSum.comp (Primrec.list_map (Primrec.list_range.comp hf) hg)
  exact hh.of_eq (fun a => by simpa only [List.toFinset_range] using (List.sum_toFinset (g a) List.nodup_range).symm)
end RecursiveArithmetic

end
end PeriodicLattice

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Clauses
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

def frozenCoordinates {n : ℕ} (S : Finset (Assignment n)) (σ₀ : Assignment n) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ σ ∈ S, σ i = σ₀ i

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Replacement
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

def killFraction (b n r : ℕ) : ℝ := (b.choose r : ℝ) / ((n.choose r : ℝ) * 2 ^ r)

@[simp] theorem killFraction_zero (b n : ℕ) : killFraction b n 0 = 1 := by
  simp [killFraction]

def replacementScale (n k : ℕ) : ℝ := (n : ℝ) ^ (1 / (k : ℝ))

def replacementError (n k : ℕ) : ℝ := (replacementScale n k)⁻¹ ^ (k - 1)

def replacementBlock (n k : ℕ) : ℕ := ⌈2 * (k : ℝ) * replacementScale n k⌉₊

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Binomial
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite Bernoulli-count expectations and integrated telescoping estimates.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def binomialMean (p : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, f => f 0
  | m + 1, f => (1 - p) * binomialMean p m f +
      p * binomialMean p m (fun d => f (d + 1))

def replacementDifference (P : ℕ → ℝ) (g j d : ℕ) : ℝ :=
  P (j - d) - P (j + (g - 1) * d)

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_CenterBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

def firstMomentBase : ℝ := 2 * Real.exp (-1)

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Interpolation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

def mixedAverage {X : Type*} (p : ℝ) (A B : (X → ℝ) → (X → ℝ))
    (f : X → ℝ) : X → ℝ := fun S => (1 - p) * B f S + p * A f S

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Transfer
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The exact probability of distinct variables, birthday bounds, and deletion and
thinning comparisons transfer auxiliary probabilities to the proper-clause law.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def properFraction (n k : ℕ) : ℝ := (n.descFactorial k : ℝ) / (n : ℝ)^k

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Convergence
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A balanced-block geometric potential proves convergence from boundedness and
summable-min comparisons, including block counts that are not powers of two.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def balanceConstant (β : ℝ) : ℝ := (3 : ℝ)^β / ((3 / 2 : ℝ)^β - 1)

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_ArithmeticAutomation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
@[fun_prop] lemma primrec_nat_div : Primrec (fun p : ℕ × ℕ => p.1 / p.2) := Primrec.nat_div
@[fun_prop] lemma primrec_nat_max : Primrec (fun p : ℕ × ℕ => max p.1 p.2) := Primrec.nat_max
@[fun_prop] lemma primrec_nat_min : Primrec (fun p : ℕ × ℕ => min p.1 p.2) := Primrec.nat_min

@[fun_prop] lemma primrec_factorial : Primrec Nat.factorial := by
  exact (Primrec.nat_rec' Primrec.id (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
        (fun n => by
          change Nat.rec 1 (fun j IH => (j + 1) * IH) n = n.factorial
          induction n <;> simp [Nat.factorial, *])

end RapidForcing.EffectiveArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_ExprCoding
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open Encodable Denumerable Nat.Partrec
namespace RapidForcing.EffectiveArithmetic

attribute [fun_prop] Nat.Partrec.Code.primrec_rfind'
@[fun_prop] lemma primrec_code_ofNat : Primrec Code.ofNatCode := Primrec.ofNat Code

@[instance_reducible] def retractEncodable {A B : Type} [Encodable B] (f : A → B) (g : B → A)
    (h : Function.LeftInverse g f) : Encodable A := Encodable.ofLeftInverse f g h

@[instance_reducible] def primcodable_retract {A B : Type} [Primcodable B] (f : A → B) (g : B → A)
    (h : Function.LeftInverse g f) (hr : Primrec (fun b => f (g b))) :
    Primcodable A :=
  { toEncodable := retractEncodable f g h
    prim := by
      let := retractEncodable f g h
      have hp := Primrec.nat_iff.mp <| Primrec.encode.comp <|
        Primrec.option_map Primrec.decode (hr.comp Primrec.snd).to₂
      apply hp.of_eq
      intro n
      change encode ((decode (α := B) n).map (fun b => f (g b))) =
        @encode (Option A) _ ((decode (α := B) n).bind (some ∘ g))
      cases decode (α := B) n <;> rfl }

@[simp] lemma code_encode_ofNat (n : ℕ) : encode (Code.ofNatCode n) = n :=
  Denumerable.encode_ofNat (α := Code) n

end RapidForcing.EffectiveArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_TypedPrograms
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Encodable Nat.Partrec
namespace RapidForcing.EffectiveArithmetic

variable {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]

def runTyped (c : Code) (a : A) : Part B :=
  (c.eval (encode a)).bind (fun n => Part.ofOption (decode n))

end RapidForcing.EffectiveArithmetic

end

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

@[fun_prop] lemma computable_fin_app {S : Type} [Primcodable S] {d : ℕ} :
    Computable (fun p : (Fin d → S) × Fin d => p.1 p.2) := Computable.fin_app

lemma computable_fin_lambda {A S : Type} [Primcodable A] [Primcodable S] {d : ℕ}
    {f : A → Fin d → S} (hf : ∀ i, Computable (fun a => f a i)) : Computable f := by
  exact (Primrec.vector_get'.to_comp.comp (Computable.vector_ofFn hf)).of_eq
    (fun a => by ext i; simp)

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
@[fun_prop] lemma computable_fin_val {n : ℕ} : Computable (fun i : Fin n => i.val) := Primrec.fin_val.to_comp
end RapidForcing

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_SyntaxComputable
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Encodable
open scoped BigOperators
namespace RapidForcing.EffectiveArithmetic
@[fun_prop] lemma computable_fin_eval {S : Type} [Primcodable S] {d : ℕ} (i : Fin d) :
    Computable (fun f : Fin d → S => f i) := Computable.fin_app.comp Computable.id (Computable.const i)
end RapidForcing.EffectiveArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SATModel
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

def literalFactor (sign value : Bool) : ℝ := if value = sign then 0 else 1

noncomputable def satInteraction (β : ℝ) (J : Fin 3 → Bool) : Interaction 3 :=
  fun s => if ∀ l, s l ≠ J l then -β else 0

noncomputable def satSample (β : ℝ) (J : Fin 3 → Bool) : InteractionSample 3 :=
  (satInteraction β J, 1, Real.exp (-β) - 1, fun l => literalFactor (J l))

theorem satInteraction_norm_le {β : ℝ} (hβ : 0 ≤ β) (J : Fin 3 → Bool) :
    ‖satInteraction β J‖ ≤ β := by
  apply (pi_norm_le_iff_of_nonneg hβ).mpr
  intro s
  unfold satInteraction
  split <;> simp [Real.norm_eq_abs, abs_of_nonneg hβ, hβ]

noncomputable def signLaw : ProbabilityMeasure (Fin 3 → Bool) :=
  ⟨(PMF.uniformOfFintype (Fin 3 → Bool)).toMeasure, (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

noncomputable def satModel (a : ℝ≥0) (β : ℝ) : Model 3 where
  alpha := a
  disorder := signLaw.map (f := satSample β) (measurable_of_countable _).aemeasurable
  field := ⟨Measure.dirac 0, inferInstance⟩

def permuteSigns (e : Equiv.Perm (Fin 3)) : (Fin 3 → Bool) ≃ (Fin 3 → Bool) where
  toFun J := fun l => J (e.symm l)
  invFun J := fun l => J (e l)
  left_inv J := by funext l; simp
  right_inv J := by funext l; simp

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CavityExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Nat.Partrec DilutedSpinGlass RapidForcing.EffectiveArithmetic
open scoped BigOperators

def clausePenalty (β : ℚ) (J s : Fin 3 → Bool) : ℚ :=
  if ∀ i, s i ≠ J i then -β else 0

theorem sum_bool_vector_succ {p : ℕ} (f : (Fin (p+1) → Bool) → ℝ) :
    (∑ s, f s) =
      (∑ t : Fin p → Bool, f (Fin.cons false t)) +
      ∑ t : Fin p → Bool, f (Fin.cons true t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (p+1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  exact add_comm _ _

@[fun_prop] theorem spinsThree_computable :
    Computable (fun p : Bool × Bool × Bool => ![p.1,p.2.1,p.2.2]) := by
  apply computable_fin_lambda
  intro i
  fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals fun_prop

def extendSpins (a b ε : Bool) : Fin 3 → Bool := ![a,b,ε]

@[fun_prop] theorem extendSpins_computable :
    Computable (fun p : Bool × Bool × Bool => extendSpins p.1 p.2.1 p.2.2) :=
  spinsThree_computable

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

def tolerance (r : ℕ) : ℚ := (2 ^ r : ℚ)⁻¹

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_VariableDeletion
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset

def relaxedClauseSatisfied {n : ℕ} (s : Fin n → Bool)
    (indices : Fin 3 → Fin n) (signs : Fin 3 → Bool) : Prop :=
  ∃ l, s (indices l) = signs l

instance instDecidableRelaxedClauseSatisfied {n : ℕ} (s : Fin n → Bool) (indices : Fin 3 → Fin n)
    (signs : Fin 3 → Bool) : Decidable (relaxedClauseSatisfied s indices signs) := by
  unfold relaxedClauseSatisfied
  infer_instance

def relaxedViolations {n m : ℕ} (s : Fin n → Bool)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) : ℕ :=
  (univ.filter fun j => ¬relaxedClauseSatisfied s (indices j) (signs j)).card

def deletionSatisfiable {n m : ℕ} (r : ℕ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) : Prop :=
  ∃ D : Finset (Fin n), D.card ≤ r ∧ ∃ s : Fin n → Bool,
    ∀ j, (∃ l, indices j l ∈ D) ∨ relaxedClauseSatisfied s (indices j) (signs j)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DeletionIncrement
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset
open DilutedSpinGlass
open scoped BigOperators

def allowedDeletions (n r : ℕ) : Finset (Finset (Fin n)) :=
  univ.filter (fun D => D.card ≤ r)

theorem allowedDeletions_nonempty (n r : ℕ) : (allowedDeletions n r).Nonempty :=
  ⟨∅, by simp [allowedDeletions]⟩

noncomputable def bestDeletionTime {n : ℕ} (t : Finset (Fin n) → ℝ) (r : ℕ) : ℝ :=
  (allowedDeletions n r).sup' (allowedDeletions_nonempty n r) t

noncomputable def freeDeletionTime {n : ℕ} (t : Finset (Fin n) → ℝ)
    (r : ℕ) (v : Fin n) : ℝ :=
  (allowedDeletions n r).sup' (allowedDeletions_nonempty n r) (fun D => t (insert v D))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SignLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem uniformFiniteLaw_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] :
    (FiniteLaw.uniform : FiniteLaw (∀ i, A i)) =
      FiniteLaw.pi (fun i => (FiniteLaw.uniform : FiniteLaw (A i))) := by
  apply FiniteLaw.weights_ext
  intro x
  simp [FiniteLaw.uniform, FiniteLaw.pi, Fintype.card_pi, Nat.cast_prod,
    Finset.prod_inv_distrib]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_MarkovOccupation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators

noncomputable def finiteKernelStep {Ω : Type*} [Fintype Ω]
    (K : Ω → FiniteLaw Ω) (f : Ω → ℝ) (x : Ω) : ℝ := (K x).expect f

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonKilling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem poisson_power_integrable (r : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun m : ℕ => x^m) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have h := ((NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*x)).mul_left
    (Real.exp (-(r : ℝ)))).summable
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext m
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx m), mul_pow]
  ring

theorem poisson_power_integral (r : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    (∫ m : ℕ, x^m ∂poissonMeasure r) = Real.exp ((r : ℝ)*(x-1)) := by
  rw [integral_poissonMeasure' (poisson_power_integrable r hx)]
  have h := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*x)).mul_left
    (Real.exp (-(r : ℝ)))
  calc
    _ = ∑' m : ℕ, Real.exp (-(r : ℝ)) * (((r : ℝ)*x)^m / m.factorial) := by
      apply tsum_congr
      intro m
      simp only [smul_eq_mul, mul_pow]
      ring
    _ = Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ)*x) := by
      simpa only [← Real.exp_eq_exp_ℝ] using h.tsum_eq
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonKernel
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem finiteLaw_weight_le_one {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (x : Ω) :
    P.weight x ≤ 1 := by
  rw [← P.total]
  exact Finset.single_le_sum (fun y _ => P.nonneg y) (Finset.mem_univ x)

theorem poisson_weight_integrable {Ω : Type*} [Fintype Ω]
    (r : ℝ≥0) (P : ℕ → FiniteLaw Ω) (x : Ω) :
    Integrable (fun m => (P m).weight x) (poissonMeasure r) := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  exact Eventually.of_forall (fun m => abs_le.mpr
    ⟨by linarith [(P m).nonneg x], finiteLaw_weight_le_one (P m) x⟩)

noncomputable def poissonMixture {Ω : Type*} [Fintype Ω]
    (r : ℝ≥0) (P : ℕ → FiniteLaw Ω) : FiniteLaw Ω where
  weight x := ∫ m, (P m).weight x ∂poissonMeasure r
  nonneg x := integral_nonneg (fun m => (P m).nonneg x)
  total := by
    rw [← integral_finsetSum _ (fun x _ => poisson_weight_integrable r P x)]
    simp only [(P _).total, integral_const, probReal_univ, one_smul]

theorem poissonMixture_expect {Ω : Type*} [Fintype Ω]
    (r : ℝ≥0) (P : ℕ → FiniteLaw Ω) (f : Ω → ℝ) :
    (poissonMixture r P).expect f =
      ∫ m, (P m).expect f ∂poissonMeasure r := by
  simp only [FiniteLaw.expect, poissonMixture]
  rw [integral_finsetSum _ (fun x _ => (poisson_weight_integrable r P x).mul_const (f x))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_mul_const]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DyadicBlocks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

noncomputable def dyadicLevel (j : ℕ) : ℝ := ((2 : ℝ)^j)⁻¹
def dyadicTruncation (j : ℕ) : ℕ := j+122
def dyadicMultiplicity (j : ℕ) : ℕ := 2*(j+122)*2^((j+1)/2)
def dyadicBlock (j : ℕ) : ℕ := 32*dyadicTruncation j*dyadicMultiplicity j

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DyadicMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped BigOperators NNReal Topology

noncomputable def dyadicLifetimeBound (j : ℕ) : ℝ :=
  (4*(dyadicBlock j : ℝ)/dyadicLevel j)^(1/5 : ℝ)

noncomputable def dyadicMomentCoefficient (j : ℕ) : ℝ :=
  (dyadicLevel j)^2 * (4*(dyadicBlock j : ℝ)/dyadicLevel j)^(6/5 : ℝ)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_IncidentMasks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

noncomputable def finiteMap {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [DecidableEq Ξ] (P : FiniteLaw Ω) (f : Ω → Ξ) : FiniteLaw Ξ where
  weight y := P.expect (fun x => if f x = y then 1 else 0)
  nonneg y := P.expect_nonneg (fun x => by split_ifs <;> norm_num)
  total := by
    rw [← FiniteLaw.expect_fintype_sum]
    simp

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_FinitePushforward
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

theorem finite_indicator_integrable {X Y : Type*} [MeasurableSpace X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → Y) (hg : Measurable g) (y : Y) :
    Integrable (fun x => if g x = y then (1 : ℝ) else 0) μ := by
  apply Integrable.of_bound
    (((measurable_of_countable (fun z : Y => if z = y then (1 : ℝ) else 0)).comp hg).aestronglyMeasurable) 1
  filter_upwards [] with x
  dsimp only [Function.comp_def]
  split_ifs <;> norm_num

noncomputable def finitePushforward {X Y : Type*} [MeasurableSpace X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → Y) (hg : Measurable g) : FiniteLaw Y where
  weight y := ∫ x, if g x = y then 1 else 0 ∂μ
  nonneg y := integral_nonneg (fun x => by split_ifs <;> norm_num)
  total := by
    rw [← integral_finsetSum _ (fun y _ => finite_indicator_integrable μ g hg y)]
    simp

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonMaskCounts
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

noncomputable def zeroMask {X : Type*} [Fintype X] (z : X → ℝ) : Finset X :=
  Finset.univ.filter (fun x => z x = 0)

noncomputable def maskDefect {A X : Type*} [Fintype X]
    (mask : A → Finset X) (a : A) : X → ℝ :=
  fun x => if x ∈ mask a then 0 else 1

noncomputable def countsMask {A X : Type*} [Fintype A] [Fintype X]
    (mask : A → Finset X) (counts : A → ℕ) : Finset X :=
  Finset.univ.filter (fun x => ∀ a, counts a = 0 ∨ x ∈ mask a)

noncomputable def markedMaskLaw {A X : Type*} [Fintype A] [Nonempty A] [Fintype X]
    (r : ℝ≥0) (mask : A → Finset X) : FiniteLaw (Finset X) :=
  poissonMixture r (fun d => finiteMap (FiniteLaw.uniform : FiniteLaw (Fin d → A))
    (fun as => Finset.univ.filter (fun x => ∀ j, x ∈ mask (as j))))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PoissonCountProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

noncomputable def poissonCountLaw (A : Type*) [Fintype A] (r : ℝ≥0) : Measure (A → ℕ) :=
  Measure.pi (fun _ : A => poissonMeasure r)

instance poissonCountLaw_probability (A : Type*) [Fintype A] (r : ℝ≥0) :
    IsProbabilityMeasure (poissonCountLaw A r) := by unfold poissonCountLaw; infer_instance

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_UniformDelayConstant
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators NNReal

noncomputable def deletionMomentConstant : ℝ :=
  (48/5 : ℝ)*(∑' j, dyadicMomentCoefficient j) + (12/5 : ℝ)*(1200 : ℝ)^2

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_IncidentRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped NNReal

noncomputable def clauseAtomRate (n : ℕ) : ℝ≥0 := (8*((n+1 : ℕ) : ℝ≥0)^3)⁻¹

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_UniformFreeMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped NNReal Classical

noncomputable def uniformFreeConstant : ℝ := deletionMomentConstant + 400

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DeletionScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Filter
open scoped NNReal Topology

noncomputable def deletionSlope (q : ℕ) : ℝ :=
  6*uniformFreeConstant^(5/6 : ℝ)*((q : ℝ)⁻¹)^(1/6 : ℝ)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RationalWeights
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators

def RationalWeights (ι : Type*) [Fintype ι] :=
  {w : ι → ℚ // (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

noncomputable def RationalWeights.toLaw {ι : Type*} [Fintype ι]
    (w : RationalWeights ι) : FiniteLaw ι where
  weight i := w.val i
  nonneg i := by exact_mod_cast w.property.1 i
  total := by exact_mod_cast w.property.2

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RationalHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory Set Filter TopologicalSpace
open scoped Topology BigOperators NNReal

noncomputable def RationalWeights.toAtomic {ι : Type*} [Fintype ι]
    (w : RationalWeights ι) : AtomicWeights ι :=
  ⟨fun i => ⟨w.val i, by exact_mod_cast w.property.1 i⟩, by
    exact NNReal.coe_injective ((NNReal.coe_sum Finset.univ
      (fun i => (⟨(w.val i : ℝ), by exact_mod_cast w.property.1 i⟩ : ℝ≥0))).trans
        (by
          change (∑ i, (w.val i : ℝ)) = 1
          exact_mod_cast w.property.2))⟩

def RationalTree : ℕ → Type
  | 0 => ℚ
  | r+1 => Σ n : ℕ, RationalWeights (Fin n) × (Fin n → RationalTree r)

instance rationalWeightsEncodable (n : ℕ) : Encodable (RationalWeights (Fin n)) := by
  unfold RationalWeights
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

@[instance_reducible] def rationalTreeEncoding : (r : ℕ) → Encodable (RationalTree r)
  | 0 => Rat.instEncodable
  | r+1 => by
    letI := rationalTreeEncoding r
    exact inferInstanceAs (Encodable (Σ n : ℕ,
      RationalWeights (Fin n) × (Fin n → RationalTree r)))

instance rationalTreeEncodable (r : ℕ) : Encodable (RationalTree r) := rationalTreeEncoding r

local instance rationalHierarchyMeasurableSpace (space : TopCat) : MeasurableSpace space :=
  borel space

noncomputable def rationalTreeValue : (r : ℕ) → RationalTree r → Hierarchy r
  | 0, x => Rat.cast (K := ℝ) x
  | r+1, ⟨_, q, x⟩ => atomicProbability (fun i => rationalTreeValue r (x i)) q.toAtomic

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_FiniteTrialEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory
open scoped BigOperators

local instance finiteTrialEvaluationMeasurable (X : TopCat) : MeasurableSpace X := borel X
local instance finiteTrialEvaluationBorel (X : TopCat) : BorelSpace X := ⟨rfl⟩

noncomputable def finiteLogMean {ι : Type} [Fintype ι] :
    (r : ℕ) → ((ι → ℝ) → ℝ) → (Fin r → ℝ) → (ι → RationalTree r) → ℝ
  | 0, g, _, t => g (fun i => Rat.cast (K := ℝ) (t i))
  | r+1, g, m, t => by
    classical
    exact Real.log ((FiniteLaw.pi (fun i => (t i).2.1.toLaw)).expect (fun a =>
      Real.exp (m 0 * finiteLogMean r g (fun j => m j.succ) (fun i => (t i).2.2 (a i))))) / m 0

theorem rationalTreeValue_asProbability (r : ℕ) (t : RationalTree (r+1)) :
    rationalTreeValue (r+1) t =
      t.2.1.toLaw.asProbability (fun a => rationalTreeValue r (t.2.2 a)) := by
  rfl

noncomputable def finiteTrialLog {ι : Type} [Fintype ι] (r : ℕ)
    (t : RationalTree (r+1)) (m : Fin r → ℝ) (g : (ι → ℝ) → ℝ) : ℝ := by
  classical
  exact (FiniteLaw.pi (fun _ : ι => t.2.1.toLaw)).expect
    (fun a => finiteLogMean r g m (fun i => t.2.2 (a i)))

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

def words {α : Type*} (alphabet : List α) : ℕ → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun a => (words alphabet n).map (a :: ·)

theorem mem_words {α : Type*} (alphabet : List α) (n : ℕ) (w : List α) :
    w ∈ words alphabet n ↔ w.length = n ∧ ∀ a ∈ w, a ∈ alphabet := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w => simp [words, ih, and_assoc, and_left_comm]

theorem words_primrec {α : Type*} [Primcodable α] :
    Primrec₂ (@words α) := by
  have h := Primrec.nat_rec' (f := fun p : List α × ℕ => p.2)
    (g := fun _ => ([[]] : List (List α)))
    (h := fun p q => p.1.flatMap fun a => q.2.map (a :: ·))
    Primrec.snd (Primrec.const _) ?_
  · exact h.of_eq fun p => by
      induction p.2 <;> simp_all [words]
  · apply Primrec.list_flatMap (Primrec.fst.comp Primrec.fst)
    apply Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact Primrec.list_cons.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd

def clauseAlphabet : List (Option Bool) := [none, some false, some true]

def clauseWords (n k : ℕ) : List (List (Option Bool)) :=
  (words clauseAlphabet n).filter fun c => (c.filter Option.isSome).length = k

def formulaWords (n k m : ℕ) : List (List (List (Option Bool))) :=
  words (clauseWords n k) m

def clauseHolds (s : List Bool) (c : List (Option Bool)) : Prop :=
  ∃ i ∈ List.range s.length, c.getD i none = some (s.getD i false)

instance instDecidableClauseHolds (s : List Bool) (c : List (Option Bool)) : Decidable (clauseHolds s c) := by
  unfold clauseHolds
  infer_instance

def formulaHolds (s : List Bool) (f : List (List (Option Bool))) : Prop :=
  ∀ c ∈ f, clauseHolds s c

instance instDecidableFormulaHolds (s : List Bool) (f : List (List (Option Bool))) : Decidable (formulaHolds s f) := by
  unfold formulaHolds
  infer_instance

def formulaSatisfiable (n : ℕ) (f : List (List (Option Bool))) : Prop :=
  ∃ s ∈ words [false, true] n, formulaHolds s f

instance instDecidableFormulaSatisfiable (n : ℕ) (f : List (List (Option Bool))) : Decidable (formulaSatisfiable n f) := by
  unfold formulaSatisfiable
  infer_instance

def satisfiableWords (n k m : ℕ) : List (List (List (Option Bool))) :=
  (formulaWords n k m).filter (formulaSatisfiable n)

def enumeratedProbability (n k m : ℕ) : ℚ :=
  (satisfiableWords n k m).length / (formulaWords n k m).length

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

noncomputable def encodeBranches (bs : List (ℚ × Code)) : Code :=
  bs.foldr (fun b rest => .pair (.comp (ofNat Code (encode b.1)) b.2) rest) .zero

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

def codeAlphabet (bound : ℕ) : List Code :=
  (List.range (bound+1)).map (ofNat Code)

theorem mem_codeAlphabet (bound : ℕ) (c : Code) :
    c ∈ codeAlphabet bound ↔ encode c ≤ bound := by
  constructor
  · intro h
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h
    simpa only [List.mem_range, encode_ofNat, Nat.lt_succ_iff] using hn
  · intro h
    exact List.mem_map.mpr ⟨encode c, List.mem_range.mpr (Nat.lt_succ_iff.mpr h), ofNat_encode c⟩

def hierarchyStates (bound labels : ℕ) : List (List Code) := words (codeAlphabet bound) labels

theorem mem_hierarchyStates (bound labels : ℕ) (cs : List Code) :
    cs ∈ hierarchyStates bound labels ↔
      cs.length = labels ∧ ∀ c ∈ cs, encode c ≤ bound := by
  simp only [hierarchyStates, mem_words, mem_codeAlphabet]

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

theorem sum_flatMap_eq {A B : Type*} [AddMonoid B] (xs : List A) (f : A → List B) :
    (xs.flatMap f).sum = (xs.map (fun a => (f a).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons,
      List.sum_cons, ih]

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_HierarchyExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec
open scoped BigOperators

noncomputable def branchSum (bs : List (ℚ × List Code)) (f : List Code → ℝ) : ℝ :=
  (bs.map (fun b => (b.1 : ℝ) * f b.2)).sum

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
local instance hierarchyTableCodeEq : DecidableEq Code := Encodable.decidableEqOfEncodable Code
local instance hierarchyTableListBEq : BEq (List Code) := instBEqOfDecidableEq

end FixedClauseThreshold.Computability

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

theorem nat_succ_le_two_pow_real (k : ℕ) : (k : ℝ)+1 ≤ (2 : ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Nat.cast_succ, pow_succ]
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith

theorem poisson_linear_integrable (r : ℝ≥0) (f : ℕ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ k, |f k| ≤ C*((k : ℝ)+1)) :
    Integrable f (poissonMeasure r) := by
  apply Integrable.mono' ((poisson_power_integrable r (by norm_num : (0 : ℝ) ≤ 2)).const_mul C)
    (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with k
  rw [Real.norm_eq_abs]
  exact (hf k).trans (mul_le_mul_of_nonneg_left (nat_succ_le_two_pow_real k) hC)

theorem exp_le_three_natCeil (q : ℚ) :
    Real.exp (q : ℝ) ≤ (3 : ℝ)^⌈q⌉₊ := by
  have hceil : (q : ℝ) ≤ (⌈q⌉₊ : ℕ) := by exact_mod_cast (Nat.le_ceil q)
  calc
    _ ≤ Real.exp (⌈q⌉₊ : ℕ) := Real.exp_le_exp.mpr hceil
    _ = (Real.exp 1)^⌈q⌉₊ := by rw [← Real.exp_nat_mul]; simp
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le _

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_DisorderEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass Nat.Partrec FiniteArithmetic RapidForcing.EffectiveArithmetic
open scoped BigOperators Classical

noncomputable def signAlphabet : List (Fin 3 → Bool) := Finset.univ.toList

@[fun_prop] theorem signWords_computable :
    Computable (fun k => words signAlphabet k) :=
  words_primrec.to_comp.comp (Computable.const signAlphabet) Computable.id

theorem sum_words {A : Type} [Fintype A] [DecidableEq A] (k : ℕ)
    (f : List A → ℝ) :
    ((words (Finset.univ.toList : List A) k).map f).sum =
      ∑ x : Fin k → A, f (List.ofFn x) := by
  induction k generalizing f with
  | zero => simp [words]
  | succ k ih =>
    simp only [words, List.map_flatMap, sum_flatMap_eq, List.map_map, Function.comp_def]
    simp_rw [ih]
    rw [Finset.sum_map_toList, ← (Fin.consEquiv (fun _ : Fin (k+1) => A)).sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro x _
    rw [List.ofFn_succ]
    rfl

theorem trialLog_site_cast {k l r : ℕ} (h : k = l) (β : ℝ)
    (ζ : Hierarchy (r+1)) (m : Fin r → ℝ) (J : Fin l → Fin 3 → Bool) :
    trialLog r ζ m (siteLog (fun j : Fin k => satSample β (J (Fin.cast h j))) 0) =
      trialLog r ζ m (siteLog (fun j => satSample β (J j)) 0) := by
  subst l
  rfl

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ExponentContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal

local instance exponentContinuityMeasurable (X : TopCat) : MeasurableSpace X := borel X

abbrev UnitExponents (r : ℕ) := {m : Fin r → ℝ // ∀ i, 0 < m i ∧ m i < 1}

def exponentTail {r : ℕ} (m : UnitExponents (r+1)) : UnitExponents r :=
  ⟨fun i => m.val i.succ, fun i => m.property i.succ⟩

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_InterpolationInputs
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.PositiveInterpolation
open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

structure InterpolationAdmissible {p : ℕ} (M : Model p) : Prop where
  arity : 2 ≤ p
  density : 0 < M.alpha
  interaction_integrable : Integrable (fun z : InteractionSample p => ‖z.1‖)
    M.disorder.toMeasure
  field_integrable : Integrable (fun h : ℝ => |h|) M.field.toMeasure
  factorization : ∀ᵐ z ∂M.disorder.toMeasure,
    0 < z.2.1 ∧ ∀ s : Fin p → Spin,
      Real.exp (z.1 s) = z.2.1 * (1 + z.2.2.1 * ∏ l, z.2.2.2 l (s l)) ∧
      |z.2.2.1 * ∏ l, z.2.2.2 l (s l)| < 1
  independent_f : iIndepFun (fun l (z : InteractionSample p) => z.2.2.2 l)
    M.disorder.toMeasure
  identically_distributed_f : ∀ l j : Fin p,
    IdentDistrib (fun z : InteractionSample p => z.2.2.2 l)
      (fun z : InteractionSample p => z.2.2.2 j)
      M.disorder.toMeasure M.disorder.toMeasure
  independent_b : IndepFun (fun z : InteractionSample p => z.2.2.1)
    (fun z : InteractionSample p => z.2.2.2) M.disorder.toMeasure
  finite_b_moments : ∀ n : ℕ, 1 ≤ n →
    Integrable (fun z : InteractionSample p => (-z.2.2.1) ^ n) M.disorder.toMeasure
  positivity : ∀ n : ℕ, 1 ≤ n →
    0 ≤ ∫ z : InteractionSample p, (-z.2.2.1) ^ n ∂M.disorder.toMeasure

  raw_nonnegative : ∀ (n : ℕ), 1 ≤ n → ∀ (j : Fin p)
    (P B : FiniteLaw (Fin n → Spin)),
    0 ≤ rawReplicaMoment M (fun _ : Fin p => P) -
      (p : ℝ) * rawReplicaMoment M (fun l : Fin p => if l = j then P else B) +
      ((p - 1 : ℕ) : ℝ) * rawReplicaMoment M (fun _ : Fin p => B)

end FixedClauseThreshold.Computability.PositiveInterpolation

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RelaxedPressure
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable def relaxedPartition {n m : ℕ} (β : ℝ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) : ℝ :=
  ∑ s : Fin n → Bool, Real.exp (-β * relaxedViolations s indices signs)

noncomputable def relaxedLogPartition {n m : ℕ} (β : ℝ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) : ℝ :=
  Real.log (relaxedPartition β indices signs)

noncomputable def relaxedFixedLogPartition (n m : ℕ) (β : ℝ) : ℝ :=
  (∑ J : Fin m → Fin 3 → Bool,
    (∑ indices : Fin m → Fin 3 → Fin n, relaxedLogPartition β indices J) /
      Fintype.card (Fin m → Fin 3 → Fin n)) /
    Fintype.card (Fin m → Fin 3 → Bool)

noncomputable def relaxedPoissonPressure (a : ℝ≥0) (β : ℝ) (n : ℕ) : ℝ :=
  (∫ m : ℕ, relaxedFixedLogPartition n m β ∂poissonMeasure (a * n)) / n

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SignMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability
open DilutedSpinGlass
open scoped BigOperators

noncomputable def signFeature {n : ℕ} (P : FiniteLaw (Fin n → Spin)) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw Bool).expect fun J =>
    P.expect (fun s => ∏ a, literalFactor J (s a))

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_SATVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

noncomputable def satPressure (a : ℝ≥0) (β : ℝ) : ℝ :=
  liminf (pressure (satModel a β)) atTop

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

@[fun_prop] theorem computable_bool_and :
    Computable (fun p : Bool × Bool => p.1 && p.2) := Primrec.and.to_comp

noncomputable def rationalAt (ms : List ℚ) (i : ℕ) : ℚ := ms[i]?.getD 0

noncomputable def positiveExponents (ms : List ℚ) : Bool :=
  ms.all (fun q => decide (0 < q))

attribute [local irreducible] rationalAt

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
open RapidForcing.EffectiveArithmetic
open scoped NNReal

abbrev TrialData := ℚ × ℕ × Code × List ℚ

attribute [local irreducible] positiveExponents

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RelaxedEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset
open scoped BigOperators

noncomputable def relaxedMinimumViolations {n m : ℕ}
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) : ℕ :=
  Nat.find (show ∃ v : ℕ, ∃ s : Fin n → Bool,
      relaxedViolations s indices signs = v from
    ⟨relaxedViolations (fun _ => false) indices signs, (fun _ => false), rfl⟩)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RootEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

abbrev RelaxedClause (n : ℕ) := (Fin 3 → Fin n) × (Fin 3 → Bool)

noncomputable def clauseMinimum {n m : ℕ} (cs : Fin m → RelaxedClause n) : ℕ :=
  relaxedMinimumViolations (fun j => (cs j).1) (fun j => (cs j).2)

noncomputable def rootMinimum (n m : ℕ) (x : RootPath (RelaxedClause n) m) : ℝ :=
  clauseMinimum (rootArray m x)

noncomputable def rootSatisfiableProbability (n : ℕ) (μ : Measure (RelaxedClause n))
    (r : ℝ≥0) : ℝ :=
  poissonRootAverage μ r (fun m x => if rootMinimum n m x = 0 then 1 else 0)

end FixedClauseThreshold.Computability

end OAI
end


