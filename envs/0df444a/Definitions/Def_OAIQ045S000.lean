-- Prove2me | Definitions.Def_OAIQ045S000
-- name    : OAIQ045S000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:20:13.102991+00:00
-- url     : https://prove2.me/theorems/e3c94424-2bd0-4568-97a2-edfc1a886eb3
-- title:
--   Definitions bundle OAIQ045S000 of the split of OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 549 declarations of OpenAI's Lean: 353 definitions, 17 inductive types or structures, 3 instances and 176 theorems. The definitions and types are `OAI.SharpLogRamsey.ActualHighRank.Caps`, `OAI.SharpLogRamsey.ActualHighRank.Replacement`, `OAI.SharpLogRamsey.ActualHighRank.Replacement.cost_mono`, `OAI.SharpLogRamsey.ActualHighRank.StreamReplacement`, `OAI.SharpLogRamsey.ActualHighRank.StreamReplacement.toContextOutput`, `OAI.SharpLogRamsey.ActualHighRank.StreamReplacement.transport`, `OAI.SharpLogRamsey.ActualHighRank.flat_ActualHighRankExtraction_2`, `OAI.SharpLogRamsey.ActualHighRank.flat_ActualHighRankExtraction_3`, `OAI.SharpLogRamsey.ActualHighRank.flat_ActualHighRankReplacement_2`, `OAI.SharpLogRamsey.ActualHighRank.flat_ActualHighRankReplacement_3`, `OAI.SharpLogRamsey.ActualHighRank.flat_ActualHighRankSuccess_2`, `OAI.SharpLogRamsey.ActualHighRank.flat_ActualHighRankSuccess_3`, `OAI.SharpLogRamsey.ActualHighRank.highPrefactor`, `OAI.SharpLogRamsey.ActualHighRank.rawDomain`, `OAI.SharpLogRamsey.ActualHighRank.rawError`, `OAI.SharpLogRamsey.ActualHighRank.rawRows`, `OAI.SharpLogRamsey.ActualHighRank.rawThreshold`, `OAI.SharpLogRamsey.ActualHighRank.richDensity`, `OAI.SharpLogRamsey.ActualPivot.Banks`, `OAI.SharpLogRamsey.ActualPivot.Book`, `OAI.SharpLogRamsey.ActualPivot.Book.LocalRaw`, `OAI.SharpLogRamsey.ActualPivot.Book.allowed`, `OAI.SharpLogRamsey.ActualPivot.Book.choose`, `OAI.SharpLogRamsey.ActualPivot.Book.chronoChoose`, `OAI.SharpLogRamsey.ActualPivot.Book.decodeRaw`, `OAI.SharpLogRamsey.ActualPivot.Book.ofValidated`, `OAI.SharpLogRamsey.ActualPivot.Book.prepare`, `OAI.SharpLogRamsey.ActualPivot.Book.publicAlphabet`, `OAI.SharpLogRamsey.ActualPivot.ChronoDomains`, `OAI.SharpLogRamsey.ActualPivot.Code`, `OAI.SharpLogRamsey.ActualPivot.FirstBank`, `OAI.SharpLogRamsey.ActualPivot.FirstCode`, `OAI.SharpLogRamsey.ActualPivot.FirstSize`, `OAI.SharpLogRamsey.ActualPivot.Flag`, `OAI.SharpLogRamsey.ActualPivot.Header`, `OAI.SharpLogRamsey.ActualPivot.Input`, `OAI.SharpLogRamsey.ActualPivot.Input.FirstRow`, `OAI.SharpLogRamsey.ActualPivot.Input.choose`, `OAI.SharpLogRamsey.ActualPivot.Input.dualLoss`, `OAI.SharpLogRamsey.ActualPivot.Input.failure` and 330 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/SharpRamsey, in whole or in part: `SharpRamsey_Bounds_Lower`, `SharpRamsey_Construction_FiniteStreamTail`, `SharpRamsey_Construction_FlagConstruction`, `SharpRamsey_Construction_InitialLaw`, `SharpRamsey_Construction_InitialRectangles`, `SharpRamsey_Construction_InitialTools`, `SharpRamsey_Construction_RectangleStreamEvent`, `SharpRamsey_Entropy_ExternalMass`, `SharpRamsey_Entropy_ReciprocalEntropy`, `SharpRamsey_Execution_ContextOutput`, `SharpRamsey_Execution_ExecutedDeletion`, `SharpRamsey_Execution_ExecutedEndpoint`, `SharpRamsey_Execution_ExecutedExtraction`, `SharpRamsey_Execution_ExecutedFailureBudget`, `SharpRamsey_Execution_ExecutedFullMessage`, `SharpRamsey_Execution_ExecutedGoodTarget`, `SharpRamsey_Execution_ExecutedLawExtraction`, `SharpRamsey_Execution_ExecutedLoss`, `SharpRamsey_Execution_ExecutedMessage`, `SharpRamsey_Execution_ExecutedOutputCount`, `SharpRamsey_Execution_ExecutedPotential`, `SharpRamsey_Execution_ExecutedReplacement`, `SharpRamsey_Execution_ExecutedSecondTrim`, `SharpRamsey_Execution_ExecutedTrim`, `SharpRamsey_Execution_FreshExecution`, `SharpRamsey_Execution_HighRankExtraction`, `SharpRamsey_Execution_HighRankReplacement`, `SharpRamsey_Execution_OriginalTargetLoss`, `SharpRamsey_Exposure_DivergenceMap`, `SharpRamsey_Exposure_ExposureBudget`, `SharpRamsey_Exposure_ExposureModel`, `SharpRamsey_Exposure_HighRankMixture`, `SharpRamsey_Exposure_MixtureRealization`, `SharpRamsey_Exposure_RemainingEmbedding`, `SharpRamsey_Exposure_SourceCoupling`, `SharpRamsey_Exposure_StreamTransport`, `SharpRamsey_Exposure_SupportMixtures`, `SharpRamsey_Geometry_EightIntersections`, `SharpRamsey_Geometry_GeometricCover`, `SharpRamsey_Geometry_GeometricInduction`, `SharpRamsey_Geometry_HessianTangent`, `SharpRamsey_Geometry_PencilGeometry`, `SharpRamsey_Geometry_Projection`, `SharpRamsey_Geometry_ProjectionFullDescription`, `SharpRamsey_Geometry_ProjectionMessageCost`, `SharpRamsey_Geometry_ProjectiveTransport`, `SharpRamsey_Geometry_QuotientHeader`, `SharpRamsey_Geometry_ReadyProjectiveValidation`, `SharpRamsey_Geometry_RichLines`, `SharpRamsey_Geometry_ScaledTangentDot`, `SharpRamsey_Geometry_TotalDegreeCombination`, `SharpRamsey_Geometry_Triple`, `SharpRamsey_Geometry_Weight`, `SharpRamsey_Learning_DescriptionHeaders`, `SharpRamsey_Learning_GreedyIndexed`, `SharpRamsey_Learning_PreparedDecoder`, `SharpRamsey_Learning_PreparedProposals`, `SharpRamsey_Learning_ReadyTests`, `SharpRamsey_Learning_TestLearningRowBase`, `SharpRamsey_Learning_TestPointTail`, `SharpRamsey_Marking_AtomEscape`, `SharpRamsey_Marking_CardVectorLifts`, `SharpRamsey_Marking_ClassTransport`, `SharpRamsey_Marking_FinalMarking`, `SharpRamsey_Marking_HighRankBudgets`, `SharpRamsey_Marking_HighRankSuccess`, `SharpRamsey_Marking_MarkingActual`, `SharpRamsey_Marking_MarkingClassification`, `SharpRamsey_Marking_MarkingFiniteClasses`, `SharpRamsey_Marking_MarkingOrientation`, `SharpRamsey_Marking_MarkingTwoScans`, `SharpRamsey_Marking_MultiplicityClass`, `SharpRamsey_Marking_Popular`, `SharpRamsey_Marking_RawLowerTail`, `SharpRamsey_Marking_RowSpan`, `SharpRamsey_Marking_TailSum`, `SharpRamsey_Marking_TargetEvent`, `SharpRamsey_Parameters_ReciprocalScales`, `SharpRamsey_Parameters_SourceScaleComparisons`, `SharpRamsey_Parameters_SourceScales`, `SharpRamsey_Planar_HeavyPlaneCurrent`, `SharpRamsey_Planar_HeavyPlaneInput`, `SharpRamsey_Planar_HeavyPlanePublic`, `SharpRamsey_Reciprocal_AuxiliaryFamilies`, `SharpRamsey_Reciprocal_AuxiliaryLevels`, `SharpRamsey_Reciprocal_CanonicalAuxiliaryLaw`, `SharpRamsey_Reciprocal_LevelLosses`, `SharpRamsey_Reciprocal_ReciprocalBands`, `SharpRamsey_Reciprocal_ReciprocalCurrent`, `SharpRamsey_Reciprocal_ReciprocalOutput`, `SharpRamsey_Reciprocal_ReciprocalPopulation`, `SharpRamsey_Reciprocal_ReciprocalTree`, `SharpRamsey_Selection_DyadicGrid`, `SharpRamsey_Selection_EmptySupports`, `SharpRamsey_Selection_EndpointSupports`, `SharpRamsey_Selection_FreshAccrual`, `SharpRamsey_Selection_FreshFamilies`, `SharpRamsey_Selection_HistoryLaw`, `SharpRamsey_Selection_LiveFamilies`, `SharpRamsey_Selection_LiveRealization`, `SharpRamsey_Selection_NullFreeLaw`, `SharpRamsey_Selection_OriginalFamilies`, `SharpRamsey_Selection_ScheduledBanks`, `SharpRamsey_Selection_SparseProductSharp`, `SharpRamsey_Selection_UnifiedContext`, `SharpRamsey_Trees_ChronologicalExecution`, `SharpRamsey_Trees_ChronologicalTree`, `SharpRamsey_Trees_OriginalTreeLoss`, `SharpRamsey_Trees_Pivot`, `SharpRamsey_Trees_PivotAlphabet`, `SharpRamsey_Trees_PivotAlphabetCost`, `SharpRamsey_Trees_PivotBanks`, `SharpRamsey_Trees_PivotCalls`, `SharpRamsey_Trees_PivotCaps`, `SharpRamsey_Trees_PivotDecoder`, `SharpRamsey_Trees_PivotExecution`, `SharpRamsey_Trees_PivotGeometry`, `SharpRamsey_Trees_PivotLosses`, `SharpRamsey_Trees_PivotValidation`, `SharpRamsey_Trees_TreeDecoder`, `SharpRamsey_Validation_ProducedExclusion`, `SharpRamsey_Validation_ValidationSchedule`, `SharpRamsey_Validation_ValidationTools`, `SharpRamsey_Windows_BalancedWindows`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ045S002`; the statements `OAI.SharpLogRamsey.ActualPivot.Book.live_realization`, `OAI.SharpLogRamsey.ActualPivot.eventually_reciprocal_message_cost`, `OAI.SharpLogRamsey.ActualPivot.supplied_book`, `OAI.SharpLogRamsey.GeometricCover.uniform_four`, `OAI.SharpLogRamsey.LowerTransfer.prime_construction`, `OAI.SharpLogRamsey.Marking.eventually_high_ordered`, `OAI.SharpLogRamsey.Selection.Windows.eventually_integer_output`, `OAI.SharpLogRamsey.Selection.Windows.eventually_open_output` and `OAI.SharpLogRamsey.SpatialPublic.actual_cover`; the proofs of `OAI.SharpLogRamsey.ActualPivot.eventually_reciprocal_message_cost` and `OAI.SharpLogRamsey.main`.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/SharpRamsey at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ045_SR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_RichLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section

section

namespace SharpLogRamsey.ImplicitBranch
open Polynomial
open scoped Ring

/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

The following Hensel lifting theorem is adapted from Mathlib.RingTheory.Henselian.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Henselian.lean

This code has been modified.
-/

variable {σ K R S : Type*} [Fintype σ] [DecidableEq σ] [Field K]
  [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

noncomputable def liftZ (F : MvPolynomial (Option σ) K) :
    Polynomial (MvPowerSeries σ K) :=
  MvPolynomial.aeval (fun o => o.elim Polynomial.X
    (fun i => Polynomial.C (MvPowerSeries.X i))) F

end SharpLogRamsey.ImplicitBranch

open Finset Finsupp
namespace SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
variable {p : ℕ} [CharP K p]

noncomputable def jetIdeal (n : ℕ) : Ideal (MvPowerSeries σ K) where
  carrier := {f | (n : ℕ∞) ≤ f.order}
  zero_mem' := by simp
  add_mem' := fun ha hb => (le_min ha hb).trans MvPowerSeries.min_order_le_add
  smul_mem' := by
    intro a f hf
    change (n : ℕ∞) ≤ (a*f).order
    exact hf.trans ((le_add_left le_rfl).trans MvPowerSeries.le_order_mul)

variable {τ R : Type*} [CommRing R] [Algebra K R]

variable [Fintype τ] [DecidableEq τ]

noncomputable def branchPoint (h : MvPowerSeries σ K) : Option σ → MvPowerSeries σ K :=
  fun o => o.elim h MvPowerSeries.X

noncomputable def branchTangent (h : MvPowerSeries σ K) (a : σ) :
    Option σ → MvPowerSeries σ K := fun o => MvPowerSeries.pderiv _ a (branchPoint h o)

end SharpLogRamsey.FlatnessCore
end
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_HessianTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
namespace SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
variable {p : ℕ} [CharP K p]
variable {τ R : Type*} [CommRing R] [Algebra K R]
variable [Fintype τ] [DecidableEq τ]

def scaledTangent (g : Option σ → R) (a : σ) : Option σ → R :=
  fun o => o.elim (-g (some a)) (fun i => if i = a then g none else 0)

noncomputable def flatnessPolynomial (F : MvPolynomial (Option σ) K) (a b : σ) :
    MvPolynomial (Option σ) K :=
  ∑ j, ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv j F) *
    scaledTangent (fun o => MvPolynomial.pderiv o F) a i *
    scaledTangent (fun o => MvPolynomial.pderiv o F) b j

end SharpLogRamsey.FlatnessCore

open scoped BigOperators
open MvPolynomial Finsupp

open scoped BigOperators
open MvPolynomial

open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid
namespace SharpLogRamsey.CoprimeCombination
variable {σ ι K : Type*} [Fintype ι] [Field K] [Infinite K]

noncomputable def combinationMap (Q : ι → MvPolynomial σ K) :
    (ι → K) →ₗ[K] MvPolynomial σ K :=
  ∑ i, (LinearMap.proj i).smulRight (Q i)
omit [Infinite K] in

@[simp] lemma combinationMap_apply (Q : ι → MvPolynomial σ K) (c : ι → K) :
    combinationMap Q c = ∑ i, c i • Q i := by simp [combinationMap]

end SharpLogRamsey.CoprimeCombination
end
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_TotalDegreeCombination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
open scoped BigOperators
open MvPolynomial Finsupp
open scoped BigOperators
open MvPolynomial
open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid

open scoped BigOperators
open Finset MvPolynomial
namespace SharpLogRamsey.LineFlatness
variable {K σ R : Type*} [Field K] [Fintype σ] [DecidableEq σ]
  [CommRing R] [Algebra K R]

noncomputable def restrictLine (x v : σ → K) (F : MvPolynomial σ K) : Polynomial K :=
  aeval (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) F

noncomputable def hessian (x : σ → K) (F : MvPolynomial σ K) (u v : σ → K) : K :=
  ∑ j, ∑ i, eval x (pderiv i (pderiv j F))*u i*v j

def scaledTangent (g : Option (Fin 2) → K) (a : Fin 2) : Option (Fin 2) → K :=
  fun o => o.elim (-g (some a)) (fun i => if i = a then g none else 0)

end SharpLogRamsey.LineFlatness

end
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ScaledTangentDot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section

section

section

namespace SharpLogRamsey.GenericCoordinates
open MvPolynomial Finset
open scoped BigOperators
variable {K : Type*} [Field K] [Infinite K]
noncomputable section

def shear (a b c : K) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun x := ![x 0+a*x 1+b*x 2, x 1+c*x 2, x 2]
  invFun x := ![x 0-a*x 1+(a*c-b)*x 2, x 1-c*x 2, x 2]
  left_inv x := by ext i; fin_cases i <;> simp ; ring
  right_inv x := by ext i; fin_cases i <;> simp ; ring
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

abbrev first (a b : K) : (Fin 3 → K) →ₗ[K] K :=
  LinearMap.proj 0+a • LinearMap.proj 1+b • LinearMap.proj 2

def line (x v : Fin 3 → K) : Set (Fin 3 → K) := Set.range (fun r : K => x+r • v)
def direction (t : (Fin 3 → K) →ₗ[K] K) (v : Fin 3 → K) : Fin 3 → K := (t v)⁻¹ • v
def base (t : (Fin 3 → K) →ₗ[K] K) (x v : Fin 3 → K) : Fin 3 → K :=
  x-t x • direction t v

end
end SharpLogRamsey.GenericCoordinates

end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_Triple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section

section

namespace SharpLogRamsey.AffineIncidence
open Finset
open scoped BigOperators
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]
noncomputable section

def carrier (x v : Fin 3 → K) : Set (Fin 3 → K) := Set.range (fun r : K => x+r • v)

variable (x v : ι → Fin 3 → K)
def pencil (y : Fin 3 → K) : Finset ι := by
  classical
  exact univ.filter (fun i => y ∈ carrier (x i) (v i))
def onLine (S : Finset (Fin 3 → K)) (i : ι) : Finset (Fin 3 → K) := by
  classical
  exact S.filter (fun y => y ∈ carrier (x i) (v i))
def richPoints (S : Finset (Fin 3 → K)) (i : ι) : Finset (Fin 3 → K) := by
  classical
  exact (onLine x v S i).filter (fun y => 2 < (pencil x v y).card)
def poorPoints (S : Finset (Fin 3 → K)) (i : ι) : Finset (Fin 3 → K) := by
  classical
  exact (onLine x v S i).filter (fun y => (pencil x v y).card ≤ 2)

end
end SharpLogRamsey.AffineIncidence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_Weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section

section

namespace SharpLogRamsey.Interpolation
open Finset MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]
noncomputable section

abbrev Box (n h : ℕ) := Fin n → Fin (h+1)
def exponent {n h : ℕ} (d : Box n h) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (d i).val)

end
end SharpLogRamsey.Interpolation

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_FiniteStreamTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FiniteStreamTail
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α : Type*} [Fintype α]

def hits {N : ℕ} (S : Finset α) (z : Fin N→α) : ℕ :=
  (univ.filter (fun i=>z i∈S)).card

def probability (S : Finset α) : ℝ := (S.card:ℝ)/(Fintype.card α:ℝ)

lemma moment (S : Finset α) (N : ℕ) :
    (∑ z : Fin N→α,(2:ℝ)^hits S z)=
      ((Fintype.card α:ℝ)+(S.card:ℝ))^N := by
  have hp (z : Fin N→α) :
      (2:ℝ)^hits S z=∏ i,if z i∈S then (2:ℝ) else 1 := by
    simp only [prod_ite,hits,prod_const,one_pow,mul_one]
  have hs : (∑ a : α,if a∈S then (2:ℝ) else 1)=(Fintype.card α:ℝ)+(S.card:ℝ) := by
    have he (a : α) : (if a∈S then (2:ℝ) else 1)=1+(if a∈S then 1 else 0) := by
      split_ifs <;> norm_num
    simp only [he,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one,
      Fintype.sum_ite_mem,sum_const]
  simp_rw [hp]
  rw [←Fintype.prod_sum (fun (_ : Fin N) (a : α)=>if a∈S then (2:ℝ) else 1)]
  simp only [hs,prod_const,card_univ,Fintype.card_fin]

variable [Nonempty α]

lemma card_pos : (0:ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos

lemma average_moment (S : Finset α) (N : ℕ) :
    (∑ z : Fin N→α,(2:ℝ)^hits S z)/(Fintype.card (Fin N→α):ℝ) =
      (1+probability S)^N := by
  rw [moment]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,←div_pow,probability]
  congr 1
  rw [add_div,div_self (ne_of_gt (card_pos (α:=α)))]

lemma average_moment_le (S : Finset α) (N : ℕ) :
    (∑ z : Fin N→α,(2:ℝ)^hits S z)/(Fintype.card (Fin N→α):ℝ) ≤
      exp (N*probability S) := by
  rw [average_moment,exp_nat_mul]
  apply pow_le_pow_left₀
  · exact add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · simpa only [add_comm] using Real.add_one_le_exp (probability S)

lemma single_tail (S : Finset α) (N : ℕ) (t : ℝ) :
    probability (univ.filter (fun z : Fin N→α=>t≤hits S z)) ≤
      exp (N*probability S-t*log 2) := by
  let B := univ.filter (fun z : Fin N→α=>t≤hits S z)
  have hsum : (B.card:ℝ)*exp (t*log 2)≤∑ z : Fin N→α,(2:ℝ)^hits S z := by
    calc
      _ = ∑ _z∈B,exp (t*log 2) := by simp
      _ ≤ ∑ z∈B,(2:ℝ)^hits S z := by
        apply sum_le_sum
        intro z hz
        have ht := (mem_filter.mp hz).2
        have he : exp ((hits S z:ℝ)*log 2)=(2:ℝ)^hits S z := by
          rw [exp_nat_mul,exp_log (by norm_num)]
        rw [←he]
        apply exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right ht (log_nonneg (by norm_num))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>by positivity)
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (Fintype.card (Fin N→α)))
  have hm := average_moment_le S N
  have hb : probability B*exp (t*log 2)≤exp (N*probability S) := by
    unfold probability
    calc
      _ = (B.card*exp (t*log 2))/(Fintype.card (Fin N→α):ℝ) := by ring
      _ ≤ _ := hdiv.trans hm
  have hh := (le_div_iff₀ (exp_pos (t*log 2))).mpr hb
  simpa only [exp_sub] using hh

lemma probability_compl (S : Finset α) : probability Sᶜ=1-probability S := by
  simp only [probability,Finset.card_compl,Nat.cast_sub (card_le_univ S),sub_div,
    div_self (ne_of_gt (card_pos (α:=α)))]

variable {J : Type*} [Fintype J]

theorem simultaneous_tail (R : J→Finset α) (N : ℕ) (t μ : ℝ)
    (hμ : ∀ j,(N:ℝ)*probability (R j)≤μ) :
    probability (univ.filter (fun z : Fin N→α=>∃ j,t≤hits (R j) z)) ≤
      (Fintype.card J:ℝ)*exp (μ-t*log 2) := by
  let B := fun j=>univ.filter (fun z : Fin N→α=>t≤hits (R j) z)
  have he : (univ.filter (fun z : Fin N→α=>∃ j,t≤hits (R j) z))=
      univ.biUnion B := by ext z; simp [B]
  rw [he]
  have hc : ((univ.biUnion B).card:ℝ)≤∑ j,((B j).card:ℝ) := by
    exact_mod_cast (card_biUnion_le (s:=univ) (t:=B))
  calc
    _ ≤ (∑ j,((B j).card:ℝ))/(Fintype.card (Fin N→α):ℝ) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = ∑ j,probability (B j) := by rw [sum_div]; rfl
    _ ≤ ∑ _j : J,exp (μ-t*log 2) := by
      apply sum_le_sum
      intro j _
      exact (single_tail (R j) N t).trans (exp_le_exp.mpr (sub_le_sub_right (hμ j) _))
    _ = _ := by simp

end
end SharpLogRamsey.FiniteStreamTail

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Bounds_Lower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of finite prime-field graph constructions to all sufficiently large orders. -/

section
namespace SharpLogRamsey.LowerTransfer
open Filter Real
open scoped Topology
noncomputable section

def PrimeConstruction (d : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → η < 1/10 → ∀ᶠ q : ℕ in atTop,
    q.Prime → ∃ G : SimpleGraph (Fin ⌊(q:ℝ)^d * Real.log q⌋₊),
      G.CliqueFree (d+1) ∧ G.indepNum < ⌊(q:ℝ) * (Real.log q)^(1+η)⌋₊

end
end SharpLogRamsey.LowerTransfer

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection

structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def entropy (p : Law α) : ℝ := - ∑ a, p.mass a * Real.log (p.mass a)

noncomputable def Law.map (p : Law α) (f : α → β) : Law β := by
  classical
  refine ⟨fun b => ∑ a with f a = b, p.mass a, ?_, ?_⟩
  · intro b; exact Finset.sum_nonneg fun a _ => p.nonneg a
  · exact (Finset.sum_fiberwise Finset.univ f p.mass).trans p.total

noncomputable def Law.fst (p : Law (α × β)) : Law α where
  mass a := ∑ b, p.mass (a,b)
  nonneg a := Finset.sum_nonneg fun b _ => p.nonneg (a,b)
  total := by simpa only [← Fintype.sum_prod_type] using p.total

noncomputable def Law.snd (p : Law (α × β)) : Law β where
  mass b := ∑ a, p.mass (a,b)
  nonneg b := Finset.sum_nonneg fun a _ => p.nonneg (a,b)
  total := by rw [Finset.sum_comm]; simpa only [← Fintype.sum_prod_type] using p.total

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def Law.event (p : Law α) (E : Finset α) : ℝ := ∑ a ∈ E, p.mass a

noncomputable def Law.prod (p : Law α) (q : Law β) : Law (α × β) where
  mass z := p.mass z.1*q.mass z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  total := by rw [Fintype.sum_prod_type, ← sum_mul_sum, p.total,q.total]; ring

theorem Law.le_snd (p : Law (α × β)) (a : α) (b : β) : p.mass (a,b) ≤ p.snd.mass b :=
  single_le_sum (fun c _hc => p.nonneg (c,b)) (mem_univ a)

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem Law.sum_map (p : Law α) (f : α → β) (g : β → ℝ) :
    ∑ b, (p.map f).mass b*g b = ∑ a, p.mass a*g (f a) := by
  change ∑ b, (∑ a with f a = b, p.mass a)*g b = _
  simp_rw [sum_mul]
  calc
    _ = ∑ b, ∑ a with f a = b, p.mass a*g (f a) := by
      apply sum_congr rfl; intro b hb
      apply sum_congr rfl; intro a ha
      rw [(mem_filter.mp ha).2]
    _ = _ := sum_fiberwise univ f (fun a => p.mass a*g (f a))

theorem entropy_map (p : Law α) (f : α → β) :
    entropy (p.map f) = -∑ a, p.mass a*Real.log ((p.map f).mass (f a)) := by
  exact congrArg Neg.neg (p.sum_map f (fun b => Real.log ((p.map f).mass b)))

noncomputable def Law.condFst (p : Law (α × β)) (b : β) : Law α := by
  by_cases h : p.snd.mass b = 0
  · exact p.fst
  · refine ⟨fun a => p.mass (a,b)/p.snd.mass b, ?_, ?_⟩
    · intro a; exact div_nonneg (p.nonneg _) (p.snd.nonneg b)
    · rw [← sum_div]
      change p.snd.mass b/p.snd.mass b = 1
      exact div_self h

theorem Law.condFst_mass (p : Law (α × β)) (b : β) (h : p.snd.mass b ≠ 0) (a : α) :
    (p.condFst b).mass a = p.mass (a,b)/p.snd.mass b := by
  simp [Law.condFst,h]

end SharpLogRamsey.Selection
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_DivergenceMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

@[ext] theorem Law.ext {p q : Law α} (h : ∀ a, p.mass a = q.mass a) : p = q := by
  cases p with | mk p hp hpt =>
  cases q with | mk q hq hqt =>
  have hh : p = q := funext h
  subst q
  rfl

@[simp] theorem Law.map_id (p : Law α) : p.map id = p := by
  ext a
  simp [Law.map, sum_filter]

@[simp] theorem Law.map_map (p : Law α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (g ∘ f) := by
  ext c
  change (∑ b with g b = c, (p.map f).mass b) = ∑ a with g (f a) = c, p.mass a
  have h := p.sum_map f (fun b => if g b = c then 1 else 0)
  simpa [mul_ite, sum_filter] using h

@[simp] theorem Law.map_fst (p : Law (α × β)) : p.map Prod.fst = p.fst := by
  ext a
  simp only [Law.map, Law.fst, sum_filter, Fintype.sum_prod_type]
  rw [sum_comm]
  simp

@[simp] theorem Law.map_snd (p : Law (α × β)) : p.map Prod.snd = p.snd := by
  ext b
  simp [Law.map, Law.snd, sum_filter, Fintype.sum_prod_type]

@[simp] theorem Law.fst_map_pair (p : Law (α × β)) (f : α → γ) (g : β → δ) :
    (p.map (fun z => (f z.1,g z.2))).fst = p.fst.map f := by
  rw [← Law.map_fst, Law.map_map, ← Law.map_fst, Law.map_map]
  rfl

@[simp] theorem Law.snd_map_pair (p : Law (α × β)) (f : α → γ) (g : β → δ) :
    (p.map (fun z => (f z.1,g z.2))).snd = p.snd.map g := by
  rw [← Law.map_snd, Law.map_map, ← Law.map_snd, Law.map_map]
  rfl

@[simp] theorem Law.fst_map_self (p : Law α) (f : α → β) :
    (p.map (fun a => (a,f a))).fst = p := by
  rw [← Law.map_fst, Law.map_map]
  exact p.map_id

@[simp] theorem Law.snd_map_self (p : Law α) (f : α → β) :
    (p.map (fun a => (a,f a))).snd = p.map f := by
  rw [← Law.map_snd, Law.map_map]
  rfl

noncomputable def Law.cond (p : Law α) (f : α → β) (b : β) : Law α :=
  (p.map (fun a => (a,f a))).condFst b

theorem Law.cond_mass (p : Law α) (f : α → β) (b : β)
    (hb : (p.map f).mass b ≠ 0) (a : α) :
    (p.cond f b).mass a = (if f a = b then p.mass a else 0)/(p.map f).mass b := by
  unfold Law.cond
  rw [Law.condFst_mass _ _ (by simpa using hb)]
  rw [Law.snd_map_self]
  congr 1
  simp [Law.map, sum_filter, ite_and]

theorem Law.cond_map_weight (p : Law α) (f : α → β) (g : α → γ) (b : β) (c : γ) :
    (p.map f).mass b * ((p.cond f b).map g).mass c =
    (p.map (fun a => (g a,f a))).mass (c,b) := by
  by_cases hb : (p.map f).mass b = 0
  · rw [hb,zero_mul]
    have hh := (p.map (fun a => (g a,f a))).le_snd c b
    have he : (p.map (fun a => (g a,f a))).snd = p.map f := by
      rw [← Law.map_snd, Law.map_map]; rfl
    rw [he,hb] at hh
    exact (le_antisymm hh ((p.map _).nonneg _)).symm
  change (p.map f).mass b*(∑ a with g a = c, (p.cond f b).mass a) = _
  simp_rw [p.cond_mass f b hb]
  rw [← sum_div, mul_div_cancel₀ _ hb]
  simp only [Law.map, Prod.mk.injEq, sum_filter]
  apply sum_congr rfl
  intro a ha
  split_ifs <;> simp_all

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def Law.pi (p : ι → Law β) : Law (ι → β) where
  mass x := ∏ i, (p i).mass (x i)
  nonneg x := prod_nonneg fun i hi => (p i).nonneg (x i)
  total := by
    have h := prod_univ_sum (fun _ : ι => (univ : Finset β)) (fun i b => (p i).mass b)
    simpa only [Fintype.piFinset_univ, Law.total, prod_const_one] using h.symm

noncomputable def Law.marginal (p : Law (ι → β)) (i : ι) : Law β :=
  p.map (fun x => x i)

theorem Law.map_mass_injective (p : Law α) (f : α → β) (hf : Function.Injective f) (a : α) :
    (p.map f).mass (f a) = p.mass a := by
  change (∑ x with f x = f a, p.mass x) = p.mass a
  simp only [hf.eq_iff]
  simp [sum_filter]

theorem entropy_map_eq_of_injective (p : Law α) (f : α → β) (hf : Function.Injective f) :
    entropy (p.map f) = entropy p := by
  rw [entropy_map]
  simp only [p.map_mass_injective f hf]
  rfl

noncomputable def Law.restrict (p : Law (ι → β)) (S : Finset ι) : Law (S → β) :=
  p.map (fun x i => x i)

@[simp] theorem Law.marginal_restrict (p : Law (ι → β)) (S : Finset ι) (i : S) :
    (p.restrict S).marginal i = p.marginal i := by
  unfold Law.marginal Law.restrict
  rw [Law.map_map]
  rfl

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_RemainingEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical
namespace SharpLogRamsey.Selection
variable {Ω α Γ A : Type*} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype A]

lemma Law.map_support (p : Law Ω) (f : Ω → A) (a : A) (ha : (p.map f).mass a ≠ 0) :
    ∃ x, p.mass x ≠ 0 ∧ f x = a := by
  by_contra hn
  push Not at hn
  apply ha
  change (∑ x with f x = a, p.mass x) = 0
  apply sum_eq_zero
  intro x hx
  by_contra hp
  exact hn x hp (mem_filter.mp hx).2

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalCurrent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def Incident (a : Projectivization K V)
    (b : Projectivization K (Module.Dual K V)) : Prop := b.rep a.rep = 0

theorem incident_iff_submodule (a : Projectivization K V)
    (b : Projectivization K (Module.Dual K V)) :
    Incident a b ↔ a.submodule ≤ LinearMap.ker b.rep := by
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
  rfl

noncomputable def projectiveSubmoduleEquiv (W : Submodule K V) :
    Projectivization K W ≃ {a : Projectivization K V // a.submodule ≤ W} := by
  let f : Projectivization K W → {a : Projectivization K V // a.submodule ≤ W} :=
    fun a => ⟨Projectivization.map W.subtype W.injective_subtype a, by
      induction a using Projectivization.ind with
      | h v hv =>
        rw [Projectivization.map_mk, Projectivization.submodule_mk,
          Submodule.span_singleton_le_iff_mem]
        exact v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    exact Projectivization.map_injective W.subtype W.injective_subtype
      (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    have hmem : a.rep ∈ W := ha (by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _)
    let v : W := ⟨a.rep, hmem⟩
    have hv : v ≠ 0 := fun h => a.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    exact a.mk_rep

end SharpLogRamsey.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_AuxiliaryLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped Classical BigOperators

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def massLevel (p : Law α) (a : α) : ℕ := ⌊-Real.log (p.mass a)⌋₊

abbrev Levels (p : Law α) := {n // n ∈ (univ.image (massLevel p) : Finset ℕ)}

noncomputable def levelIndex (p : Law α) (a : α) : Levels p :=
  ⟨massLevel p a, mem_image.mpr ⟨a, mem_univ _, rfl⟩⟩

noncomputable def Law.onEvent (p : Law α) (E : Finset α) (hE : 0<p.event E) : Law E where
  mass a := p.mass a / p.event E
  nonneg a := div_nonneg (p.nonneg a) hE.le
  total := by
    rw [←sum_div, sum_coe_sort]
    exact div_self hE.ne'

noncomputable def levelSet (p : Law α) (b : Levels p) : Finset α :=
  univ.filter (fun a => 0<p.mass a ∧ levelIndex p a=b)

noncomputable def levelLoss (p : Law α) (A : ℝ) (b : Levels p) : ℝ :=
  Real.log (A/(levelSet p b).card)

noncomputable def retainedLevels (p : Law α) (good : Finset α) (A K : ℝ) : Finset (Levels p) :=
  univ.filter (fun b => 0<(levelSet p b).card ∧ levelLoss p A b≤K ∧
    (levelSet p b).card ≤ 2*((levelSet p b)∩good).card)

end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_LevelLosses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem incident_iff_dualAnnihilator (a : Projectivization K V)
    (b : Projectivization K (Module.Dual K V)) :
    Incident a b ↔ b.submodule ≤ a.submodule.dualAnnihilator := by
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
    Submodule.mem_dualAnnihilator]
  change b.rep a.rep = 0 ↔ a.submodule ≤ LinearMap.ker b.rep
  exact incident_iff_submodule a b

theorem card_incident_dual [Finite K] [FiniteDimensional K V] {d : ℕ}
    (hdim : Module.finrank K V = d+1) (a : Projectivization K V) :
    Nat.card {b : Projectivization K (Module.Dual K V) // Incident a b} =
      ∑ i ∈ Finset.range d, Nat.card K^i := by
  let e := Equiv.subtypeEquivRight (fun b => incident_iff_dualAnnihilator a b)
  rw [Nat.card_congr e, ← Nat.card_congr (projectiveSubmoduleEquiv a.submodule.dualAnnihilator)]
  apply Projectivization.card_of_finrank
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq a.submodule
  rw [Projectivization.finrank_submodule] at h
  omega

theorem card_common_incident_dual [Finite K] [FiniteDimensional K V] {d : ℕ}
    (hdim : Module.finrank K V = d+2)
    (a a' : Projectivization K V) (haa : a ≠ a') :
    Nat.card {b : Projectivization K (Module.Dual K V) // Incident a b ∧ Incident a' b} =
      ∑ i ∈ Finset.range d, Nat.card K^i := by
  let W := Submodule.span K (Set.range ![a.rep, a'.rep])
  have hW : Module.finrank K W = 2 := by
    simpa [W] using finrank_span_eq_card (Projectivization.linearIndependent_pair_iff_ne.mpr haa)
  have hpred (b : Projectivization K (Module.Dual K V)) :
      (Incident a b ∧ Incident a' b) ↔ b.submodule ≤ W.dualAnnihilator := by
    rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_dualAnnihilator]
    change _ ↔ W ≤ LinearMap.ker b.rep
    rw [Submodule.span_le]
    simp [Incident, Set.insert_subset_iff, and_comm]
  let e := Equiv.subtypeEquivRight hpred
  rw [Nat.card_congr e, ← Nat.card_congr (projectiveSubmoduleEquiv W.dualAnnihilator)]
  apply Projectivization.card_of_finrank
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

section Design
variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def weightedIncidences (R : X → Y → Prop) (w : X → ℝ) (y : Y) : ℝ :=
  ∑ x, if R x y then w x else 0

theorem design_quadratic (R : X → Y → Prop) (k l : ℝ)
    (hdeg : ∀ x, (Fintype.card {y // R x y} : ℝ) = k)
    (hpair : ∀ x z, x ≠ z → (Fintype.card {y // R x y ∧ R z y} : ℝ) = l)
    (w : X → ℝ) :
    ∑ y, (weightedIncidences R w y)^2 =
      (k-l) * (∑ x, (w x)^2) + l * (∑ x, w x)^2 := by
  have hcount (x z : X) : (Fintype.card {y // R x y ∧ R z y} : ℝ) =
      if x = z then k else l := by
    by_cases h : x = z
    · subst z; simpa using hdeg x
    · simpa [h] using hpair x z h
  have hexpand (y : Y) : (weightedIncidences R w y)^2 =
      ∑ x, ∑ z, if R x y ∧ R z y then w x * w z else 0 := by
    rw [weightedIncidences, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    by_cases hx : R x y <;> by_cases hz : R z y <;> simp [hx,hz]
  have hcoeff (x z : X) : (if x = z then k else l) =
      (if x = z then k-l else 0) + l := by split_ifs <;> ring
  calc
    _ = ∑ x, ∑ z, ∑ y, if R x y ∧ R z y then w x * w z else 0 := by
      simp_rw [hexpand]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ z, (w x * w z) * (if x = z then k else l) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      rw [← hcount]
      simp only [Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul]
      ring
    _ = ∑ x, ∑ z, (w x * w z) * ((if x = z then k-l else 0) + l) := by
      simp_rw [hcoeff]
    _ = (k-l) * (∑ x, (w x)^2) + l * (∑ x, w x)^2 := by
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      simp only [sq, Finset.sum_mul, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl
      · intro x _; ring
      · intro x _; apply Finset.sum_congr rfl; intro z _; ring

theorem design_variance (R : X → Y → Prop) (k l : ℝ)
    (hdeg : ∀ x, (Fintype.card {y // R x y} : ℝ) = k)
    (hpair : ∀ x z, x ≠ z → (Fintype.card {y // R x y ∧ R z y} : ℝ) = l)
    [Nonempty Y] (w : X → ℝ) :
    ∑ y, (weightedIncidences R w y - k / Fintype.card Y * ∑ x, w x)^2 =
      (k-l) * (∑ x, (w x)^2) +
        (l - k^2 / Fintype.card Y) * (∑ x, w x)^2 := by
  have hv : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ y, weightedIncidences R w y = k * ∑ x, w x := by
    unfold weightedIncidences
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [← hdeg x]
    simp [← Finset.sum_filter, Fintype.card_subtype]
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, design_quadratic R k l hdeg hpair w]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hsum]
  field_simp
  ring

end Design

theorem geom_design_identity (q : ℝ) (n : ℕ) :
    (∑ i ∈ range (n+2), q^i)^2 =
      (∑ i ∈ range (n+1), q^i) * (∑ i ∈ range (n+3), q^i) + q^(n+1) := by
  have hk : (∑ i ∈ range (n+2), q^i) = q*(∑ i ∈ range (n+1), q^i)+1 :=
    geom_sum_succ
  have hv : (∑ i ∈ range (n+3), q^i) = q*(∑ i ∈ range (n+2), q^i)+1 :=
    geom_sum_succ
  have hd : (∑ i ∈ range (n+2), q^i) = q^(n+1)+(∑ i ∈ range (n+1), q^i) :=
    geom_sum_succ'
  have hc : q^(n+1) = (∑ i ∈ range (n+2), q^i) -
      (∑ i ∈ range (n+1), q^i) := by linarith
  rw [hv, hc, hk]
  ring

section Projective
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

theorem projective_variance {n : ℕ} (hdim : Module.finrank K V = n+3)
    (w : Projectivization K V → ℝ) :
    ∑ y : Projectivization K (Module.Dual K V),
      (weightedIncidences Incident w y -
        (∑ i ∈ range (n+2), (Nat.card K : ℝ)^i) /
        (∑ i ∈ range (n+3), (Nat.card K : ℝ)^i) * ∑ x, w x)^2 =
      (Nat.card K : ℝ)^(n+1) * ((∑ x, w x^2) -
        (∑ x, w x)^2 / (∑ i ∈ range (n+3), (Nat.card K : ℝ)^i)) := by
  have hv : (Fintype.card (Projectivization K (Module.Dual K V)) : ℝ) =
      ∑ i ∈ range (n+3), (Nat.card K : ℝ)^i := by
    rw [← Nat.card_eq_fintype_card, Projectivization.card_of_finrank K _
      (Subspace.dual_finrank_eq.trans hdim)]
    push_cast
    rfl
  have hvpos : 0 < ∑ i ∈ range (n+3), (Nat.card K : ℝ)^i := by
    apply Finset.sum_pos'
    · intro i hi; positivity
    · exact ⟨0, by simp, by simp⟩
  have : Nonempty (Projectivization K (Module.Dual K V)) := by
    apply Fintype.card_pos_iff.mp
    exact_mod_cast hv ▸ hvpos
  have hg (x : Projectivization K V) :
      (Fintype.card {y : Projectivization K (Module.Dual K V) // Incident x y} : ℝ) =
      ∑ i ∈ range (n+2), (Nat.card K : ℝ)^i := by
    rw [← Nat.card_eq_fintype_card, card_incident_dual (d := n+2) hdim x]
    push_cast
    rfl
  have hp (x z : Projectivization K V) (hxz : x ≠ z) :
      (Fintype.card {y : Projectivization K (Module.Dual K V) //
        Incident x y ∧ Incident z y} : ℝ) =
      ∑ i ∈ range (n+1), (Nat.card K : ℝ)^i := by
    rw [← Nat.card_eq_fintype_card, card_common_incident_dual (d := n+1) hdim x z hxz]
    push_cast
    rfl
  have he := design_variance Incident _ _ hg hp w
  rw [hv] at he
  rw [he]
  have hd : (∑ i ∈ range (n+2), (Nat.card K : ℝ)^i) -
      (∑ i ∈ range (n+1), (Nat.card K : ℝ)^i) = (Nat.card K : ℝ)^(n+1) := by
    rw [geom_sum_succ']; ring
  rw [hd]
  have hg := geom_design_identity (Nat.card K : ℝ) n
  rw [hg]
  field_simp
  ring

theorem projective_variance_le {n : ℕ} (hdim : Module.finrank K V = n+3)
    (w : Projectivization K V → ℝ) :
    ∑ y : Projectivization K (Module.Dual K V),
      (weightedIncidences Incident w y -
        (∑ i ∈ range (n+2), (Nat.card K : ℝ)^i) /
        (∑ i ∈ range (n+3), (Nat.card K : ℝ)^i) * ∑ x, w x)^2 ≤
      (Nat.card K : ℝ)^(n+1) * ∑ x, w x^2 := by
  rw [projective_variance hdim]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sub_le_self _ (by positivity)

noncomputable def incidenceCount (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) : ℕ :=
  ∑ y ∈ T, (S.filter (fun x => Incident x y)).card

theorem projective_mixing_sq {n : ℕ} (hdim : Module.finrank K V = n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    ((incidenceCount S T : ℝ) -
      (∑ i ∈ range (n+2), (Nat.card K : ℝ)^i) /
      (∑ i ∈ range (n+3), (Nat.card K : ℝ)^i) * S.card * T.card)^2 ≤
      (Nat.card K : ℝ)^(n+1) * S.card * T.card := by
  let w : Projectivization K V → ℝ := fun x => if x ∈ S then 1 else 0
  have hsum : ∑ x, w x = (S.card : ℝ) := by simp [w]
  have hsumsq : ∑ x, w x^2 = (S.card : ℝ) := by simp [w]
  have hc (y : Projectivization K (Module.Dual K V)) :
      weightedIncidences Incident w y = ((S.filter (fun x => Incident x y)).card : ℝ) := by
    simp [weightedIncidences, w, ← Finset.sum_filter]
    congr 1
    ext x
    simp [and_comm]
  let p : ℝ := (∑ i ∈ range (n+2), (Nat.card K : ℝ)^i) /
      (∑ i ∈ range (n+3), (Nat.card K : ℝ)^i)
  let f (y : Projectivization K (Module.Dual K V)) := weightedIncidences Incident w y - p*S.card
  have hf : ∑ y ∈ T, f y = (incidenceCount S T : ℝ) - p*S.card*T.card := by
    simp only [f, hc, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      incidenceCount, Nat.cast_sum]
    ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1:ℝ)) f
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  have hv := projective_variance_le hdim w
  rw [hsum, hsumsq] at hv
  have hsub : ∑ y ∈ T, f y^2 ≤ ∑ y, f y^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun _ _ _ => sq_nonneg _)
  calc
    _ = (∑ y ∈ T, f y)^2 := by rw [hf]
    _ ≤ (T.card : ℝ) * ∑ y ∈ T, f y^2 := hCS
    _ ≤ (T.card : ℝ) * ((Nat.card K : ℝ)^(n+1)*S.card) :=
      mul_le_mul_of_nonneg_left (hsub.trans hv) (by positivity)
    _ = _ := by ring

theorem sparse_product_bound {n : ℕ} (hdim : Module.finrank K V = n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V)))
    (hsparse : (incidenceCount S T : ℝ) ≤ (S.card : ℝ)*T.card/(4*Nat.card K)) :
    (S.card : ℝ)*T.card ≤ 16*(Nat.card K : ℝ)^(n+3) := by
  let q : ℝ := Nat.card K
  let v : ℝ := ∑ i ∈ range (n+3), q^i
  let k : ℝ := ∑ i ∈ range (n+2), q^i
  let a : ℝ := (S.card : ℝ)*T.card
  have hq : 1 < q := by
    change (1:ℝ) < (Nat.card K : ℝ)
    exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)
  have hk : 1 ≤ k := by
    have h0 : (1:ℝ) ≤ ∑ i ∈ range (n+2), q^i := by
      calc
        _ = q^0 := by simp
        _ ≤ ∑ i ∈ range (n+2), q^i :=
          single_le_sum (fun i hi => by positivity) (by simp)
    exact h0
  have hgeom : v = q*k+1 := geom_sum_succ
  have hv : 0 < v := by nlinarith
  have hp : 1/(2*q) ≤ k/v := by
    apply (div_le_div_iff₀ (by positivity) hv).mpr
    nlinarith
  have ha : 0 ≤ a := by positivity
  have hdev : a/(4*q) ≤ k/v*a-(incidenceCount S T : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hp ha
    change (incidenceCount S T : ℝ) ≤ a/(4*q) at hsparse
    have heq : (1/(2*q))*a = 2*(a/(4*q)) := by ring
    rw [heq] at hmul
    linarith
  have hsq := projective_mixing_sq hdim S T
  change ((incidenceCount S T : ℝ) - k/v*S.card*T.card)^2 ≤ q^(n+1)*S.card*T.card at hsq
  have hsq' : (a/(4*q))^2 ≤ q^(n+1)*a := by
    have hdnon : 0 ≤ k/v*a-(incidenceCount S T : ℝ) :=
      (by positivity : 0 ≤ a/(4*q)).trans hdev
    have h := (sq_le_sq₀ (by positivity : 0 ≤ a/(4*q)) hdnon).mpr hdev
    nlinarith [hsq]
  have hpow : q^(n+3) = q^(n+1)*q^2 := by rw [← pow_add]
  rw [hpow]
  by_cases haz : a = 0
  · change a ≤ _; rw [haz]; positivity
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hq0 : q ≠ 0 := by linarith
  have hcancel : (a/(4*q))^2 * (16*q^2) = a^2 := by field_simp; ring
  have hmult := mul_le_mul_of_nonneg_right hsq' (by positivity : 0 ≤ 16*q^2)
  rw [hcancel] at hmult
  change a ≤ _
  nlinarith [hmult]

end Projective
end SharpLogRamsey.Incidence

namespace SharpLogRamsey.Incidence
open SharpLogRamsey.Selection
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

noncomputable def endpointLabels
    (p : Law (Projectivization K V × Projectivization K (Module.Dual K V))) :=
  fun z : Projectivization K V × Projectivization K (Module.Dual K V) =>
    (levelIndex p.fst z.1,levelIndex p.snd z.2)

end SharpLogRamsey.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Marking

section FinitePotential
variable {Y : Type*} [Fintype Y]

noncomputable def level (r : Y → ℕ) (l : ℕ) : Finset Y := {y | r y = l}
noncomputable def below (r : Y → ℕ) (l : ℕ) : Finset Y := {y | r y ≤ l}
end FinitePotential

section State
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
abbrev Points := Projectivization K V
abbrev State := Points (K:=K) (V:=V) → Submodule K V
noncomputable def ranks (W : State (K:=K) (V:=V)) (y : Points (K:=K) (V:=V)) : ℕ :=
  Module.finrank K (W y)

noncomputable def update (W : State (K:=K) (V:=V))
    (a : Module.Dual K V) (b : Points (K:=K) (V:=V)) : State (K:=K) (V:=V) :=
  fun y => if a y.rep = 0 then W y ⊔ b.submodule else W y

def Popular (W : State (K:=K) (V:=V)) (q : ℝ) (l : ℕ)
    (b : Points (K:=K) (V:=V)) : Prop :=
  ((level (ranks W) l).card : ℝ)/(16*q) ≤
    ((level (ranks W) l).filter (fun y => b.submodule ≤ W y)).card

def Poor (W : State (K:=K) (V:=V)) (q : ℝ) (l : ℕ)
    (a : Module.Dual K V) : Prop :=
  (((level (ranks W) l).filter (fun y => a y.rep = 0)).card : ℝ) ≤
    (level (ranks W) l).card/(8*q)

noncomputable def chosenLevel (W : State (K:=K) (V:=V))
    (b : Points (K:=K) (V:=V)) : ℕ :=
  Classical.choose ((range (ranks W b + 1)).exists_max_image
    (fun l => (level (ranks W) l).card) ⟨0, by simp⟩)

def IsExpensive (W : State (K:=K) (V:=V)) (q : ℝ)
    (f : Module.Dual K V × Points (K:=K) (V:=V)) : Prop :=
  ¬ Popular W q (chosenLevel W f.2) f.2 ∧ ¬ Poor W q (chosenLevel W f.2) f.1

end State
end SharpLogRamsey.Marking

namespace SharpLogRamsey.Marking
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem geom_sum_le_twice {q : ℝ} (hq : 2 ≤ q) (r : ℕ) :
    (∑ i ∈ range (r+1), q^i) ≤ 2*q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, pow_succ]
    have hp : 0 ≤ q^r := pow_nonneg (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_right hq hp]

omit [Fintype (Projectivization K (Module.Dual K V))] in
omit [FiniteDimensional K V] in
theorem card_subspace_points_le (W : Submodule K V) {r : ℕ}
    (hW : Module.finrank K W = r+1) :
    ((univ.filter (fun b : Points (K:=K) (V:=V) => b.submodule ≤ W)).card:ℝ) ≤
      2*(Nat.card K:ℝ)^r := by
  have hc : (univ.filter (fun b : Points (K:=K) (V:=V) => b.submodule ≤ W)).card =
      ∑ i ∈ range (r+1), Nat.card K^i := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      ← Nat.card_congr (_root_.OAI.SharpLogRamsey.Incidence.projectiveSubmoduleEquiv W)]
    exact Projectivization.card_of_finrank K W hW
  rw [hc, Nat.cast_sum]
  push_cast
  apply geom_sum_le_twice
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)

noncomputable def poorDomain (W : State (K:=K) (V:=V)) (l : ℕ) :
    Finset (Projectivization K (Module.Dual K V)) :=
  univ.filter (fun a => Poor W (Nat.card K) l a.rep)

end SharpLogRamsey.Marking

namespace SharpLogRamsey.Marking
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

noncomputable def popularDomain (W : State (K:=K) (V:=V)) (l : ℕ) : Finset (Points (K:=K) (V:=V)) :=
  univ.filter (Popular W (Nat.card K) l)

end SharpLogRamsey.Marking
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_Popular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Marking
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

noncomputable def partnerDomain (W : Submodule K V) :
    Finset (Projectivization K (Module.Dual K V)) :=
  univ.filter (fun a => W ≤ LinearMap.ker a.rep)

noncomputable def popularJoint (W : State (K:=K) (V:=V)) (l r : ℕ) :
    Finset (Points (K:=K) (V:=V) × Projectivization K (Module.Dual K V)) :=
  (popularDomain W l).biUnion (fun b =>
    if ranks W b = r then (partnerDomain (W b)).image (Prod.mk b) else ∅)

end SharpLogRamsey.Marking
namespace SharpLogRamsey.Marking
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]

inductive ScanKind
  | popular | poor | expensive
  deriving DecidableEq

instance flat_ActualMarkingOrientation_1 : Fintype ScanKind := ⟨{.popular,.poor,.expensive}, by
  intro k
  cases k <;> simp⟩

def levelFromRank (W : State (K:=K) (V:=V)) (r : ℕ) : ℕ :=
  Classical.choose ((range (r+1)).exists_max_image
    (fun l => (level (ranks W) l).card) ⟨0,by simp⟩)

abbrev RankMask := Fin (Module.finrank K V+1) × ScanKind

abbrev ScanFlag := Module.Dual K V × Points (K:=K) (V:=V)

def replayStep (W : State (K:=K) (V:=V)) : Option (ScanFlag (K:=K) (V:=V)) →
    State (K:=K) (V:=V)
  | none => W
  | some f => update W f.1 f.2

def decodedCheap (q : ℝ) (W : State (K:=K) (V:=V))
    (m : RankMask (K:=K) (V:=V)) (f : ScanFlag (K:=K) (V:=V)) : Prop :=
  ranks W f.2 = m.1.val ∧
    match m.2 with
    | .popular => Popular W q (levelFromRank W m.1.val) f.2
    | .poor => Poor W q (levelFromRank W m.1.val) f.1
    | .expensive => False

end
end SharpLogRamsey.Marking
namespace SharpLogRamsey.Marking
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]

def ScanConsistent (fs : List (ScanFlag (K:=K) (V:=V))) : Prop :=
  fs.Pairwise (fun f g => f.1 g.2.rep = 0 → g.1 f.2.rep = 0)

omit [FiniteDimensional K V] in
lemma levelFromRank_spec (W : State (K:=K) (V:=V)) (r : ℕ) :
    levelFromRank W r ≤ r ∧ ∀ j ≤ r,
      (level (ranks W) j).card ≤ (level (ranks W) (levelFromRank W r)).card := by
  have h := Classical.choose_spec ((range (r+1)).exists_max_image
    (fun l => (level (ranks W) l).card) ⟨0,by simp⟩)
  simpa only [levelFromRank,mem_range,Nat.lt_succ_iff] using h

end
end SharpLogRamsey.Marking
namespace SharpLogRamsey.Marking
open Finset SharpLogRamsey.Incidence
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

abbrev ProjectivePair := Points (K:=K) (V:=V) × Projectivization K (Module.Dual K V)

def incidentPairs (S : Finset (Points (K:=K) (V:=V)))
    (T : Finset (Projectivization K (Module.Dual K V))) : Finset (ProjectivePair (K:=K) (V:=V)) :=
  (S ×ˢ T).filter (fun f => _root_.OAI.SharpLogRamsey.Incidence.Incident f.1 f.2)

def projectiveCheapDomain (W : State (K:=K) (V:=V)) (m : RankMask (K:=K) (V:=V)) :
    Finset (ProjectivePair (K:=K) (V:=V)) :=
  if m.1.val < Module.finrank K V then
    match m.2 with
    | .popular => popularJoint W (levelFromRank W m.1.val) m.1.val
    | .poor => incidentPairs (level (ranks W) m.1.val) (poorDomain W (levelFromRank W m.1.val))
    | .expensive => ∅
  else ∅

end
end SharpLogRamsey.Marking
namespace SharpLogRamsey.ProjectiveDuality
open SharpLogRamsey.Incidence
noncomputable section
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

def mapEquiv (e : V ≃ₗ[K] W) : Projectivization K V ≃ Projectivization K W where
  toFun := Projectivization.map e.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearMap e.symm.injective
  left_inv p := by
    induction p using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk, LinearEquiv.coe_coe, e.symm_apply_apply]
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk, LinearEquiv.coe_coe, e.apply_symm_apply]

variable [FiniteDimensional K V]
def bidual : Projectivization K V ≃ Projectivization K (Module.Dual K (Module.Dual K V)) :=
  mapEquiv (Module.evalEquiv K V)

lemma incident_bidual (y : Projectivization K V) (b : Projectivization K (Module.Dual K V)) :
    _root_.OAI.SharpLogRamsey.Incidence.Incident b (bidual y) ↔ _root_.OAI.SharpLogRamsey.Incidence.Incident y b := by
  have he : bidual y = Projectivization.mk K ((Module.evalEquiv K V) y.rep)
      (by simpa using (Module.evalEquiv K V).injective.ne y.rep_nonzero) := by
    conv_lhs => rw [← y.mk_rep]
    rfl
  rw [_root_.OAI.SharpLogRamsey.Incidence.Incident, he]
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep K ((Module.evalEquiv K V) y.rep)
    (by simpa using (Module.evalEquiv K V).injective.ne y.rep_nonzero)
  rw [← hu]
  simp [Units.smul_def, _root_.OAI.SharpLogRamsey.Incidence.Incident]

end
end SharpLogRamsey.ProjectiveDuality
namespace SharpLogRamsey
section Flags
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

def Incident (a : Projectivization K V)
    (b : Projectivization K (Module.Dual K V)) : Prop := b.rep a.rep = 0
structure Flag where
  point : Projectivization K V
  dualPoint : Projectivization K (Module.Dual K V)
  incident : Incident K V point dualPoint
variable {K V}
def Consistent {N : ℕ} (F : Fin N → Flag K V) : Prop :=
  ∀ i j, i < j → Incident K V (F i).point (F j).dualPoint →
    Incident K V (F j).point (F i).dualPoint
end Flags
end SharpLogRamsey

namespace SharpLogRamsey.Marking
open ProjectiveDuality
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def backwardScan {N : ℕ} (F : Fin N → Flag K V) : List (ScanFlag (K:=K) (V:=V)) :=
  List.ofFn (fun i => ((F i.rev).dualPoint.rep,(F i.rev).point))

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_FlagConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey

section Flags
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

theorem incident_iff_submodule (a : Projectivization K V)
    (b : Projectivization K (Module.Dual K V)) :
    Incident K V a b ↔ a.submodule ≤ LinearMap.ker b.rep := by
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
  rfl

def flagGraph {N : ℕ} (F : Fin N → Flag K V) : SimpleGraph (Fin N) where
  Adj i j :=
    (i < j ∧ Incident K V (F i).point (F j).dualPoint ∧
      ¬ Incident K V (F j).point (F i).dualPoint) ∨
    (j < i ∧ Incident K V (F j).point (F i).dualPoint ∧
      ¬ Incident K V (F i).point (F j).dualPoint)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i => by simp⟩

variable {K V}

theorem flagGraph_adj_of_lt {N : ℕ} (F : Fin N → Flag K V)
    {i j : Fin N} (hij : i < j) :
    (flagGraph K V F).Adj i j ↔
      Incident K V (F i).point (F j).dualPoint ∧
      ¬ Incident K V (F j).point (F i).dualPoint := by
  simp only [flagGraph, hij, true_and, not_lt_of_ge hij.le, false_and, or_false]

def ConsistentOn {N : ℕ} (F : Fin N → Flag K V) (S : Finset (Fin N)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i < j → Incident K V (F i).point (F j).dualPoint →
    Incident K V (F j).point (F i).dualPoint

theorem consistentOn_iff_compl_isClique {N : ℕ} (F : Fin N → Flag K V)
    (S : Finset (Fin N)) :
    ConsistentOn F S ↔ (flagGraph K V F)ᶜ.IsClique S := by
  constructor
  · intro h i hi j hj hne
    rw [SimpleGraph.compl_adj]
    refine ⟨hne, ?_⟩
    rintro (⟨hij, hinc, hnot⟩ | ⟨hji, hinc, hnot⟩)
    · exact hnot (h i hi j hj hij hinc)
    · exact hnot (h j hj i hi hji hinc)
  · intro h i hi j hj hij hinc
    have hnot := ((flagGraph K V F).compl_adj i j).mp (h hi hj (ne_of_lt hij))
    by_contra hrev
    exact hnot.2 ((flagGraph_adj_of_lt F hij).mpr ⟨hinc, hrev⟩)

noncomputable def projectiveSubmoduleEquiv (W : Submodule K V) :
    Projectivization K W ≃ {a : Projectivization K V // a.submodule ≤ W} := by
  let f : Projectivization K W → {a : Projectivization K V // a.submodule ≤ W} :=
    fun a => ⟨Projectivization.map W.subtype W.injective_subtype a, by
      induction a using Projectivization.ind with
      | h v hv =>
        rw [Projectivization.map_mk, Projectivization.submodule_mk,
          Submodule.span_singleton_le_iff_mem]
        exact v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    exact Projectivization.map_injective W.subtype W.injective_subtype
      (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    have hmem : a.rep ∈ W := ha (by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _)
    let v : W := ⟨a.rep, hmem⟩
    have hv : v ≠ 0 := fun h => a.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    exact a.mk_rep

theorem card_incident_points [Finite K] [FiniteDimensional K V] {d : ℕ}
    (hdim : Module.finrank K V = d+1)
    (b : Projectivization K (Module.Dual K V)) :
    Nat.card {a : Projectivization K V // Incident K V a b} =
      ∑ i ∈ Finset.range d, Nat.card K ^ i := by
  let e : {a : Projectivization K V // Incident K V a b} ≃
      {a : Projectivization K V // a.submodule ≤ LinearMap.ker b.rep} :=
    Equiv.subtypeEquivRight (fun a => incident_iff_submodule K V a b)
  rw [Nat.card_congr e, ← Nat.card_congr (projectiveSubmoduleEquiv (LinearMap.ker b.rep))]
  apply Projectivization.card_of_finrank
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  omega

theorem card_flags [Finite K] [FiniteDimensional K V] {d : ℕ}
    (hdim : Module.finrank K V = d+1) :
    Nat.card (Flag K V) =
      (∑ i ∈ Finset.range (d+1), Nat.card K ^ i) *
      (∑ i ∈ Finset.range d, Nat.card K ^ i) := by
  classical
  let : Finite V := Finite.of_injective (Module.finBasis K V).equivFun
    (Module.finBasis K V).equivFun.injective
  let : Finite (Module.Dual K V) :=
    Finite.of_injective (Module.finBasis K (Module.Dual K V)).equivFun
      (Module.finBasis K (Module.Dual K V)).equivFun.injective
  let : Finite (Projectivization K V) :=
    Finite.of_injective Projectivization.rep (fun a b h => by
      rw [← a.mk_rep, ← b.mk_rep]; congr 1)
  let : Finite (Projectivization K (Module.Dual K V)) :=
    Finite.of_injective Projectivization.rep (fun a b h => by
      rw [← a.mk_rep, ← b.mk_rep]; congr 1)
  let := Fintype.ofFinite (Projectivization K (Module.Dual K V))
  let e : Flag K V ≃ Σ b : Projectivization K (Module.Dual K V),
      {a : Projectivization K V // Incident K V a b} :=
    { toFun := fun f => ⟨f.dualPoint, f.point, f.incident⟩
      invFun := fun f => ⟨f.2.1, f.1, f.2.2⟩
      left_inv := fun f => by cases f; rfl
      right_inv := fun f => by cases f; rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [card_incident_points hdim]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  rw [Projectivization.card_of_finrank K (Module.Dual K V)
    (Subspace.dual_finrank_eq.trans hdim)]

end Flags
end SharpLogRamsey

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_InitialRectangles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.InitialRectangles
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedInitialRectangles_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedInitialRectangles_2 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective Projectivization.rep (fun a b h => by
    rw [←a.mk_rep,←b.mk_rep]; congr 1)
local instance flat_JoinedInitialRectangles_3 : Finite (Projectivization K (Module.Dual K V)) :=
  Finite.of_injective Projectivization.rep (fun a b h => by
    rw [←a.mk_rep,←b.mk_rep]; congr 1)
local instance flat_JoinedInitialRectangles_4 : Finite (Flag K V) :=
  Finite.of_injective (fun f : Flag K V => (f.point,f.dualPoint)) (by
    intro a b h
    cases a; cases b
    cases h
    rfl)
local instance flat_JoinedInitialRectangles_5 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective

def IsRectangle (W : Submodule K V) (f : Flag K V) : Prop :=
  f.point.submodule≤W ∧ f.dualPoint.submodule≤W.dualAnnihilator

omit [FiniteDimensional K V] in
lemma card_points (W : Submodule K V) :
    Nat.card {a : Projectivization K V // a.submodule≤W} =
      ∑ i∈range (Module.finrank K W),(Nat.card K)^i := by
  rw [←Nat.card_congr (projectiveSubmoduleEquiv W)]
  exact Projectivization.card_of_finrank K W rfl

lemma card_rectangle_le (W : Submodule K V) :
    Nat.card {f : Flag K V // IsRectangle W f} ≤
      (∑ i∈range (Module.finrank K W),(Nat.card K)^i)*
      (∑ i∈range (Module.finrank K W.dualAnnihilator),(Nat.card K)^i) := by
  let f : {f : Flag K V // IsRectangle W f} →
      {a : Projectivization K V // a.submodule≤W} ×
      {b : Projectivization K (Module.Dual K V) // b.submodule≤W.dualAnnihilator} :=
    fun z => (⟨z.1.point,z.2.1⟩,⟨z.1.dualPoint,z.2.2⟩)
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have hp := congrArg (fun z => z.1.val) h
    have hd := congrArg (fun z => z.2.val) h
    cases a with | mk a ha =>
      cases b with | mk b hb =>
        cases a; cases b
        simp only [f] at hp hd
        cases hp; cases hd; rfl
  exact (Nat.card_le_card_of_injective f hi).trans_eq (by
    rw [Nat.card_prod,card_points,card_points])

lemma card_subspaces_le :
    Nat.card (Submodule K V)≤(Nat.card K)^(Module.finrank K V)^2 := by
  let : Finite V := Module.finite_of_finite K
  let : Finite (V→ₗ[K]V) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have hs : Function.Surjective (LinearMap.range : (V→ₗ[K]V)→Submodule K V) := by
    intro W
    obtain ⟨Q,hQ⟩ := W.exists_isCompl
    exact ⟨W.projection Q hQ,W.range_projection hQ⟩
  apply (Nat.card_le_card_of_surjective _ hs).trans_eq
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (V→ₗ[K]V) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card,Module.finrank_linearMap,pow_two] using
    (Module.card_eq_pow_finrank (K:=K) (V:=V→ₗ[K]V))

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma sum_powers_le_two {q n : ℕ} (hq : 2≤q) (hn : 0<n) :
    ∑ i∈range n,q^i≤2*q^(n-1) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  clear hn
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel] at *
    have hm : 2*q^m≤q^(m+1) := by
      rw [pow_succ]
      simpa only [mul_comm] using Nat.mul_le_mul_left (q^m) hq
    omega

lemma card_rectangle_bound {d : ℕ} (hd : 1≤d)
    (hdim : Module.finrank K V=d+1) (W : Submodule K V) :
    Nat.card {f : Flag K V // IsRectangle W f} ≤ 4*(Nat.card K)^(d-1) := by
  have hq : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  have hs := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  rw [hdim] at hs
  let r := Module.finrank K W
  let s := Module.finrank K W.dualAnnihilator
  by_cases hr : r=0
  · apply (card_rectangle_le W).trans
    change (∑ i∈range r,(Nat.card K)^i)*_≤_
    simp [hr]
  by_cases ht : s=0
  · apply (card_rectangle_le W).trans
    change _*(∑ i∈range s,(Nat.card K)^i)≤_
    simp [ht]
  have he : (r-1)+(s-1)=d-1 := by dsimp [r,s] at *; omega
  calc
    _ ≤ (∑ i∈range r,(Nat.card K)^i)*(∑ i∈range s,(Nat.card K)^i) := card_rectangle_le W
    _ ≤ (2*(Nat.card K)^(r-1))*(2*(Nat.card K)^(s-1)) :=
      Nat.mul_le_mul (sum_powers_le_two hq (Nat.pos_of_ne_zero hr))
        (sum_powers_le_two hq (Nat.pos_of_ne_zero ht))
    _ = _ := by rw [show (2*(Nat.card K)^(r-1))*(2*(Nat.card K)^(s-1))=
        4*((Nat.card K)^(r-1)*(Nat.card K)^(s-1)) by ring,←pow_add,he]

lemma card_flags_lower {d : ℕ} (hd : 1≤d) (hdim : Module.finrank K V=d+1) :
    (Nat.card K)^(2*d-1)≤Nat.card (Flag K V) := by
  rw [card_flags hdim]
  have h1 : (Nat.card K)^d≤∑ i∈range (d+1),(Nat.card K)^i :=
    single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
  have h2 : (Nat.card K)^(d-1)≤∑ i∈range d,(Nat.card K)^i :=
    single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
  have he : 2*d-1=d+(d-1) := by omega
  rw [he,pow_add]
  exact Nat.mul_le_mul h1 h2

lemma finite_flags : Finite (Flag K V) := inferInstance

lemma finite_subspaces : Finite (Submodule K V) := inferInstance

end
end SharpLogRamsey.InitialRectangles

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_RectangleStreamEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.RectangleStreamEvent
open Finset Real InitialRectangles FiniteStreamTail
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedRectangleStreamEvent_1 : Fintype (Flag K V) := @Fintype.ofFinite _ (finite_flags (K:=K) (V:=V))
local instance flat_JoinedRectangleStreamEvent_2 : Fintype (Submodule K V) := @Fintype.ofFinite _ (finite_subspaces (K:=K) (V:=V))

def rectangle (W : Submodule K V) : Finset (Flag K V) :=
  univ.filter (IsRectangle W)

lemma rectangle_card {d : ℕ} (hd : 1≤d) (hdim : Module.finrank K V=d+1)
    (W : Submodule K V) : (rectangle W).card≤4*(Nat.card K)^(d-1) := by
  convert card_rectangle_bound hd hdim W using 1
  all_goals try with_reducible_and_instances rfl
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl

lemma flags_card_pos {d : ℕ} (hd : 1≤d) (hdim : Module.finrank K V=d+1) :
    0<Fintype.card (Flag K V) := by
  have h := card_flags_lower hd hdim
  rw [Nat.card_eq_fintype_card (α:=Flag K V)] at h
  exact lt_of_lt_of_le (pow_pos (Nat.card_pos (α:=K)) _) h

lemma rectangle_probability {d : ℕ} (hd : 1≤d) (hdim : Module.finrank K V=d+1)
    (W : Submodule K V) : probability (rectangle W)≤4/(Nat.card K:ℝ)^d := by
  have hp : 0<(Nat.card K:ℝ) := by exact_mod_cast (show 0<Nat.card K from Nat.card_pos)
  have hf : 0<(Fintype.card (Flag K V):ℝ) := by exact_mod_cast flags_card_pos hd hdim
  have hc : ((rectangle W).card:ℝ)≤4*(Nat.card K:ℝ)^(d-1) := by
    exact_mod_cast rectangle_card hd hdim W
  have hb : (Nat.card K:ℝ)^(2*d-1)≤Fintype.card (Flag K V) := by
    exact_mod_cast (show (Nat.card K)^(2*d-1)≤Fintype.card (Flag K V) by
      simpa only [Nat.card_eq_fintype_card] using card_flags_lower hd hdim)
  unfold probability
  calc
    _ ≤ (4*(Nat.card K:ℝ)^(d-1))/(Nat.card K:ℝ)^(2*d-1) :=
      div_le_div₀ (by positivity) hc (by positivity) hb
    _ = _ := by
      have he : 2*d-1=d+(d-1) := by omega
      rw [he,pow_add]
      field_simp

lemma rectangle_mean {d N : ℕ} (hd : 1≤d) (hdim : Module.finrank K V=d+1)
    (hN : (N:ℝ)≤(Nat.card K:ℝ)^d*log (Nat.card K)) (W : Submodule K V) :
    (N:ℝ)*probability (rectangle W)≤4*log (Nat.card K) := by
  have hp : 0<(Nat.card K:ℝ) := by exact_mod_cast (show 0<Nat.card K from Nat.card_pos)
  calc
    _ ≤ N*(4/(Nat.card K:ℝ)^d) :=
      mul_le_mul_of_nonneg_left (rectangle_probability hd hdim W) (Nat.cast_nonneg _)
    _ ≤ ((Nat.card K:ℝ)^d*log (Nat.card K))*(4/(Nat.card K:ℝ)^d) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by field_simp

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma union_exponent (q : ℝ) (hq : 0<q) (n : ℕ) :
    q^n*exp (4*log q-(((n:ℝ)+5)/log 2*log q)*log 2)=1/q := by
  have hl : log (2:ℝ)≠0 := ne_of_gt (log_pos (by norm_num))
  have he : 4*log q-(((n:ℝ)+5)/log 2*log q)*log 2=
      -(n:ℝ)*log q-log q := by field_simp; ring
  rw [he]
  have hpow : q^n=exp ((n:ℝ)*log q) := by rw [exp_nat_mul,exp_log hq]
  rw [hpow,←exp_add]
  rw [show (n:ℝ)*log q+(-(n:ℝ)*log q-log q)= -log q by ring,
    exp_neg,exp_log hq,one_div]

theorem simultaneous_rectangle_tail {d N : ℕ} (hd : 1≤d)
    (hdim : Module.finrank K V=d+1)
    (hN : (N:ℝ)≤(Nat.card K:ℝ)^d*log (Nat.card K)) :
    probability (univ.filter (fun z : Fin N→Flag K V=>∃ W : Submodule K V,
      (((d+1)^2:ℕ)+5:ℝ)/log 2*log (Nat.card K)≤hits (rectangle W) z)) ≤
        1/(Nat.card K:ℝ) := by
  have hf := flags_card_pos hd hdim
  let : Nonempty (Flag K V) := Fintype.card_pos_iff.mp hf
  let t : ℝ := (((d+1)^2:ℕ)+5:ℝ)/log 2*log (Nat.card K)
  have hs := simultaneous_tail (rectangle (K:=K) (V:=V)) N t (4*log (Nat.card K))
    (rectangle_mean hd hdim hN)
  have hc : (Fintype.card (Submodule K V):ℝ)≤(Nat.card K:ℝ)^((d+1)^2) := by
    have h := card_subspaces_le (K:=K) (V:=V)
    rw [hdim,Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  calc
    _ ≤ (Fintype.card (Submodule K V):ℝ)*exp (4*log (Nat.card K)-t*log 2) := hs
    _ ≤ (Nat.card K:ℝ)^((d+1)^2)*exp (4*log (Nat.card K)-t*log 2) :=
      mul_le_mul_of_nonneg_right hc (le_of_lt (exp_pos _))
    _ = _ := union_exponent _ (by exact_mod_cast (show 0<Nat.card K from Nat.card_pos)) _

theorem simultaneous_good_probability {d N : ℕ} (hd : 1≤d)
    (hdim : Module.finrank K V=d+1)
    (hN : (N:ℝ)≤(Nat.card K:ℝ)^d*log (Nat.card K)) :
    1-1/(Nat.card K:ℝ) ≤
    probability (univ.filter (fun z : Fin N→Flag K V=>∀ W : Submodule K V,
      (hits (rectangle W) z:ℝ)<(((d+1)^2:ℕ)+5:ℝ)/log 2*log (Nat.card K))) := by
  let : Nonempty (Flag K V) := Fintype.card_pos_iff.mp (flags_card_pos hd hdim)
  let B := univ.filter (fun z : Fin N→Flag K V=>∃ W : Submodule K V,
      (((d+1)^2:ℕ)+5:ℝ)/log 2*log (Nat.card K)≤hits (rectangle W) z)
  have he : Bᶜ=univ.filter (fun z : Fin N→Flag K V=>∀ W : Submodule K V,
      (hits (rectangle W) z:ℝ)<(((d+1)^2:ℕ)+5:ℝ)/log 2*log (Nat.card K)) := by
    ext z
    simp only [B,mem_compl,mem_filter,mem_univ,true_and,not_exists,not_le]
  rw [←he]
  have hc : probability Bᶜ=1-probability B := by
    convert probability_compl B using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext z
    simp
  rw [hc]
  exact sub_le_sub_left (simultaneous_rectangle_tail hd hdim hN) 1

end
end SharpLogRamsey.RectangleStreamEvent

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open scoped Classical BigOperators
open Finset
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]

def toScan (f : ProjectivePair (K:=K) (V:=V)) : ScanFlag (K:=K) (V:=V) :=
  (f.2.rep,f.1)

def pairStep (W : State (K:=K) (V:=V)) (s : Option (ProjectivePair (K:=K) (V:=V))) :
    State (K:=K) (V:=V) := replayStep W (s.map toScan)

def pairReplay : State (K:=K) (V:=V) → List (Option (ProjectivePair (K:=K) (V:=V))) →
    State (K:=K) (V:=V)
  | W,[] => W
  | W,s::ss => pairReplay (pairStep W s) ss

def expensiveMask {N : ℕ} (M : Fin N → RankMask (K:=K) (V:=V)) : Finset (Fin N) :=
  univ.filter (fun i => (M i).2=.expensive)

def cheapTuple {Γ : Type*} {N : ℕ}
    (θ : (Fin N → Option (ProjectivePair (K:=K) (V:=V))) ×
      (Γ × (Fin N → RankMask (K:=K) (V:=V)))) (i : Fin N) :
    Finset (ProjectivePair (K:=K) (V:=V)) :=
  projectiveCheapDomain (pairReplay (fun _ => ⊥) ((List.ofFn θ.1).take i.val)) (θ.2.2 i)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_FinalMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey
open scoped Classical BigOperators
open Finset
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

 def flagPair (f : Flag K V) : Marking.ProjectivePair (K:=K) (V:=V) :=
  (f.point,f.dualPoint)

 def flagPairEquiv : Flag K V ≃
    {f : Marking.ProjectivePair (K:=K) (V:=V) // Incidence.Incident f.1 f.2} where
  toFun f := ⟨flagPair f,f.incident⟩
  invFun f := ⟨f.1.1,f.1.2,f.2⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
instance flagFintype : Fintype (Flag K V) := Fintype.ofEquiv _ flagPairEquiv.symm

end
end SharpLogRamsey

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingTwoScans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open scoped BigOperators Classical
open Finset ProjectiveDuality
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def pairDuality : ProjectivePair (K:=K) (V:=V) ≃
    ProjectivePair (K:=K) (V:=Module.Dual K V) where
  toFun f := (f.2,bidual f.1)
  invFun f := (bidual.symm f.2,f.1)
  left_inv f := by simp
  right_inv f := by simp

abbrev TwoMask (N : ℕ) := (Fin N → RankMask (K:=K) (V:=V)) ×
  (Fin N → RankMask (K:=K) (V:=Module.Dual K V))

def bothExpensive {N : ℕ} (m : TwoMask (K:=K) (V:=V) N) : Finset (Fin N) :=
  expensiveMask m.1 ∪ (expensiveMask m.2).image Fin.rev

abbrev TwoMessage (Γ : Type*) (N : ℕ) :=
  (Fin N → Option (ProjectivePair (K:=K) (V:=V))) × (Γ × TwoMask (K:=K) (V:=V) N)

def firstMessage {Γ : Type*} {N : ℕ} (z : TwoMessage (K:=K) (V:=V) Γ N) :
    (Fin N → Option (ProjectivePair (K:=K) (V:=V))) ×
      (Γ × (Fin N → RankMask (K:=K) (V:=V))) :=
  (fun i => if i∈expensiveMask z.2.2.1 then z.1 i else none,(z.2.1,z.2.2.1))

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ReciprocalBands
open Real
noncomputable section

def IntegerBand (r : ℕ) (σ K u : ℝ) : Prop := |u-(r:ℝ)*σ|≤K
def OpenBand (r : ℕ) (σ K u : ℝ) : Prop :=
  ((r:ℝ)-1)*σ+K<u ∧ u<(r:ℝ)*σ-K

end
end SharpLogRamsey.ReciprocalBands

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingClassification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]

omit [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma ambient_point_bound {d : ℕ} (hdim : Module.finrank K V=d+1)
    (S : Finset (Projectivization K V)) : (S.card:ℝ)≤2*(Nat.card K:ℝ)^d := by
  have ht : Module.finrank K (⊤ : Submodule K V)=d+1 := by
    simpa using hdim
  have hb := card_subspace_points_le (⊤ : Submodule K V) ht
  have hcard : (S.card:ℝ)≤(Fintype.card (Projectivization K V):ℝ) := by
    exact_mod_cast card_le_univ S
  exact hcard.trans (by simpa using hb)

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MarkingFiniteClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset ReciprocalBands
open scoped Classical
noncomputable section

abbrev SlotClass (d : ℕ) := (Bool×Fin (d+1))⊕(Fin (d+1)×Fin (d+1))

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def ValidSlotClass (d : ℕ) (gap : ℝ)
    (D : Finset (ProjectivePair (K:=K) (V:=V))) : SlotClass d→Prop
  | .inl (integer,r) => ∃ u : ℝ,
      Real.log (Nat.card K:ℝ)≤u ∧ u≤(d:ℝ)*Real.log (Nat.card K:ℝ) ∧
      ((D.image Prod.fst).card:ℝ)≤1024*Real.exp (((d:ℝ)+1)*Real.log (Nat.card K:ℝ)-u) ∧
      ((D.image Prod.snd).card:ℝ)≤1024*Real.exp u ∧
      1 ≤ r.val ∧ (if integer then IntegerBand r.val (Real.log (Nat.card K:ℝ)) gap u
        else 2 ≤ r.val ∧ OpenBand r.val (Real.log (Nat.card K:ℝ)) gap u)
  | .inr (r,r') =>
      1 ≤ r.val ∧ 1 ≤ r'.val ∧ d+1 < r.val+r'.val ∧
      ((D.image Prod.fst).card:ℝ)≤32*(Nat.card K:ℝ)^r.val ∧
      ((D.image Prod.snd).card:ℝ)≤32*(Nat.card K:ℝ)^r'.val ∧
      (∀ b,((D.filter (fun f=>f.1=b)).card:ℝ)≤2*(Nat.card K:ℝ)^(d-r.val)) ∧
      (∀ a,((D.filter (fun f=>f.2=a)).card:ℝ)≤2*(Nat.card K:ℝ)^(d-r'.val))

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_SupportMixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open Finset
open scoped Classical
namespace SharpLogRamsey.SupportMixtures
noncomputable section
variable {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

 def kernel (S : Finset A) (a : A) : ℝ :=
  if a∈S then 1/(S.card:ℝ) else 0

 def pairing (f : A→ℝ) (g : B→ℝ) (R : A→B→ℝ) : ℝ :=
  ∑ a, ∑ b, f a*g b*R a b

end
end SharpLogRamsey.SupportMixtures

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_EndpointSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

def Law.swap (p : Law (A × B)) : Law (B × A) where
  mass z := p.mass (z.2,z.1)
  nonneg z := p.nonneg _
  total := by
    rw [Fintype.sum_prod_type, sum_comm, ← Fintype.sum_prod_type]
    exact p.total

@[simp] lemma Law.swap_mass (p : Law (A × B)) (b : B) (a : A) :
    p.swap.mass (b,a) = p.mass (a,b) := rfl

@[simp] lemma Law.swap_fst (p : Law (A × B)) : p.swap.fst = p.snd := rfl

@[simp] lemma Law.swap_snd (p : Law (A × B)) : p.swap.snd = p.fst := rfl

structure AuxiliarySupport (p : Law A) (good : Finset A) (M κ : ℝ) where
  law : Law (retainedLevels p good M κ)
  size : ∀ b : retainedLevels p good M κ,
    M * exp (-κ) / 2 ≤ ((levelSet p b ∩ good).card : ℝ) ∧
      ((levelSet p b ∩ good).card : ℝ) ≤ M
  density : ∀ a, (∑ b : retainedLevels p good M κ, law.mass b *
    (if a ∈ levelSet p b ∩ good then 1 / ((levelSet p b ∩ good).card : ℝ) else 0))
      ≤ 4 * exp 1 * p.mass a

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_PencilGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Classical
namespace SharpLogRamsey.CertificateGeometry
open SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
noncomputable section
local instance flat_JoinedPencilGeometry_3 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPencilGeometry_4 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

end
end SharpLogRamsey.CertificateGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma rep_mem_line_iff (p z : Projectivization K V) : p.rep ∈ z.submodule ↔ p = z := by
  rw [Projectivization.submodule_eq,Submodule.mem_span_singleton]
  constructor
  · intro h
    exact p.mk_rep.symm.trans (((Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr h).trans z.mk_rep)
  · intro h
    subst p
    exact ⟨1,one_smul K z.rep⟩

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.FiniteImage
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*}

def collisions (s : Finset α) (f : α → β) : ℕ :=
  (s.offDiag.filter (fun ab => f ab.1 = f ab.2)).card

end
end SharpLogRamsey.FiniteImage

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_ExternalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
variable (label : D → Option C) (R : ℕ)

variable (color : V → C) (s : V → Finset D) (b : ℝ) (own : V → Fin R → Bool)

abbrev IntDir (c : C) := {d : D // label d = some c}

end SharpRamseyFive.TupleComponents
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestPointTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

open MeasureTheory
open scoped BigOperators Classical

namespace SharpLogRamsey.BoundedProbability
open MeasureTheory Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω A B I : Type*} [MeasurableSpace Ω]
  [MeasurableSpace A] [MeasurableSpace B]

def eventCount (S : Finset I) (E : I → Set Ω) (ω : Ω) : ℝ :=
  ∑ i∈S,if ω∈E i then 1 else 0

end
end SharpLogRamsey.BoundedProbability

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_SparseProductSharp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Incidence
open Finset
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
variable [Fintype (Projectivization K (Module.Dual K V))]

theorem sparse_product_bound_two {n : ℕ} (hdim : Module.finrank K V = n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V)))
    (hsparse : (incidenceCount S T : ℝ) ≤ (S.card : ℝ)*T.card/(20*Nat.card K)) :
    (S.card : ℝ)*T.card ≤ 2*(Nat.card K : ℝ)^(n+3) := by
  let q : ℝ := Nat.card K
  let v : ℝ := ∑ i ∈ range (n+3), q^i
  let k : ℝ := ∑ i ∈ range (n+2), q^i
  let a : ℝ := (S.card : ℝ)*T.card
  have hq : 2 ≤ q := by
    have hh : 2 ≤ Nat.card K := Finite.one_lt_card
    change (2:ℝ) ≤ (Nat.card K:ℝ)
    exact_mod_cast hh
  have hk : 1+q ≤ k := by
    calc
      _ = ∑ i ∈ range 2, q^i := by norm_num [sum_range_succ]
      _ ≤ ∑ i ∈ range (n+2), q^i :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intros; positivity)
  have hgeom : v = q*k+1 := geom_sum_succ
  have hv : 0 < v := by nlinarith
  have hp : 4/(5*q) ≤ k/v := by
    apply (div_le_div_iff₀ (by positivity) hv).mpr
    nlinarith
  have ha : 0 ≤ a := by positivity
  have hdev : 3*a/(4*q) ≤ k/v*a-(incidenceCount S T : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hp ha
    change (incidenceCount S T : ℝ) ≤ a/(20*q) at hsparse
    have hid : (4/(5*q))*a = 16*(a/(20*q)) := by ring
    have hid' : 3*a/(4*q) = 15*(a/(20*q)) := by ring
    rw [hid] at hmul
    rw [hid']
    have hnon : 0 ≤ a/(20*q) := by positivity
    linarith
  have hsq := projective_mixing_sq hdim S T
  change ((incidenceCount S T : ℝ) - k/v*S.card*T.card)^2 ≤ q^(n+1)*S.card*T.card at hsq
  have hsq' : (3*a/(4*q))^2 ≤ q^(n+1)*a := by
    have hdnon : 0 ≤ k/v*a-(incidenceCount S T : ℝ) :=
      (by positivity : 0 ≤ 3*a/(4*q)).trans hdev
    have hh := (sq_le_sq₀ (by positivity : 0 ≤ 3*a/(4*q)) hdnon).mpr hdev
    nlinarith [hsq]
  have hpow : q^(n+3) = q^(n+1)*q^2 := by rw [← pow_add]
  rw [hpow]
  by_cases haz : a = 0
  · change a ≤ _; rw [haz]; positivity
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hq0 : q ≠ 0 := by linarith
  have hcancel : (3*a/(4*q))^2 * (16*q^2) = 9*a^2 := by
    calc
      _ = (9*a^2/(16*q^2))*(16*q^2) := by ring
      _ = 9*a^2 := div_mul_cancel₀ _ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hq0))
  have hmult := mul_le_mul_of_nonneg_right hsq' (by positivity : 0 ≤ 16*q^2)
  rw [hcancel] at hmult
  change a ≤ _
  nlinarith [hmult]

end SharpLogRamsey.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology

noncomputable def beta (η : ℝ) : ℝ := η/10000000
noncomputable def scaleL (σ η D : ℝ) : ℝ := D*σ^(8*beta η)
noncomputable def scaleP (σ η D : ℝ) (R : ℕ) : ℝ := scaleL σ η D*R

structure Admissible (σ η D : ℝ) (R : ℕ) : Prop where
  D_lower : σ^beta η ≤ D
  D_upper : D ≤ σ^(1-η/2)
  R_lower : σ^beta η ≤ (R : ℝ)
  R_upper : (R : ℝ) ≤ 2*σ^beta η+2
  R_even : Even R

end SharpLogRamsey.SourceScales
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScaleComparisons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

def scaleKstar (σ η D : ℝ) : ℝ := D*σ^(6*beta η)

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_GreedyIndexed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

def residual (S : Finset α) (U : β → Finset α) : List β → Finset α
  | [] => S
  | b::bs => residual (S \ U b) U bs

def cells (S : Finset α) (U : β → Finset α) : List β → List (Finset α)
  | [] => []
  | b::bs => (S ∩ U b)::cells (S \ U b) U bs

inductive Complete (F : Finset β) (U : β → Finset α) (m : ℕ) : Finset α → List β → Prop
  | nil (S : Finset α) (h : ∀ b ∈ F, (S ∩ U b).card < m) : Complete F U m S []
  | cons (S : Finset α) (b : β) (bs : List β) (hb : b ∈ F)
      (hrich : m ≤ (S ∩ U b).card)
      (hmax : ∀ c ∈ F, (S ∩ U c).card ≤ (S ∩ U b).card)
      (tail : Complete F U m (S \ U b) bs) : Complete F U m S (b::bs)

lemma cells_length (S : Finset α) (U : β → Finset α) (bs : List β) :
    (cells S U bs).length = bs.length := by
  induction bs generalizing S with
  | nil => rfl
  | cons b bs ih => simp [cells,ih]

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

def removed (S : Finset α) (U : β → Finset α) (bs : List β) : Finset α :=
  S \ residual S U bs

def own (S : Finset α) (U : β → Finset α) : List β → α → Finset α
  | [], _ => ∅
  | b::bs, x => if x ∈ U b then S ∩ U b else own (S \ U b) U bs x

end
end SharpLogRamsey.GreedyPreparation

namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*}

def indexedCell (S : Finset α) (U : β → Finset α) (bs : List β)
    (i : Fin bs.length) : Finset α := residual S U (bs.take i.val) ∩ U bs[i.val]

end
end SharpLogRamsey.GreedyPreparation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_TestLearningRowBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace SharpLogRamsey.PoissonSchedules
variable {ι : Type*} [Fintype ι]

def emptyLedger (A : Finset ι) : Set (ι → ℕ) := {x | ∀ i ∈ A, x i = 0}

end SharpLogRamsey.PoissonSchedules
namespace SharpLogRamsey.EmptyExceptional
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical NNReal
open SharpLogRamsey.PoissonSchedules SharpLogRamsey.BoundedProbability
noncomputable section
variable {ι H : Type*}

def emptySum (E : Finset H) (D : H → Finset ι) (w : H → ℝ) (ω : ι → ℕ) : ℝ :=
  ∑ h∈E,if ω∈emptyLedger (D h) then w h else 0

end
end SharpLogRamsey.EmptyExceptional
namespace SharpLogRamsey.LearningRow
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A : Type*} [Fintype A]

def test (sample : Finset A) (score : A → ℝ) (z q : ℝ) : Finset A :=
  univ.filter (fun x => x∈sample ∨ score x<z/(2*q))

end
end SharpLogRamsey.LearningRow

namespace SharpLogRamsey.LearningRow
open MeasureTheory Finset
open SharpLogRamsey.BoundedProbability
open scoped Classical BigOperators
noncomputable section
variable {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]

def failures (S : Finset A) (E : A → Set Ω) (ω : Ω) : Finset A := S.filter (fun x => ω∈E x)

end
end SharpLogRamsey.LearningRow

namespace SharpLogRamsey.ExceptionalScore
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A H R : Type*} [Fintype R]

def empty (S : Finset A) (ω : R → A → ℕ) (r : R) : Prop := ∀ x∈S,ω r x=0

def term (O X : Finset A) (b : ℝ) (ω : R → A → ℕ) : ℝ :=
  ∏ r,if empty O ω r then (if empty X ω r then 1-b else -b) else 0

def fullyEmpty (S : Finset A) (ω : R → A → ℕ) : Prop := ∀ r,empty S ω r

end
end SharpLogRamsey.ExceptionalScore

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GreedyPreparation
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*} [Fintype α]

def sized (S : Finset α) (U : β → Finset α) : List β → List (β×ℕ)
  | [] => []
  | b::bs => (b,(S∩U b).card)::sized (S\U b) U bs

def publicSize (U : β → Finset α) : List (β×ℕ) → α → ℕ
  | [],_ => 0
  | (b,m)::bs,x => if x∈U b then m else publicSize U bs x

end
end SharpLogRamsey.GreedyPreparation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_PreparedProposals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.PublicTables

structure Law (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

universe u

def Table (Ω : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => Ω × Table Ω n

instance instFintypeTable (Ω : Type*) [Fintype Ω] (n : ℕ) : Fintype (Table Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (Ω × Table Ω n))

variable {Ω : Type*} [Fintype Ω]

noncomputable def tableWeight (p : Law Ω) : (n : ℕ) → Table Ω n → ℝ
  | 0, _ => 1
  | n+1, z => p.mass z.1 * tableWeight p n z.2

noncomputable def first (A : Ω → Prop) [DecidablePred A] : (n : ℕ) → Table Ω n → Option Ω
  | 0, _ => none
  | n+1, z => if A z.1 then some z.1 else first A n z.2

noncomputable def outcome (A : Ω → Prop) [DecidablePred A] (f : Ω → ℝ)
    (n : ℕ) (z : Table Ω n) : ℝ :=
  (first A n z).elim 0 f

noncomputable def integral (p : Law Ω) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) (n : ℕ) : ℝ := ∑ z, tableWeight p n z * outcome A f n z

noncomputable def accepted (p : Law Ω) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) : ℝ := ∑ x, if A x then p.mass x*f x else 0

noncomputable def acceptProb (p : Law Ω) (A : Ω → Prop) [DecidablePred A] : ℝ :=
  accepted p A (fun _ => 1)

theorem tableWeight_nonneg (p : Law Ω) (n : ℕ) (z : Table Ω n) :
    0 ≤ tableWeight p n z := by
  induction n with
  | zero => simp [tableWeight]
  | succ n ih => exact mul_nonneg (p.nonneg z.1) (ih z.2)

theorem tableWeight_total (p : Law Ω) (n : ℕ) : ∑ z, tableWeight p n z = 1 := by
  induction n with
  | zero =>
    change (∑ z : PUnit, (1 : ℝ)) = 1
    simp
  | succ n ih =>
    change (∑ z : Ω × Table Ω n, p.mass z.1 * tableWeight p n z.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum,ih,mul_one]
    exact p.total

theorem acceptProb_le_one (p : Law Ω) (A : Ω → Prop) [DecidablePred A] :
    acceptProb p A ≤ 1 := by
  rw [← p.total]
  apply sum_le_sum
  intro x hx
  split <;> simp_all [p.nonneg x]

theorem rejectProb (p : Law Ω) (A : Ω → Prop) [DecidablePred A] :
    (∑ x, if A x then 0 else p.mass x) = 1-acceptProb p A := by
  have he (x : Ω) : (if A x then 0 else p.mass x) =
      p.mass x-(if A x then p.mass x*1 else 0) := by split_ifs <;> ring
  simp_rw [he]
  rw [sum_sub_distrib,p.total]
  rfl

theorem integral_succ (p : Law Ω) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) (n : ℕ) :
    integral p A f (n+1) = accepted p A f + (1-acceptProb p A)*integral p A f n := by
  have ho (z : Table Ω (n+1)) : outcome A f (n+1) z =
      if A z.1 then f z.1 else outcome A f n z.2 := by
    change (if A z.1 then some z.1 else first A n z.2).elim 0 f = _
    split_ifs <;> rfl
  simp only [integral, tableWeight, ho]
  change (∑ z : Ω × Table Ω n, p.mass z.1 * tableWeight p n z.2 *
    (if A z.1 then f z.1 else outcome A f n z.2)) = _
  rw [Fintype.sum_prod_type]
  have he (x : Ω) : (∑ z : Table Ω n, p.mass x*tableWeight p n z*
      (if A x then f x else outcome A f n z)) =
      (if A x then p.mass x*f x else 0) +
      (if A x then 0 else p.mass x)*integral p A f n := by
    by_cases hx : A x
    · simp only [hx,ite_true,zero_mul,add_zero]
      calc
        _ = (p.mass x*f x)*∑ z : Table Ω n, tableWeight p n z := by
          rw [mul_sum]; apply sum_congr rfl; intro z hz; ring
        _ = _ := by rw [tableWeight_total,mul_one]
    · simp only [hx,ite_false,zero_add]
      unfold integral
      rw [mul_sum]
      apply sum_congr rfl
      intro z hz
      ring
  simp_rw [he]
  rw [sum_add_distrib,← sum_mul,rejectProb]
  rfl

theorem integral_formula (p : Law Ω) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) (n : ℕ) :
    integral p A f n = (∑ i ∈ range n, (1-acceptProb p A)^i)*accepted p A f := by
  induction n with
  | zero => simp [integral,outcome,first,Table]
  | succ n ih =>
    rw [integral_succ,ih]
    have he : (∑ i ∈ range (n+1), (1-acceptProb p A)^i) =
        1+(1-acceptProb p A)*(∑ i ∈ range n, (1-acceptProb p A)^i) := by
      rw [sum_range_succ']
      simp_rw [pow_succ']
      rw [← mul_sum]
      simp [add_comm]
    rw [he]
    ring

theorem geometric_normalization (a : ℝ) (n : ℕ) :
    a*(∑ i ∈ range n, (1-a)^i) = 1-(1-a)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih,pow_succ]
    ring

theorem first_accepted_law (p : Law Ω) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) (n : ℕ) (ha : 0 < acceptProb p A) :
    integral p A f n = (1-(1-acceptProb p A)^n)*
      (accepted p A f / acceptProb p A) := by
  rw [integral_formula,← geometric_normalization]
  field_simp

theorem produced_domination (p : Law Ω) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) (ha : 0 < acceptProb p A) :
    integral p A f n ≤ accepted p A f / acceptProb p A := by
  rw [first_accepted_law p A f n ha]
  have hn : 0 ≤ accepted p A f := by
    apply sum_nonneg
    intro x hx
    split <;> simp_all [mul_nonneg (p.nonneg x) (hf x)]
  have hc : 1-(1-acceptProb p A)^n ≤ 1 := by
    have h := pow_nonneg (sub_nonneg.mpr (acceptProb_le_one p A)) n
    linarith
  simpa using mul_le_mul_of_nonneg_right hc (div_nonneg hn ha.le)

theorem production_probability (p : Law Ω) (A : Ω → Prop) [DecidablePred A] (n : ℕ) :
    integral p A (fun _ => 1) n = 1-(1-acceptProb p A)^n := by
  rw [integral_formula]
  simpa only [acceptProb,mul_comm] using geometric_normalization (acceptProb p A) n

end SharpLogRamsey.PublicTables

namespace SharpLogRamsey.FiniteSchedules
open Finset MeasureTheory
open scoped Classical BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι]

def clip (M : ℕ) (ω : ι → ℕ) : ι → Fin (M+2) := fun i =>
  ⟨min (ω i) (M+1),by omega⟩

def total (ω : ι → ℕ) : ℕ := ∑ i,ω i

end
end SharpLogRamsey.FiniteSchedules

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FiniteSamplingBounds
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω : Type*} [Fintype Ω]

noncomputable def rowWeight (w : Ω → ℝ) {h : ℕ} (z : Fin h → Ω) : ℝ := ∏ i, w (z i)
noncomputable def hitCount (E : Finset Ω) {h : ℕ} (z : Fin h → Ω) : ℕ :=
  (univ.filter (fun i => z i ∈ E)).card
omit [Fintype Ω] in
lemma rowWeight_nonneg (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) {h : ℕ} (z : Fin h → Ω) :
    0 ≤ rowWeight w z := Finset.prod_nonneg (fun i _ => hw (z i))

lemma rowWeight_total (w : Ω → ℝ) (hw : ∑ x, w x = 1) (h : ℕ) :
    ∑ z : Fin h → Ω, rowWeight w z = 1 := by
  unfold rowWeight
  rw [← Fintype.prod_sum]
  simp [hw]

lemma rowMoment (w : Ω → ℝ) (ht : ∑ x, w x = 1) (E : Finset Ω) (h : ℕ) (b : ℝ) :
    (∑ z : Fin h → Ω, rowWeight w z*b^(hitCount E z)) =
      (1+(b-1)*(∑ x ∈ E, w x))^h := by
  classical
  have hi (z : Fin h → Ω) : b^(hitCount E z) = ∏ i, if z i ∈ E then b else 1 := by
    simp [hitCount, ← Finset.prod_filter]
  simp_rw [hi, rowWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin h) (x : Ω) => w x*(if x ∈ E then b else 1))]
  have he : (∑ x : Ω, w x*(if x ∈ E then b else 1)) = 1+(b-1)*(∑ x ∈ E, w x) := by
    have hi (x : Ω) : w x*(if x ∈ E then b else 1) = w x+(b-1)*(if x ∈ E then w x else 0) := by
      split_ifs <;> ring
    simp_rw [hi]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ht]
    simp
  rw [he]
  simp

noncomputable def rowLower (w : Ω → ℝ) (E : Finset Ω) (h T : ℕ) : ℝ :=
  ∑ z : Fin h → Ω, if hitCount E z < T then rowWeight w z else 0

lemma rowLower_moment (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : ∑ x, w x = 1)
    (E : Finset Ω) (h T : ℕ) :
    (1/2:ℝ)^T*rowLower w E h T ≤ (1-(∑ x ∈ E, w x)/2)^h := by
  have he : 1-(∑ x ∈ E, w x)/2 = 1+((1/2:ℝ)-1)*(∑ x ∈ E, w x) := by ring
  rw [he, ← rowMoment w ht E h (1/2), rowLower, mul_sum]
  apply sum_le_sum
  intro z _
  split_ifs with hz
  · rw [mul_comm ((1/2:ℝ)^T)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) hz.le)
      (rowWeight_nonneg w hw z)
  · simp only [mul_zero]
    exact mul_nonneg (rowWeight_nonneg w hw z) (by positivity)

theorem rowLower_exp (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : ∑ x, w x = 1)
    (E : Finset Ω) (h T : ℕ) :
    rowLower w E h T ≤ Real.exp ((T:ℝ)-(h:ℝ)*(∑ x ∈ E, w x)/2) := by
  have hs : (∑ x ∈ E, w x) ≤ 1 := by
    rw [← ht]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ E) (by intros; exact hw _)
  have hpow : (1-(∑ x ∈ E, w x)/2)^h ≤ Real.exp (-(h:ℝ)*(∑ x ∈ E, w x)/2) := by
    rw [show -(h:ℝ)*(∑ x ∈ E, w x)/2 = (h:ℝ)*(-(∑ x ∈ E, w x)/2) by ring,
      Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by linarith)
    simpa only [neg_div] using Real.one_sub_le_exp_neg ((∑ x ∈ E, w x)/2)
  have hmult := mul_le_mul_of_nonneg_left ((rowLower_moment w hw ht E h T).trans hpow)
    (show (0:ℝ) ≤ 2^T by positivity)
  have hcancel : (2:ℝ)^T*((1/2:ℝ)^T*rowLower w E h T) = rowLower w E h T := by
    rw [← mul_assoc, ← mul_pow]
    norm_num
  rw [hcancel] at hmult
  have htwo : (2:ℝ)^T ≤ Real.exp (T:ℝ) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
      (show (2:ℝ) ≤ Real.exp 1 by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1) T
    simpa [← Real.exp_nat_mul] using hh
  calc
    _ ≤ (2:ℝ)^T*Real.exp (-(h:ℝ)*(∑ x ∈ E, w x)/2) := hmult
    _ ≤ Real.exp (T:ℝ)*Real.exp (-(h:ℝ)*(∑ x ∈ E, w x)/2) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end
end SharpLogRamsey.FiniteSamplingBounds

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

def uniformMass (X : Finset Ω) (x : Ω) : ℝ := if x ∈ X then (X.card : ℝ)⁻¹ else 0

omit [Fintype Ω] in
lemma uniform_nonneg (X : Finset Ω) (x : Ω) : 0 ≤ uniformMass X x := by
  unfold uniformMass
  split_ifs <;> positivity

lemma uniform_total {X : Finset Ω} (hX : X.Nonempty) : ∑ x, uniformMass X x = 1 := by
  have hx : (X.card:ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hX).ne'
  simp [uniformMass,hx]

omit [Fintype Ω] in
lemma uniform_sum (X E : Finset Ω) :
    (∑ x ∈ E, uniformMass X x) = ((E ∩ X).card : ℝ)/(X.card:ℝ) := by
  simp [uniformMass, div_eq_mul_inv, ← filter_mem_eq_inter]

lemma coordinate_mean (w : Ω → ℝ) (ht : ∑ x, w x=1)
    {h : ℕ} (i : Fin h) (f : Ω → ℝ) :
    (∑ z : Fin h → Ω, rowWeight w z*f (z i)) = ∑ x, w x*f x := by
  have hi (z : Fin h → Ω) : rowWeight w z*f (z i) =
      ∏ j, w (z j)*(if j=i then f (z j) else 1) := by
    rw [prod_mul_distrib]
    simp [rowWeight]
  simp_rw [hi]
  rw [← Fintype.prod_sum (fun j x => w x*(if j=i then f x else 1))]
  have he (j : Fin h) : (∑ x, w x*(if j=i then f x else 1)) =
      if j=i then ∑ x, w x*f x else 1 := by
    split_ifs <;> simp_all
  simp_rw [he]
  simp

omit [Fintype Ω] in
lemma hitCount_real {h : ℕ} (E : Finset Ω) (z : Fin h → Ω) :
    (hitCount E z:ℝ) = ∑ i, if z i ∈ E then (1:ℝ) else 0 := by
  simp [hitCount, ← sum_boole]

lemma hitCount_mean (w : Ω → ℝ) (ht : ∑ x, w x=1) (E : Finset Ω) (h : ℕ) :
    (∑ z : Fin h → Ω, rowWeight w z*(hitCount E z:ℝ)) = (h:ℝ)*(∑ x ∈ E, w x) := by
  simp_rw [hitCount_real, mul_sum]
  rw [sum_comm]
  have hi (i : Fin h) : (∑ z : Fin h → Ω,
      if z i∈E then rowWeight w z else 0) = ∑ x∈E,w x := by
    simpa only [mul_ite, mul_one, mul_zero, ← sum_filter, filter_mem_eq_inter,
      univ_inter] using coordinate_mean w ht i (fun x => if x∈E then (1:ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero]
  simp_rw [hi]
  simp [mul_sum]

def pass (R : Ω → Y → Prop) (q : ℝ) {h : ℕ} (z : Fin h → Ω) (y : Y) : Prop :=
  (hitCount (univ.filter (fun x => R x y)) z:ℝ) < (h:ℝ)/(5*q)

def cap (R : Ω → Y → Prop) (q : ℝ) (U : Finset Y) {h : ℕ} (z : Fin h → Ω) : Finset Y :=
  U.filter (pass R q z)

omit [Fintype Y] in

theorem pointwise_exclusion (w : Ω → ℝ) (hw : ∀ x, 0≤w x) (ht : ∑ x, w x=1)
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (h : ℕ) (hh : 0<h) (y : Y) :
    (∑ z : Fin h → Ω, if ¬pass R q z y then rowWeight w z else 0) ≤
      5*q*(∑ x ∈ univ.filter (fun x => R x y), w x) := by
  let E := univ.filter (fun x => R x y)
  have hm : (h:ℝ)/(5*q)*(∑ z : Fin h → Ω,
      if ¬pass R q z y then rowWeight w z else 0) ≤ (h:ℝ)*(∑ x ∈ E, w x) := by
    rw [←hitCount_mean w ht E h, mul_sum]
    apply sum_le_sum
    intro z _
    by_cases hz : pass R q z y
    · simp only [hz, not_true_eq_false, ite_false, mul_zero]
      exact mul_nonneg (rowWeight_nonneg w hw z) (Nat.cast_nonneg _)
    · simp only [hz, not_false_eq_true, ite_true]
      have hz' : (h:ℝ)/(5*q) ≤ (hitCount E z:ℝ) := le_of_not_gt hz
      nlinarith [mul_le_mul_of_nonneg_right hz' (rowWeight_nonneg w hw z)]
  have hc : 0<(h:ℝ) := by exact_mod_cast hh
  apply (mul_le_mul_iff_right₀ hc).mp
  have hm' := mul_le_mul_of_nonneg_right hm (show 0≤5*q by positivity)
  dsimp [E] at hm'
  convert hm' using 1 <;> field_simp

omit [Fintype Y] in

theorem pointwise_pass (w : Ω → ℝ) (hw : ∀ x, 0≤w x) (ht : ∑ x, w x=1)
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (h : ℕ) (y : Y)
    (hy : 1/(2*q) ≤ ∑ x ∈ univ.filter (fun x => R x y), w x) :
    (∑ z : Fin h → Ω, if pass R q z y then rowWeight w z else 0) ≤
      Real.exp (1-(h:ℝ)/(20*q)) := by
  let E := univ.filter (fun x => R x y)
  let T := ⌈(h:ℝ)/(5*q)⌉₊
  have ht' : (T:ℝ) ≤ (h:ℝ)/(5*q)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hpt : (∑ z : Fin h → Ω, if pass R q z y then rowWeight w z else 0) ≤
      rowLower w E h T := by
    apply sum_le_sum
    intro z _
    by_cases hz : pass R q z y
    · have hc : hitCount E z < T := by
        apply Nat.lt_ceil.mpr
        exact hz
      simp only [hz, ite_true, hc, le_refl]
    · simp only [hz, ite_false]
      split_ifs <;> simp [rowWeight_nonneg w hw z]
  apply hpt.trans ((rowLower_exp w hw ht E h T).trans ?_)
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hy (show 0≤(h:ℝ)/2 by positivity)
  have he : (h:ℝ)/2*(1/(2*q)) = (h:ℝ)/(4*q) := by ring
  rw [he] at hm
  have hm' : (h:ℝ)/(4*q) ≤ ((h:ℝ)*(∑ x∈E,w x))/2 := by
    exact hm.trans_eq (by dsimp [E]; ring)
  calc
    _ ≤ (h:ℝ)/(5*q)+1-(h:ℝ)/(4*q) := sub_le_sub ht' hm'
    _ = _ := by ring

end
end SharpLogRamsey.Validation

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

def prob (w : Ω → ℝ) (h : ℕ) (P : (Fin h → Ω) → Prop) : ℝ :=
  ∑ z : Fin h → Ω, if P z then rowWeight w z else 0

lemma prob_le_one (w : Ω → ℝ) (hw : ∀ x, 0≤w x) (ht : ∑ x,w x=1) {h : ℕ}
    (P : (Fin h → Ω) → Prop) : prob w h P ≤ 1 := by
  rw [←rowWeight_total w ht h]
  apply sum_le_sum
  intro z _
  split_ifs <;> simp [rowWeight_nonneg w hw z]

omit [Fintype Y] in
lemma cardinal_mean (w : Ω → ℝ) {h : ℕ} (U : Finset Y)
    (P : (Fin h → Ω) → Y → Prop) :
    (∑ z : Fin h → Ω, rowWeight w z*((U.filter (P z)).card:ℝ)) =
      ∑ y∈U, prob w h (fun z => P z y) := by
  have he (z : Fin h → Ω) : ((U.filter (P z)).card:ℝ) =
      ∑ y∈U, if P z y then (1:ℝ) else 0 := by simp
  simp_rw [he,mul_sum,mul_ite,mul_one,mul_zero]
  rw [sum_comm]
  rfl

lemma markov (w : Ω → ℝ) (hw : ∀ x,0≤w x) {h : ℕ}
    (f : (Fin h → Ω) → ℝ) (hf : ∀ z,0≤f z) (M : ℝ) (hM : 0<M) :
    prob w h (fun z => M<f z) ≤ (∑ z, rowWeight w z*f z)/M := by
  apply (le_div_iff₀ hM).mpr
  rw [prob,sum_mul]
  apply sum_le_sum
  intro z _
  split_ifs with hz
  · exact mul_le_mul_of_nonneg_left hz.le (rowWeight_nonneg w hw z)
  · simpa using mul_nonneg (rowWeight_nonneg w hw z) (hf z)

omit [Fintype Y] in

theorem cap_mean_le (w : Ω → ℝ) (hw : ∀ x,0≤w x) (ht : ∑ x,w x=1)
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (h : ℕ) (U : Finset Y) :
    (∑ z : Fin h → Ω, rowWeight w z*((cap R q U z).card:ℝ)) ≤
      ((U.filter (fun y => (∑ x∈univ.filter (fun x => R x y),w x)<1/(2*q))).card:ℝ)
        +(U.card:ℝ)*Real.exp (1-(h:ℝ)/(20*q)) := by
  simp only [cap]
  rw [cardinal_mean w U (fun z y => pass R q z y)]
  let B := U.filter (fun y => (∑ x∈univ.filter (fun x => R x y),w x)<1/(2*q))
  calc
    _ ≤ ∑ y∈U, ((if y∈B then (1:ℝ) else 0)+Real.exp (1-(h:ℝ)/(20*q))) := by
      apply sum_le_sum
      intro y hy
      by_cases hb : y∈B
      · simp only [hb,ite_true]
        exact (prob_le_one w hw ht _).trans (by linarith [Real.exp_pos (1-(h:ℝ)/(20*q))])
      · simp only [hb,ite_false,zero_add]
        apply pointwise_pass w hw ht R q hq h y
        exact le_of_not_gt (fun hh => hb (mem_filter.mpr ⟨hy,hh⟩))
    _ = _ := by
      rw [sum_add_distrib]
      simp only [sum_boole, sum_const, nsmul_eq_mul]
      congr 2
      have he : U.filter (fun y => y∈B) = B := filter_mem_eq_inter.trans (inter_eq_right.mpr (filter_subset _ _))
      rw [he]

omit [Fintype Y] in

theorem loss_mean_le (w : Ω → ℝ) (hw : ∀ x,0≤w x) (ht : ∑ x,w x=1)
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (h : ℕ) (hh : 0<h) (T : Finset Y) :
    (∑ z : Fin h → Ω, rowWeight w z*((T.filter (fun y => ¬pass R q z y)).card:ℝ)) ≤
      5*q*(∑ y∈T,∑ x∈univ.filter (fun x => R x y),w x) := by
  calc
    _ = ∑ y∈T,prob w h (fun z => ¬pass R q z y) := by
      have he (z : Fin h → Ω) : ((T.filter (fun y => ¬pass R q z y)).card:ℝ) =
          ∑ y∈T, if ¬pass R q z y then (1:ℝ) else 0 := by simp only [sum_boole]
      simp_rw [he,mul_sum,mul_ite,mul_one,mul_zero]
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      unfold prob
      apply sum_congr rfl
      intro z _
      split_ifs <;> simp_all
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro y _
      have he := pointwise_exclusion w hw ht R q hq h hh y
      apply le_trans (le_of_eq ?_) he
      unfold prob
      apply sum_congr rfl
      intro z _
      split_ifs <;> simp_all

omit [Fintype Y] in

theorem acceptance_mass (w : Ω → ℝ) (hw : ∀ x,0≤w x) (ht : ∑ x,w x=1)
    (R : Ω → Y → Prop) (q : ℝ) (h : ℕ) (U T : Finset Y)
    (M : ℝ) (hM : 0<M) (hT : T.Nonempty)
    (hs : (∑ z : Fin h → Ω,rowWeight w z*((cap R q U z).card:ℝ)) ≤ M/20)
    (hl : (∑ z : Fin h → Ω,rowWeight w z*
      ((T.filter (fun y => ¬pass R q z y)).card:ℝ)) ≤ (T.card:ℝ)/2000) :
    (9/10:ℝ) ≤ prob w h (fun z => ((cap R q U z).card:ℝ)≤M ∧
      ((T.filter (fun y => ¬pass R q z y)).card:ℝ)≤(T.card:ℝ)/100) := by
  let sz (z : Fin h → Ω) : ℝ := (cap R q U z).card
  let ls (z : Fin h → Ω) : ℝ := (T.filter (fun y => ¬pass R q z y)).card
  let A (z : Fin h → Ω) : Prop := sz z≤M ∧ ls z≤(T.card:ℝ)/100
  have htpos : 0<(T.card:ℝ) := by exact_mod_cast card_pos.mpr hT
  have hbS : prob w h (fun z => M < sz z) ≤ (1/20:ℝ) := by
    apply (markov w hw sz (fun z => Nat.cast_nonneg _) M hM).trans
    exact (div_le_iff₀ hM).mpr (by simpa [sz,div_eq_mul_inv,mul_comm] using hs)
  have hbL : prob w h (fun z => (T.card:ℝ)/100<ls z) ≤ (1/20:ℝ) := by
    apply (markov w hw ls (fun z => Nat.cast_nonneg _) _ (by positivity)).trans
    apply (div_le_iff₀ (show 0<(T.card:ℝ)/100 by positivity)).mpr
    exact hl.trans_eq (by ring)
  have hc : 1≤prob w h A+prob w h (fun z => M < sz z)+
      prob w h (fun z => (T.card:ℝ)/100<ls z) := by
    rw [←rowWeight_total w ht h,prob,prob,prob,←sum_add_distrib,←sum_add_distrib]
    apply sum_le_sum
    intro z _
    have hz := rowWeight_nonneg w hw z
    simp only [←not_le]
    by_cases hs' : sz z≤M <;> by_cases hl' : ls z≤(T.card:ℝ)/100 <;>
      simp_all [A]
    all_goals positivity
  change (9/10:ℝ) ≤ prob w h A
  linarith

end
end SharpLogRamsey.Validation

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {Ω Y : Type*} [Fintype Ω]

def rowLaw (X : Finset Ω) (hX : X.Nonempty) (h : ℕ) : PublicTables.Law (Fin h → Ω) where
  mass := rowWeight (uniformMass X)
  nonneg := rowWeight_nonneg (uniformMass X) (uniform_nonneg X)
  total := rowWeight_total (uniformMass X) (uniform_total hX) h

def allIn (X : Finset Ω) {h : ℕ} (z : Fin h → Ω) : Prop := ∀ i,z i∈X

omit [Fintype Ω] in

theorem contained_row_scaling (X W : Finset Ω) (hX : X.Nonempty) (hsub : X⊆W)
    {h : ℕ} (z : Fin h → Ω) :
    (if allIn X z then rowWeight (uniformMass W) z else 0) =
      ((X.card:ℝ)/(W.card:ℝ))^h * rowWeight (uniformMass X) z := by
  have hx : (X.card:ℝ)≠0 := by exact_mod_cast (card_pos.mpr hX).ne'
  by_cases hz : allIn X z
  · simp only [hz,ite_true]
    have hi (i : Fin h) : uniformMass W (z i)=(W.card:ℝ)⁻¹ := by
      simp [uniformMass,hsub (hz i)]
    have hj (i : Fin h) : uniformMass X (z i)=(X.card:ℝ)⁻¹ := by
      simp [uniformMass,hz i]
    simp only [rowWeight,hi,hj,prod_const,card_univ,Fintype.card_fin]
    rw [←mul_pow]
    congr 1
    field_simp
  · simp only [hz,ite_false]
    have hn : ∃ i,z i∉X := by simpa only [allIn,not_forall] using hz
    obtain ⟨i,hi⟩ := hn
    have he : rowWeight (uniformMass X) z=0 := by
      apply prod_eq_zero (mem_univ i)
      simp [uniformMass,hi]
    rw [he,mul_zero]

def implementAccept (X : Finset Ω) {h : ℕ}
    (Good : (Fin h → Ω) → Prop) (z : Fin h → Ω) : Prop := allIn X z ∧ Good z

theorem accepted_scaling (X W : Finset Ω) (hX : X.Nonempty) (hW : W.Nonempty)
    (hsub : X⊆W) (h : ℕ) (Good : (Fin h → Ω) → Prop) (f : (Fin h → Ω) → ℝ) :
    PublicTables.accepted (rowLaw W hW h) (implementAccept X Good) f =
      ((X.card:ℝ)/(W.card:ℝ))^h *
        (∑ z : Fin h → Ω, if Good z then rowWeight (uniformMass X) z*f z else 0) := by
  rw [PublicTables.accepted,mul_sum]
  apply sum_congr rfl
  intro z _
  simp only [implementAccept,rowLaw]
  by_cases hg : Good z
  · simp only [hg,and_true,ite_true]
    rw [show (if allIn X z then rowWeight (uniformMass W) z*f z else 0) =
      (if allIn X z then rowWeight (uniformMass W) z else 0)*f z by
        split_ifs <;> ring,contained_row_scaling X W hX hsub]
    ring
  · simp [hg]

theorem proposal_acceptance (X W : Finset Ω) (hX : X.Nonempty) (hW : W.Nonempty)
    (hsub : X⊆W) (h : ℕ) (Good : (Fin h → Ω) → Prop) :
    PublicTables.acceptProb (rowLaw W hW h) (implementAccept X Good) =
      ((X.card:ℝ)/(W.card:ℝ))^h * prob (uniformMass X) h Good := by
  simpa only [PublicTables.acceptProb,mul_one,prob] using
    accepted_scaling X W hX hW hsub h Good (fun _ => 1)

theorem public_iid_domination (X W : Finset Ω) (hX : X.Nonempty) (hW : W.Nonempty)
    (hsub : X⊆W) (h : ℕ) (Good : (Fin h → Ω) → Prop)
    (hGood : (9/10:ℝ) ≤ prob (uniformMass X) h Good)
    (f : (Fin h → Ω) → ℝ) (hf : ∀ z,0≤f z) (m : ℕ) :
    PublicTables.integral (rowLaw W hW h) (implementAccept X Good) f m ≤
      (10/9:ℝ) * (∑ z : Fin h → Ω,rowWeight (uniformMass X) z*f z) := by
  let r : ℝ := ((X.card:ℝ)/(W.card:ℝ))^h
  let I : ℝ := ∑ z : Fin h → Ω,rowWeight (uniformMass X) z*f z
  have hr : 0 < r := by
    have hx : 0<(X.card:ℝ) := by exact_mod_cast card_pos.mpr hX
    have hw : 0<(W.card:ℝ) := by exact_mod_cast card_pos.mpr hW
    exact pow_pos (div_pos hx hw) h
  have hI : 0≤I := sum_nonneg (fun z _ => mul_nonneg (rowWeight_nonneg _ (uniform_nonneg X) z) (hf z))
  have ha : r*(9/10) ≤ PublicTables.acceptProb (rowLaw W hW h) (implementAccept X Good) := by
    rw [proposal_acceptance X W hX hW hsub h Good]
    exact mul_le_mul_of_nonneg_left hGood hr.le
  have ha0 : 0<PublicTables.acceptProb (rowLaw W hW h) (implementAccept X Good) :=
    lt_of_lt_of_le (mul_pos hr (by norm_num)) ha
  apply (PublicTables.produced_domination (rowLaw W hW h) (implementAccept X Good) f hf m ha0).trans
  have hn : PublicTables.accepted (rowLaw W hW h) (implementAccept X Good) f ≤ r*I := by
    rw [accepted_scaling X W hX hW hsub h Good f]
    apply mul_le_mul_of_nonneg_left _ hr.le
    apply sum_le_sum
    intro z _
    split_ifs <;> simp [mul_nonneg (rowWeight_nonneg _ (uniform_nonneg X) z) (hf z)]
  calc
    _ ≤ (r*I)/PublicTables.acceptProb (rowLaw W hW h) (implementAccept X Good) :=
      div_le_div_of_nonneg_right hn ha0.le
    _ ≤ (r*I)/(r*(9/10)) :=
      div_le_div_of_nonneg_left (mul_nonneg hr.le hI) (by positivity) ha
    _ = _ := by field_simp; ring

end
end SharpLogRamsey.Validation
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ProducedExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {Ω Y : Type*} [Fintype Ω]
theorem produced_exclusion (X W : Finset Ω) (hX : X.Nonempty) (hW : W.Nonempty)
    (hsub : X⊆W) (h : ℕ) (hh : 0<h) (Good : (Fin h → Ω) → Prop)
    (hGood : (9/10:ℝ) ≤ prob (uniformMass X) h Good)
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (y : Y) (m : ℕ) :
    PublicTables.integral (rowLaw W hW h) (implementAccept X Good)
      (fun z => if ¬pass R q z y then 1 else 0) m ≤
        6*q*(∑ x∈univ.filter (fun x => R x y),uniformMass X x) := by
  have hd := public_iid_domination X W hX hW hsub h Good hGood
    (fun z => if ¬pass R q z y then 1 else 0) (by intro z; split_ifs <;> norm_num) m
  simp only [mul_ite,mul_one,mul_zero] at hd
  apply hd.trans
  have he := mul_le_mul_of_nonneg_left
    (pointwise_exclusion (uniformMass X) (uniform_nonneg X) (uniform_total hX) R q hq h hh y)
    (show (0:ℝ)≤10/9 by norm_num)
  apply he.trans
  have hp : 0≤∑ x∈univ.filter (fun x => R x y),uniformMass X x :=
    sum_nonneg (fun x _ => uniform_nonneg X x)
  nlinarith [mul_nonneg hq.le hp]

end
end SharpLogRamsey.Validation

namespace SharpLogRamsey.PublicTables
open Finset
open scoped BigOperators Classical
variable {Ω : Type*} [Fintype Ω]

theorem failure_exp (p : Law Ω) (A : Ω → Prop) [DecidablePred A] (m : ℕ) :
    1-integral p A (fun _ => 1) m ≤ Real.exp (-(m:ℝ)*acceptProb p A) := by
  rw [production_probability]
  have hp : 0≤1-acceptProb p A := sub_nonneg.mpr (acceptProb_le_one p A)
  have he := pow_le_pow_left₀ hp (Real.one_sub_le_exp_neg (acceptProb p A)) m
  calc
    _ = (1-acceptProb p A)^m := by ring
    _ ≤ Real.exp (-acceptProb p A)^m := he
    _ = _ := by
      rw [←Real.exp_nat_mul]
      congr 1
      ring

end SharpLogRamsey.PublicTables

namespace SharpLogRamsey.Incidence
open Finset
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem low_incidence_half_target_mass {n : ℕ} (hdim : Module.finrank K V = n+3)
    (w : Projectivization K V → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : ∑ x, w x = 1)
    (M : ℝ) (hM : ∀ x, w x ≤ M)
    (v : Projectivization K (Module.Dual K V) → ℝ) (N : ℝ)
    (hN0 : 0 ≤ N) (hN : ∀ y, v y ≤ N) :
    (∑ y ∈ univ.filter (fun y => weightedIncidences SharpLogRamsey.Incidence.Incident w y <
      1/(2*(Nat.card K:ℝ))), v y) ≤ 36*(Nat.card K:ℝ)^(n+3)*M*N := by
  let q : ℝ := Nat.card K
  let u : ℝ := ∑ i ∈ range (n+2), q^i
  let p : ℝ := u/(∑ i ∈ range (n+3), q^i)
  let B := univ.filter (fun y => weightedIncidences SharpLogRamsey.Incidence.Incident w y < 1/(2*q))
  have hq : 2 ≤ q := by
    change (2:ℝ) ≤ Nat.card K
    exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)
  have hq0 : 0 < q := by linarith
  have hu : 1 ≤ u := by
    have hs := single_le_sum (f := fun i => q^i)
      (fun i _ => pow_nonneg hq0.le i) (show 0 ∈ range (n+2) by simp)
    simpa [u] using hs
  have hvpos : 0 < ∑ i ∈ range (n+3), q^i := by
    rw [geom_sum_succ]
    change 0 < q*u+1
    positivity
  have hp : 2/(3*q) ≤ p := by
    change 2/(3*q) ≤ u/(∑ i ∈ range (n+3), q^i)
    apply (div_le_div_iff₀ (by positivity) hvpos).mpr
    rw [geom_sum_succ]
    change 2*(q*u+1) ≤ u*(3*q)
    nlinarith
  have hnorm : (∑ x, w x^2) ≤ M := by
    calc
      _ ≤ ∑ x, M*w x := by
        apply sum_le_sum
        intro x _
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (hM x) (hw x)
      _ = M := by rw [← mul_sum, ht, mul_one]
  have hvar := (projective_variance_le hdim w).trans
    (mul_le_mul_of_nonneg_left hnorm (show 0 ≤ q^(n+1) by positivity))
  change (∑ y, (weightedIncidences SharpLogRamsey.Incidence.Incident w y-p*(∑ x, w x))^2) ≤ q^(n+1)*M at hvar
  rw [ht, mul_one] at hvar
  have hc : (B.card:ℝ)*(1/(6*q))^2 ≤ q^(n+1)*M := by
    calc
      _ = ∑ _y ∈ B, (1/(6*q))^2 := by simp
      _ ≤ ∑ y ∈ B, (weightedIncidences SharpLogRamsey.Incidence.Incident w y-p)^2 := by
        apply sum_le_sum
        intro y hy
        have hb : weightedIncidences SharpLogRamsey.Incidence.Incident w y < 1/(2*q) := (mem_filter.mp hy).2
        have hg : 1/(6*q) ≤ p-weightedIncidences SharpLogRamsey.Incidence.Incident w y := by
          have he : 2/(3*q)-1/(2*q) = 1/(6*q) := by field_simp; ring
          linarith
        have hi : 0 ≤ 1/(6*q) := by positivity
        nlinarith
      _ ≤ ∑ y, (weightedIncidences SharpLogRamsey.Incidence.Incident w y-p)^2 := by
        apply sum_le_sum_of_subset_of_nonneg (subset_univ B)
        intro y _ _
        positivity
      _ ≤ _ := hvar
  have hmult := mul_le_mul_of_nonneg_right hc (show 0 ≤ 36*q^2 by positivity)
  have hcancel : (B.card:ℝ)*(1/(6*q))^2*(36*q^2) = B.card := by
    field_simp
    ring
  rw [hcancel] at hmult
  have he : q^(n+1)*M*(36*q^2) = 36*q^(n+3)*M := by
    rw [show n+3 = (n+1)+2 by omega, pow_add]
    ring
  rw [he] at hmult
  change (∑ y ∈ B, v y) ≤ _
  calc
    _ ≤ ∑ _y ∈ B, N := by apply sum_le_sum; intro y _; exact hN y
    _ = (B.card:ℝ)*N := by simp
    _ ≤ (36*q^(n+3)*M)*N := mul_le_mul_of_nonneg_right hmult hN0

end SharpLogRamsey.Incidence

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds SharpLogRamsey.Incidence
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem projective_low_card {n : ℕ} (hdim : Module.finrank K V=n+3)
    (X : Finset (Projectivization K V)) (hX : X.Nonempty)
    (U : Finset (Projectivization K (Module.Dual K V))) :
    ((U.filter (fun y => (∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass X x)
      <1/(2*(Nat.card K:ℝ)))).card:ℝ) ≤ 36*(Nat.card K:ℝ)^(n+3)/(X.card:ℝ) := by
  have hu (x : Projectivization K V) : uniformMass X x ≤ (X.card:ℝ)⁻¹ := by
    unfold uniformMass
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.mpr (Nat.cast_nonneg X.card)
  have hb := low_incidence_half_target_mass hdim (uniformMass X) (uniform_nonneg X)
    (uniform_total hX) (X.card:ℝ)⁻¹ hu (fun _ => (1:ℝ)) 1 (by norm_num) (by simp)
  simp only [sum_const, nsmul_eq_mul, mul_one,div_eq_mul_inv] at hb ⊢
  apply le_trans _ hb
  apply Nat.cast_le.mpr
  apply card_le_card
  intro y hy
  simp only [mem_filter,mem_univ,true_and] at hy ⊢
  simpa only [weightedIncidences,←sum_filter] using hy.2

theorem projective_cap_mean {n : ℕ} (hdim : Module.finrank K V=n+3)
    (X : Finset (Projectivization K V)) (hX : X.Nonempty)
    (U : Finset (Projectivization K (Module.Dual K V))) (h : ℕ) :
    (∑ z : Fin h → Projectivization K V, rowWeight (uniformMass X) z*
      ((cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) U z).card:ℝ)) ≤
        36*(Nat.card K:ℝ)^(n+3)/(X.card:ℝ)+
          (U.card:ℝ)*Real.exp (1-(h:ℝ)/(20*(Nat.card K:ℝ))) := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast (Nat.card_pos (α:=K))
  exact (cap_mean_le (uniformMass X) (uniform_nonneg X) (uniform_total hX)
    SharpLogRamsey.Incidence.Incident _ hq h U).trans (add_le_add (projective_low_card hdim X hX U) le_rfl)

theorem projective_ideal_acceptance {n : ℕ} (hdim : Module.finrank K V=n+3)
    (X : Finset (Projectivization K V)) (hX : X.Nonempty)
    (U T : Finset (Projectivization K (Module.Dual K V))) (hT : T.Nonempty)
    (h : ℕ) (hh : 0<h) (M : ℝ) (hM : 0<M)
    (hsize : 36*(Nat.card K:ℝ)^(n+3)/(X.card:ℝ)+
      (U.card:ℝ)*Real.exp (1-(h:ℝ)/(20*(Nat.card K:ℝ))) ≤ M/20)
    (hsparse : (∑ y∈T,∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass X x)
      ≤ (T.card:ℝ)/(10000*(Nat.card K:ℝ))) :
    (9/10:ℝ) ≤ prob (uniformMass X) h (fun z =>
      ((cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) U z).card:ℝ)≤M ∧
      ((T.filter (fun y => ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) z y)).card:ℝ)≤(T.card:ℝ)/100) := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast (Nat.card_pos (α:=K))
  apply acceptance_mass (uniformMass X) (uniform_nonneg X) (uniform_total hX)
    SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) h U T M hM hT
  · exact (projective_cap_mean hdim X hX U h).trans hsize
  · apply (loss_mean_le (uniformMass X) (uniform_nonneg X) (uniform_total hX)
      SharpLogRamsey.Incidence.Incident _ hq h hh T).trans
    have hs := mul_le_mul_of_nonneg_left hsparse (show 0≤5*(Nat.card K:ℝ) by positivity)
    apply hs.trans_eq
    field_simp
    ring

end
end SharpLogRamsey.Validation

namespace SharpLogRamsey.PublicTables
open Finset
open scoped BigOperators Classical
universe u
variable {Ω : Type u}

def rowAt : (n : ℕ) → Table Ω n → Fin n → Ω
  | 0, _, i => Fin.elim0 i
  | n+1, z, i => Fin.cases z.1 (rowAt n z.2) i

noncomputable def firstIndex (A : Ω → Prop) [DecidablePred A] :
    (n : ℕ) → Table Ω n → Option (Fin n)
  | 0, _ => none
  | n+1, z => if A z.1 then some 0 else (firstIndex A n z.2).map Fin.succ

theorem reconstruct_first (A : Ω → Prop) [DecidablePred A] (n : ℕ) (z : Table Ω n) :
    (firstIndex A n z).map (rowAt n z) = first A n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (if A z.1 then some 0 else (firstIndex A n z.2).map Fin.succ).map
      (rowAt (n+1) z) = if A z.1 then some z.1 else first A n z.2
    by_cases ha : A z.1
    · simp only [ha,ite_true,Option.map_some,rowAt,Fin.cases_zero]
    · simp only [ha,ite_false,Option.map_map]
      have hf : rowAt (n+1) z ∘ Fin.succ = rowAt n z.2 := by
        funext i
        simp only [Function.comp_apply,rowAt,Fin.cases_succ]
      rw [hf,ih]

theorem first_valid (A : Ω → Prop) [DecidablePred A] (n : ℕ) (z : Table Ω n)
    (x : Ω) (hx : first A n z=some x) : A x := by
  induction n with
  | zero => cases hx
  | succ n ih =>
    change (if A z.1 then some z.1 else first A n z.2)=some x at hx
    split_ifs at hx with ha
    · have : z.1=x := Option.some.inj hx
      simpa only [this] using ha
    · exact ih z.2 hx

theorem index_valid (A : Ω → Prop) [DecidablePred A] (n : ℕ) (z : Table Ω n)
    (i : Fin n) (hi : firstIndex A n z=some i) : A (rowAt n z i) := by
  have he := reconstruct_first A n z
  rw [hi,Option.map_some] at he
  exact first_valid A n z _ he.symm

end SharpLogRamsey.PublicTables

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {Ω Y : Type*} [Fintype Ω]

def GoodCap (R : Ω → Y → Prop) (q : ℝ) (U T : Finset Y) (M : ℝ)
    {h : ℕ} (z : Fin h → Ω) : Prop :=
  ((cap R q U z).card:ℝ)≤M ∧
    ((T.filter (fun y => ¬pass R q z y)).card:ℝ)≤(T.card:ℝ)/100

omit [Fintype Ω] in
lemma cap_capture {R : Ω → Y → Prop} [Fintype Ω] {q : ℝ} {U T : Finset Y}
    {M : ℝ} {h : ℕ} {z : Fin h → Ω} (hT : T⊆U) (hg : GoodCap R q U T M z) :
    (99:ℝ)*(T.card:ℝ) ≤ 100*((T∩cap R q U z).card:ℝ) := by
  have he : T∩cap R q U z = T.filter (pass R q z) := by
    ext y
    simp only [mem_inter,cap,mem_filter]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hT h.1,h.2⟩⟩
  rw [he]
  have ht := card_filter_add_card_filter_not (s:=T) (pass R q z)
  have ht' : ((T.filter (pass R q z)).card:ℝ)+
      ((T.filter (fun y => ¬pass R q z y)).card:ℝ) = T.card := by exact_mod_cast ht
  have hl := hg.2
  linarith

theorem decoded_cap (X : Finset Ω) (R : Ω → Y → Prop)
    (q : ℝ) (U T : Finset Y) (hT : T⊆U) (M : ℝ) (h m : ℕ)
    (table : PublicTables.Table (Fin h → Ω) m) (i : Fin m)
    (hi : PublicTables.firstIndex (implementAccept X (GoodCap R q U T M)) m table=some i) :
    let C := cap R q U (PublicTables.rowAt m table i)
    C⊆U ∧ (C.card:ℝ)≤M ∧ (99:ℝ)*(T.card:ℝ)≤100*((T∩C).card:ℝ) := by
  have hg := (PublicTables.index_valid (implementAccept X (GoodCap R q U T M)) m table i hi).2
  exact ⟨filter_subset _ _,hg.1,cap_capture hT hg⟩

omit [Fintype Ω] in
lemma uniform_sum_mono {X₀ X E : Finset Ω} (hX : X.Nonempty) (h₀ : X₀.Nonempty)
    (hsub : X₀⊆X) (c : ℝ) (hc : 0 < c) (hcap : c*(X.card:ℝ)≤(X₀.card:ℝ)) :
    (∑ x∈E,uniformMass X₀ x) ≤ c⁻¹*(∑ x∈E,uniformMass X x) := by
  rw [uniform_sum,uniform_sum]
  have hx : 0<(X.card:ℝ) := by exact_mod_cast card_pos.mpr hX
  have hx₀ : 0<(X₀.card:ℝ) := by exact_mod_cast card_pos.mpr h₀
  have he : ((E∩X₀).card:ℝ)≤((E∩X).card:ℝ) := by
    exact_mod_cast card_le_card (show E∩X₀ ⊆ E∩X from
      fun _ hx => mem_inter.mpr ⟨(mem_inter.mp hx).1,hsub (mem_inter.mp hx).2⟩)
  apply (le_inv_mul_iff₀ hc).mpr
  apply (le_div_iff₀ hx).mpr
  rw [show c*(((E∩X₀).card:ℝ)/(X₀.card:ℝ))*(X.card:ℝ) =
    (c*(X.card:ℝ)*((E∩X₀).card:ℝ))/(X₀.card:ℝ) by ring]
  apply (div_le_iff₀ hx₀).mpr
  have h1 := mul_le_mul_of_nonneg_left hcap (show 0≤((E∩X).card:ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left he (show 0 ≤ c*(X.card:ℝ) by positivity)
  nlinarith

theorem original_exclusion (X₀ X W : Finset Ω) (hX₀ : X₀.Nonempty)
    (hX : X.Nonempty) (hW : W.Nonempty) (hsub : X₀⊆X) (hWsub : X₀⊆W)
    (c : ℝ) (hc : 0 < c) (hcap : c*(X.card:ℝ)≤(X₀.card:ℝ))
    (h : ℕ) (hh : 0<h) (Good : (Fin h → Ω) → Prop)
    (hGood : (9/10:ℝ)≤prob (uniformMass X₀) h Good)
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (y : Y) (m : ℕ) :
    PublicTables.integral (rowLaw W hW h) (implementAccept X₀ Good)
      (fun z => if ¬pass R q z y then 1 else 0) m ≤
        (6/c)*q*(∑ x∈univ.filter (fun x => R x y),uniformMass X x) := by
  apply (produced_exclusion X₀ W hX₀ hW hWsub h hh Good hGood R q hq y m).trans
  have hm := mul_le_mul_of_nonneg_left (uniform_sum_mono hX hX₀ hsub c hc hcap
    (E:=univ.filter (fun x => R x y))) (show 0≤6*q by positivity)
  exact hm.trans_eq (by ring)

end
end SharpLogRamsey.Validation

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds SharpLogRamsey.Incidence
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem projective_public_validation {n : ℕ} (hdim : Module.finrank K V=n+3)
    (X W : Finset (Projectivization K V)) (hX : X.Nonempty) (hW : W.Nonempty)
    (hsub : X⊆W) (U T : Finset (Projectivization K (Module.Dual K V)))
    (hT : T.Nonempty) (h : ℕ) (hh : 0<h) (M : ℝ) (hM : 0<M)
    (hsize : 36*(Nat.card K:ℝ)^(n+3)/(X.card:ℝ)+
      (U.card:ℝ)*Real.exp (1-(h:ℝ)/(20*(Nat.card K:ℝ))) ≤ M/20)
    (hsparse : (∑ y∈T,∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass X x)
      ≤ (T.card:ℝ)/(10000*(Nat.card K:ℝ))) (m : ℕ)
    (hsearch : (Nat.card K:ℝ)≤(m:ℝ)*(((X.card:ℝ)/(W.card:ℝ))^h*(9/10))) :
    1-PublicTables.integral (rowLaw W hW h)
        (implementAccept X (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) U T M)) (fun _ => 1) m
      ≤ Real.exp (-(Nat.card K:ℝ)) ∧
    ∀ y, PublicTables.integral (rowLaw W hW h)
        (implementAccept X (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) U T M))
        (fun z => if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) z y then 1 else 0) m
      ≤ 6*(Nat.card K:ℝ)*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass X x) := by
  have hg : (9/10:ℝ)≤prob (uniformMass X) h (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) U T M) :=
    projective_ideal_acceptance hdim X hX U T hT h hh M hM hsize hsparse
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.card_pos (α:=K)
  constructor
  · apply (PublicTables.failure_exp (rowLaw W hW h) _ m).trans
    apply Real.exp_le_exp.mpr
    rw [proposal_acceptance X W hX hW hsub]
    have hmul := mul_le_mul_of_nonneg_left hg
      (show 0≤(m:ℝ)*((X.card:ℝ)/(W.card:ℝ))^h by positivity)
    nlinarith
  · intro y
    exact produced_exclusion X W hX hW hsub h hh _ hg SharpLogRamsey.Incidence.Incident _ hq y m

end
end SharpLogRamsey.Validation

open scoped BigOperators
open Finset
open scoped Classical

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section

def scheduleLength (q u t : ℝ) : ℕ := ⌈20*q*(log (u/t)+2)⌉₊

def scheduleCutoff (q a : ℝ) (h : ℕ) : ℕ := ⌈2*q*exp ((h:ℝ)*a)⌉₊

lemma scheduleLength_pos {q u t : ℝ} (hq : 0<q) (ht : 0<t) (htu : t≤u) :
    0 < scheduleLength q u t := by
  have hd : 0≤log (u/t) := log_nonneg ((le_div_iff₀ ht).mpr (by simpa using htu))
  have hh : 0<20*q*(log (u/t)+2) := by positivity
  exact Nat.ceil_pos.mpr hh

lemma scheduleLength_size {q u t s x Q C : ℝ} (hq : 0<q) (ht : 0<t)
    (htu : t≤u) (hs : 0 < s) (hx : 0<x) (hC : 1≤C)
    (hcap : s≤C*x) (hprod : s*t≤2*Q) (hQ : 0≤Q) :
    36*Q/x+u*exp (1-(scheduleLength q u t:ℝ)/(20*q))≤(1000*C*Q/s)/20 := by
  have hu : 0<u := ht.trans_le htu
  have hh := Nat.le_ceil (20*q*(log (u/t)+2))
  have he : 1-(scheduleLength q u t:ℝ)/(20*q)≤ -log (u/t) := by
    have hp : 0<20*q := by positivity
    have hh' : log (u/t)+2≤(scheduleLength q u t:ℝ)/(20*q) := by
      apply (le_div_iff₀ hp).mpr
      simpa only [scheduleLength,mul_comm] using hh
    linarith
  have hrow : u*exp (1-(scheduleLength q u t:ℝ)/(20*q))≤t := by
    apply (mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) hu.le).trans_eq
    rw [exp_neg,exp_log (div_pos hu ht)]
    field_simp
  have hsmall : 36*Q/x≤36*C*Q/s := by
    apply (div_le_div_iff₀ hx hs).mpr
    have hh := mul_le_mul_of_nonneg_left hcap (show 0≤36*Q by positivity)
    nlinarith only [hh]
  have htarget : t≤2*Q/s := (le_div_iff₀ hs).mpr (by nlinarith only [hprod])
  have haux : 2*Q/s≤2*C*Q/s := by
    simpa only [mul_one] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hC (by norm_num : (0:ℝ)≤2)) hQ) hs.le
  have hsz := add_le_add hsmall (hrow.trans (htarget.trans haux))
  have hp : 0≤C*Q/s := by positivity
  apply hsz.trans
  convert mul_le_mul_of_nonneg_right (show (38:ℝ) ≤ 50 by norm_num) hp using 1 <;> ring

lemma scheduleCutoff_search {q x w a : ℝ} (hq : 0<q) (hx : 0<x) (hw : 0<w)
    (hratio : w≤exp a*x) (h : ℕ) :
    q≤(scheduleCutoff q a h:ℝ)*((x/w)^h*(9/10)) := by
  have hr : w/x≤exp a := (div_le_iff₀ hx).mpr hratio
  have hp := pow_le_pow_left₀ (div_nonneg hw.le hx.le) hr h
  rw [←exp_nat_mul] at hp
  have hh := Nat.le_ceil (2*q*exp ((h:ℝ)*a))
  have he : (w/x)^h*(x/w)^h=1 := by rw [←mul_pow]; field_simp; simp
  have hs := mul_le_mul_of_nonneg_right hp (show 0≤(x/w)^h by positivity)
  rw [he] at hs
  have hs' := mul_le_mul_of_nonneg_right hh (show 0≤(x/w)^h*(9/10:ℝ) by positivity)
  change q≤(⌈2*q*exp ((h:ℝ)*a)⌉₊:ℝ)*_
  nlinarith [mul_le_mul_of_nonneg_left hs hq.le]

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K V))] in
lemma uniform_incidence_sum (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    (∑ y∈T,∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass S x)=
      (incidenceCount S T:ℝ)/S.card := by
  simp_rw [uniform_sum]
  rw [←sum_div]
  congr 1
  unfold incidenceCount
  push_cast
  apply sum_congr rfl
  intro y _
  congr 1
  apply congrArg Finset.card
  ext x
  simp only [mem_inter,mem_filter,mem_univ,true_and]
  tauto

theorem scheduled_validation {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S X W : Finset (Projectivization K V)) (hS : S.Nonempty) (hX : X.Nonempty)
    (hXS : X⊆S) (hXW : X⊆W)
    (T U : Finset (Projectivization K (Module.Dual K V))) (hT : T.Nonempty) (hTU : T⊆U)
    (C a : ℝ) (hC : 1≤C) (hcap : (S.card:ℝ)≤C*X.card)
    (hratio : (W.card:ℝ)≤exp a*X.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(10000*C*Nat.card K)) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q U.card T.card
    let m := scheduleCutoff q a h
    let M := 1000*C*q^(n+3)/S.card
    let accept := implementAccept X (GoodCap SharpLogRamsey.Incidence.Incident q U T M)
    (9/10:ℝ)≤prob (uniformMass X) h (GoodCap SharpLogRamsey.Incidence.Incident q U T M) ∧
    1-PublicTables.integral (rowLaw W (hX.mono hXW) h) accept (fun _ => 1) m≤exp (-q) ∧
    (∀ y,PublicTables.integral (rowLaw W (hX.mono hXW) h) accept
      (fun z => if ¬pass SharpLogRamsey.Incidence.Incident q z y then 1 else 0) m≤
        6*C*q*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass S x)) := by
  dsimp only
  let q : ℝ := Nat.card K
  let h := scheduleLength q U.card T.card
  let m := scheduleCutoff q a h
  let M := 1000*C*q^(n+3)/S.card
  have hq : 0<q := by
    change 0 < (Nat.card K:ℝ)
    exact_mod_cast (Nat.card_pos : 0<Nat.card K)
  have hs : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have hx : (0:ℝ)<X.card := by exact_mod_cast card_pos.mpr hX
  have hw : (0:ℝ)<W.card := by exact_mod_cast card_pos.mpr (hX.mono hXW)
  have ht : (0:ℝ)<T.card := by exact_mod_cast card_pos.mpr hT
  have htu : (T.card:ℝ)≤U.card := by exact_mod_cast card_le_card hTU
  have hC0 : 0<C := by linarith
  have hsp : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K) := by
    apply hsparse.trans
    gcongr
    have hqn : (0:ℝ)<Nat.card K := hq
    nlinarith
  have hprod := sparse_product_bound_two hdim S T hsp
  have hsize := scheduleLength_size hq ht htu hs hx hC hcap hprod (pow_nonneg hq.le (n+3))
  have hinc : (incidenceCount X T:ℝ)≤(incidenceCount S T:ℝ) := by
    unfold incidenceCount
    push_cast
    apply sum_le_sum
    intro y _
    exact_mod_cast card_le_card (filter_subset_filter _ hXS)
  have hsp' : (∑ y∈T,∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass X x)≤
      (T.card:ℝ)/(10000*q) := by
    rw [uniform_incidence_sum]
    apply (div_le_iff₀ hx).mpr
    apply hinc.trans (hsparse.trans _)
    apply (div_le_iff₀ (by positivity : 0<10000*C*(Nat.card K:ℝ))).mpr
    have he : (T.card:ℝ)/(10000*q)*X.card*(10000*C*Nat.card K)=C*X.card*T.card := by
      dsimp [q]; field_simp [show (Nat.card K:ℝ) ≠ 0 from hq.ne']
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_right hcap ht.le]
  have hh : 0<h := scheduleLength_pos hq ht htu
  have hM : 0<M := by dsimp [M]; positivity
  have hg := projective_ideal_acceptance hdim X hX U T hT h hh M hM hsize hsp'
  have hsearch := scheduleCutoff_search hq hx hw hratio h
  have hval := projective_public_validation hdim X W hX (hX.mono hXW) hXW U T hT h hh M hM hsize hsp' m hsearch
  refine ⟨hg,hval.1,?_⟩
  intro y
  have habs := original_exclusion X S W hX hS (hX.mono hXW) hXS hXW
    C⁻¹ (inv_pos.mpr hC0) ((inv_mul_le_iff₀ hC0).mpr hcap)
    h hh (GoodCap SharpLogRamsey.Incidence.Incident q U T M) hg SharpLogRamsey.Incidence.Incident q hq y m
  simpa only [div_inv_eq_mul] using habs

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectiveTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ProjectiveDuality
open Incidence Finset
open scoped Classical BigOperators
noncomputable section
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

variable [FiniteDimensional K V]
lemma incidenceCount_bidual (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    incidenceCount T (S.image bidual)=incidenceCount S T := by
  unfold incidenceCount
  rw [sum_image bidual.injective.injOn]
  simp only [incident_bidual]
  simp only [card_filter]
  rw [sum_comm]

end
end SharpLogRamsey.ProjectiveDuality

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_CardVectorLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset

section

namespace SharpLogRamsey.FiniteSamplingBounds
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω : Type*} [Fintype Ω]

noncomputable def rowTail (w : Ω → ℝ) (E : Finset Ω) (h T : ℕ) : ℝ :=
  ∑ z : Fin h → Ω, if T ≤ hitCount E z then rowWeight w z else 0

end
end SharpLogRamsey.FiniteSamplingBounds
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TailSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset

section

namespace SharpLogRamsey.HighRankSampling
open scoped BigOperators
open Finset Classical
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}
local instance flat_JoinedHighRankAssembly_1 : Fintype (Projectivization K (Fin n → K)) := Fintype.ofFinite _

end
end SharpLogRamsey.HighRankSampling
end

namespace SharpLogRamsey.HighRankDecoder
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def hitSpan {h : ℕ} (a : Ω → Module.Dual K V)
    (b : Ω → Projectivization K V) (y : Projectivization K V) (z : Fin h → Ω) :
    Submodule K V :=
  y.submodule ⊔ ⨆ i, if a (z i) y.rep = 0 then (b (z i)).submodule else ⊥

noncomputable def Admitted [FiniteDimensional K V] {h : ℕ}
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (z₁ z₂ : Fin h → Ω) (r T : ℕ)
    (y : Projectivization K V) (c : Projectivization K (Module.Dual K V)) : Prop :=
  Module.finrank K (hitSpan a b y z₁) = r ∧
  hitSpan a b y z₁ ≤ LinearMap.ker c.rep ∧
  T ≤ (univ.filter (fun i => (b (z₂ i)).submodule ≤ hitSpan a b y z₁)).card

end
end SharpLogRamsey.HighRankDecoder

namespace SharpLogRamsey.HighRankExcess
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def projectiveSubmoduleEquiv (W : Submodule K V) :
    Projectivization K W ≃ {a : Projectivization K V // a.submodule ≤ W} := by
  let f : Projectivization K W → {a : Projectivization K V // a.submodule ≤ W} :=
    fun a => ⟨Projectivization.map W.subtype W.injective_subtype a, by
      induction a using Projectivization.ind with
      | h v hv =>
        rw [Projectivization.map_mk, Projectivization.submodule_mk,
          Submodule.span_singleton_le_iff_mem]
        exact v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    exact Projectivization.map_injective W.subtype W.injective_subtype
      (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    have hmem : a.rep ∈ W := ha (by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _)
    let v : W := ⟨a.rep, hmem⟩
    have hv : v ≠ 0 := fun h => a.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    exact a.mk_rep

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

def partners (W : Submodule K V) : Finset (Projectivization K (Module.Dual K V)) :=
  univ.filter (fun a => W ≤ LinearMap.ker a.rep)

def excessCarrier (U : Finset (Projectivization K V))
    (W : Projectivization K V → Submodule K V) (r : ℕ) :
    Finset (Projectivization K V × Projectivization K (Module.Dual K V)) :=
  (U ×ˢ univ).filter (fun z => r < Module.finrank K (W z.1) ∧ W z.1 ≤ LinearMap.ker z.2.rep)

end
end SharpLogRamsey.HighRankExcess
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TargetEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.FiniteMarginals
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι]

omit [Fintype Y] [Fintype ι] in
def marginal (w : Ω → ℝ) (f : Ω → Y) (y : Y) : ℝ := ∑ z, if f z=y then w z else 0

end
end SharpLogRamsey.FiniteMarginals

namespace SharpLogRamsey.HighRankSize
open scoped BigOperators
open Finset Classical HighRankDecoder FiniteMarginals
noncomputable section
variable {K Ω : Type*} [Field K] [Fintype K] [Fintype Ω] {n : ℕ}
local instance flat_JoinedHighRankAssembly_2 : Fintype (Projectivization K (Fin n → K)) := Fintype.ofFinite _
local instance flat_JoinedHighRankAssembly_3 : Finite (Module.Dual K (Fin n → K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin n → K) → ((Fin n → K) → K)) DFunLike.coe_injective
local instance flat_JoinedHighRankAssembly_4 : Fintype (Projectivization K (Module.Dual K (Fin n → K))) := Fintype.ofFinite _

def rankPoints {h : ℕ} (a : Ω → Module.Dual K (Fin n → K))
    (b : Ω → Projectivization K (Fin n → K)) (z₁ : Fin h → Ω) (r : ℕ) :=
  univ.filter (fun y => Module.finrank K (hitSpan a b y z₁)=r)

def points {h : ℕ} (a : Ω → Module.Dual K (Fin n → K))
    (b : Ω → Projectivization K (Fin n → K)) (z₁ z₂ : Fin h → Ω) (r T : ℕ) :=
  (rankPoints a b z₁ r).filter (fun y =>
    T ≤ (univ.filter (fun i => (b (z₂ i)).submodule ≤ hitSpan a b y z₁)).card)

def domain {h : ℕ} (a : Ω → Module.Dual K (Fin n → K))
    (b : Ω → Projectivization K (Fin n → K)) (z₁ z₂ : Fin h → Ω) (r T : ℕ) :
    Finset (Projectivization K (Fin n → K) × Projectivization K (Module.Dual K (Fin n → K))) :=
  univ.filter (fun t => Admitted a b z₁ z₂ r T t.1 t.2)

end
end SharpLogRamsey.HighRankSize

namespace SharpLogRamsey.FiniteRowProcess
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω X : Type*} [Fintype Ω]

def weight (w : Ω → ℝ) {n : ℕ} (z : Fin n → Ω) : ℝ := ∏ i, w (z i)

def run (step : X → Ω → X) : (n : ℕ) → (Fin n → Ω) → X → X
  | 0, _, x => x
  | n+1, z, x => run step n (Fin.tail z) (step x (z 0))

def expected (w : Ω → ℝ) (step : X → Ω → X) (n : ℕ) (x : X) (f : X → ℝ) : ℝ :=
  ∑ z : Fin n → Ω, weight w z * f (run step n z x)

end
end SharpLogRamsey.FiniteRowProcess

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_RowSpan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.HighRankCoverage
open scoped BigOperators
open Finset Classical FiniteRowProcess
noncomputable section
variable {Ω K V : Type*} [Fintype Ω] [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
def rowSpan (A : Ω → Submodule K V) {m : ℕ} (W : Submodule K V) (z : Fin m → Ω) :
    Submodule K V := W ⊔ ⨆ i, A (z i)

noncomputable def projectiveSubmoduleEquiv (W : Submodule K V) :
    Projectivization K W ≃ {a : Projectivization K V // a.submodule ≤ W} := by
  let f : Projectivization K W → {a : Projectivization K V // a.submodule ≤ W} :=
    fun a => ⟨Projectivization.map W.subtype W.injective_subtype a, by
      induction a using Projectivization.ind with
      | h v hv =>
        rw [Projectivization.map_mk, Projectivization.submodule_mk,
          Submodule.span_singleton_le_iff_mem]
        exact v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    exact Projectivization.map_injective W.subtype W.injective_subtype
      (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    have hmem : a.rep ∈ W := ha (by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _)
    let v : W := ⟨a.rep, hmem⟩
    have hv : v ≠ 0 := fun h => a.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    exact a.mk_rep

variable [Finite K] [Fintype (Projectivization K V)]

omit [Fintype Ω] [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)] in
def hitSpace (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (z : Ω) : Submodule K V :=
  if a z y.rep = 0 then (b z).submodule else ⊥

end
end SharpLogRamsey.HighRankCoverage

namespace SharpLogRamsey.FiniteEventBounds
open scoped BigOperators
open Finset Classical
noncomputable section

noncomputable def indicator (P : Prop) : ℝ := if P then 1 else 0

variable {X Y : Type*} [Fintype X] [Fintype Y]

def mean2 (w : X → ℝ) (v : Y → ℝ) (f : X → Y → ℝ) : ℝ :=
  ∑ x, w x*∑ y, v y*f x y

end
end SharpLogRamsey.FiniteEventBounds

namespace SharpLogRamsey.HighRankCoverageProbability
open scoped BigOperators
open Finset Classical FiniteEventBounds HighRankDecoder
noncomputable section
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (Projectivization K V)] [Fintype Ω]

noncomputable def conflictMass (w : Ω → ℝ) (a : Ω → Module.Dual K V)
    (b : Ω → Projectivization K V) (y : Projectivization K V)
    (c : Projectivization K (Module.Dual K V)) : ℝ :=
  ∑ z, w z*indicator (a z y.rep=0 ∧ c.rep (b z).rep≠0)

omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] [Fintype (Projectivization K V)] in

end
end SharpLogRamsey.HighRankCoverageProbability
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_RawLowerTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.HighRankBudgets
open Filter Real
open scoped Topology BigOperators
noncomputable section

def beta (η : ℝ) : ℝ := η/10000000
def scaleK (σ η D : ℝ) : ℝ := D*σ^(3*beta η)

end
end SharpLogRamsey.HighRankBudgets
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_AtomEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.HighRankBudgets
open Filter Real
open scoped Topology BigOperators
noncomputable section

def error (σ η D C : ℝ) (d : ℕ) : ℝ :=
  100*C^2*Real.exp (2*scaleK σ η D)/Real.exp σ +
  d*Real.exp (-(3/(20*d))*σ^beta η) +
  Real.exp 1*Real.exp (-(1/10)*σ^beta η) +
  4*C*σ^(-(1999*beta η)) +
  C*(σ^(-(2*beta η))+σ^(-(4*beta η))) +
  2*C*Real.exp (scaleK σ η D)/Real.exp σ

end
end SharpLogRamsey.HighRankBudgets

namespace SharpLogRamsey.HighRankAssembly
open scoped BigOperators
open Finset Classical HighRankDecoder HighRankCoverageProbability FiniteEventBounds
open FiniteMarginals
noncomputable section
variable {K Ω : Type*} [Field K] [Fintype K] [Fintype Ω]
variable {d : ℕ}
local notation "V" => (Fin (d+1) → K)
local notation "A" => Projectivization K (Module.Dual K V)
local notation "B" => Projectivization K V
local instance flat_JoinedHighRankAssembly_6 : Fintype B := Fintype.ofFinite _
local instance flat_JoinedHighRankAssembly_7 : Finite (Module.Dual K V) :=
  Finite.of_injective ((↑) : Module.Dual K V → (V → K)) DFunLike.coe_injective
local instance flat_JoinedHighRankAssembly_8 : Fintype A := Fintype.ofFinite _

end
end SharpLogRamsey.HighRankAssembly

namespace SharpLogRamsey.HighRankAssembly
open scoped BigOperators Classical
open Finset HighRankDecoder HighRankCoverageProbability FiniteEventBounds
open FiniteMarginals
noncomputable section
variable {K Ω Ξ : Type*} [Field K] [Fintype K] [Fintype Ω] [Fintype Ξ]
variable {d : ℕ}
local instance flat_JoinedHighRankAssembly_9 : Finite (Module.Dual K (Fin (d+1) → K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1) → K) → ((Fin (d+1) → K) → K)) DFunLike.coe_injective
local instance flat_JoinedHighRankAssembly_10 : Fintype (Projectivization K (Fin (d+1) → K)) := Fintype.ofFinite _
local instance flat_JoinedHighRankAssembly_11 : Fintype (Projectivization K (Module.Dual K (Fin (d+1) → K))) := Fintype.ofFinite _
end
end SharpLogRamsey.HighRankAssembly

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_HighRankExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection FiniteMarginals HighRankCoverageProbability FiniteEventBounds HighRankAssembly
open scoped Classical BigOperators
noncomputable section
variable {K Ξ : Type} [Field K] [Fintype K] [Fintype Ξ] {d : ℕ}
local instance flat_ActualHighRankExtraction_1 : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankExtraction_2 : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankExtraction_3 : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Filter HighRankBudgets
open scoped Topology BigOperators
noncomputable section

def rawRows (σ η : ℝ) : ℕ := ⌈exp σ*σ^beta η⌉₊
def rawThreshold (σ η : ℝ) : ℕ := ⌈(rawRows σ η:ℝ)/(10*exp σ)⌉₊
def richDensity : ℝ := 1/(100*exp (1/2))
def rawError (σ η D : ℝ) (d : ℕ) : ℝ :=
  4365*σ^(-2*beta η)+100*1024^2*exp (2*scaleK σ η D)/exp σ+
    (d*exp (-3*(rawRows σ η:ℝ)/(20*d*exp σ))+exp (1-(rawRows σ η:ℝ)/(10*exp σ)))+
    4*(rawRows σ η)* (2*σ^(-2000*beta η)/exp σ)+2048*exp (scaleK σ η D)/exp σ

end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_HighRankSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Filter Selection HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section
variable {K Ξ : Type} [Field K] [Fintype K] [Fintype Ξ] {d : ℕ}
local instance flat_ActualHighRankSuccess_1 : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankSuccess_2 : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankSuccess_3 : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local notation "A" => Projectivization K (Module.Dual K (Fin (d+1)→K))
local notation "B" => Projectivization K (Fin (d+1)→K)

def rawDomain {h : ℕ} (z : (Fin h→A×B)×(Fin h→A×B)) (r T : ℕ) : Finset (A×B) :=
  (HighRankSize.domain (fun z : A×B=>z.1.rep) (fun z : A×B=>z.2) z.1 z.2 r T).image Prod.swap

def highPrefactor (d : ℕ) : ℝ :=
  8*(10*((d:ℝ)+1)*1024/richDensity)^(d+1)*1024*(1+2^(d+2))

end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_HighRankReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Filter Selection HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section

structure Replacement {F Ξ Γ : Type} [Fintype F] [Fintype Ξ] [Fintype Γ]
    (p : Law Ξ) {ℓ : ℕ} (f : Ξ→Fin ℓ→F) (DD : Γ→Finset F) (B C : ℝ) where
  Ω : Type
  inst : Fintype Ω
  μ : @Law Ω inst
  source : Ω→Ξ
  msg : Ω→Γ
  chosen : Ω→(Fin (ℓ/2)↪o Fin ℓ)
  hit : ∀ ω i,f (source ω) (chosen ω i)∈DD (msg ω)
  size : ∀ ω,((DD (msg ω)).card:ℝ)≤B
  dominated : letI := inst; ∀ a,(μ.map source).mass a≤2*p.mass a
  cost : letI := inst; entropy (μ.map msg)≤C
attribute [instance] Replacement.inst

section Generic
variable {F Ξ : Type} [Fintype F] [Fintype Ξ]

variable {Γ : Type} [Fintype Γ] {p : Law Ξ} {ℓ : ℕ} {f : Ξ→Fin ℓ→F}
  {DD : Γ→Finset F} {B C C' : ℝ}

def Replacement.cost_mono (e : Replacement p f DD B C) (h : C≤C') :
    Replacement p f DD B C' := { e with cost := e.cost.trans h }
end Generic

variable {K Ξ : Type} [Field K] [Fintype K] [Fintype Ξ] {d : ℕ}
local instance flat_ActualHighRankReplacement_1 : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance flat_ActualHighRankReplacement_2 : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance flat_ActualHighRankReplacement_3 : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local notation "A" => Projectivization K (Module.Dual K (Fin (d+1)→K))
local notation "B" => Projectivization K (Fin (d+1)→K)
local notation "q" => (Nat.card K:ℝ)

structure Caps (σ : ℝ) (r r' : ℕ) (S : Finset (A×B)) : Prop where
  first : ((S.image Prod.fst).card:ℝ)≤1024*q^r'
  second : ((S.image Prod.snd).card:ℝ)≤1024*q^r
  joint : (S.card:ℝ)≤64*q^d
  firstFiber : ∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤2*exp (((d:ℝ)-r')*σ)
  secondFiber : ∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤2*exp (((d:ℝ)-r)*σ)

end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_CanonicalAuxiliaryLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {A B Ω Θ : Type*} [Fintype A] [Fintype B] [Fintype Ω] [Fintype Θ]

namespace AuxiliarySupport
variable {p : Law A} {good : Finset A} {M κ : ℝ}

def setLaw (X : AuxiliarySupport p good M κ) : Law (Finset A) :=
  X.law.map (fun b => levelSet p b ∩ good)

lemma setLaw_support (X : AuxiliarySupport p good M κ) (S : Finset A)
    (hS : X.setLaw.mass S ≠ 0) :
    S ⊆ good ∧ M * exp (-κ) / 2 ≤ (S.card : ℝ) ∧ (S.card : ℝ) ≤ M := by
  obtain ⟨b,hb,rfl⟩ := X.law.map_support (fun b => levelSet p b ∩ good) S hS
  exact ⟨inter_subset_right, X.size b⟩

end AuxiliarySupport

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_AuxiliaryFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {A B I J Ω Θ : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
  [Fintype Ω] [Fintype Θ]

namespace AuxiliarySupport
variable {p : I → Law A} {q : J → Law B} {goodA : I → Finset A}
  {goodB : J → Finset B} {MA κA : I → ℝ} {MB κB : J → ℝ}

def familyLaw (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j)) :
    Law ((I → Finset A) × (J → Finset B)) :=
  (Law.pi (fun i => (X i).setLaw)).prod (Law.pi (fun j => (Y j).setLaw))

lemma familyLaw_support (X : ∀ i, AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ j, AuxiliarySupport (q j) (goodB j) (MB j) (κB j))
    (z : (I → Finset A) × (J → Finset B)) (hz : (familyLaw X Y).mass z ≠ 0) :
    (∀ i, z.1 i ⊆ goodA i ∧ MA i * exp (-κA i) / 2 ≤ ((z.1 i).card : ℝ) ∧
      ((z.1 i).card : ℝ) ≤ MA i) ∧
    (∀ j, z.2 j ⊆ goodB j ∧ MB j * exp (-κB j) / 2 ≤ ((z.2 j).card : ℝ) ∧
      ((z.2 j).card : ℝ) ≤ MB j) := by
  have hz' : (∏ i, (X i).setLaw.mass (z.1 i)) *
      (∏ j, (Y j).setLaw.mass (z.2 j)) ≠ 0 := hz
  constructor
  · intro i
    apply (X i).setLaw_support
    exact (prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hz').1) i (mem_univ _)
  · intro j
    apply (Y j).setLaw_support
    exact (prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hz').2) j (mem_univ _)

end AuxiliarySupport

lemma Law.history_observable_sum (μ : Law Ω) (θ : Ω → Θ) (F : Ω → B)
    (f : Θ → B → ℝ) :
    (∑ ω, μ.mass ω * f (θ ω) (F ω)) =
      ∑ z, (μ.map θ).mass z * ∑ b, ((μ.cond θ z).map F).mass b * f z b := by
  simp only [mul_sum, ← mul_assoc, Law.cond_map_weight]
  have h := μ.sum_map (fun ω => (F ω, θ ω)) (fun z => f z.2 z.1)
  rw [Fintype.sum_prod_type, sum_comm] at h
  exact h.symm

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_EightIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.CapComposition
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α : Type*}

def powers (L : Finset (Finset α)) (U : Finset α) : ℕ → Finset (Finset α)
  | 0 => {U}
  | k+1 => (powers L U k).biUnion (fun A => L.image (fun D => A∩D))

end
end SharpLogRamsey.CapComposition

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_DyadicGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.DyadicGrid
open Finset
open scoped BigOperators
noncomputable section

def value (i : ℕ) : ℝ := (1/2:ℝ)^i

end
end SharpLogRamsey.DyadicGrid

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_DescriptionHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.DescriptionHeaders
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

variable {α : Type*} [Fintype α]

def headers (J N : ℕ) : Finset (List (α×ℕ)) :=
  (range (J+1)).biUnion (fun m =>
    (univ : Finset (Fin m→α×Fin (N+1))).image
      (fun v => List.ofFn (fun i => ((v i).1,((v i).2:ℕ)))))

end
end SharpLogRamsey.DescriptionHeaders

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_MultiplicityClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.MultiplicityClass
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*}

def weight (S : Finset α) (f : α→β) (y : β) : ℕ := (S.filter (fun x => f x=y)).card

def domain (U : Finset α) (f : α→β) (h : ℕ) : Finset β :=
  (U.image f).filter (fun y => h≤weight U f y)

end
end SharpLogRamsey.MultiplicityClass

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_HeavyPlaneCurrent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset SharpLogRamsey.Incidence SharpLogRamsey.Projection
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def center (W : Submodule K V) (hW : Module.finrank K W + 1 = Module.finrank K V) :
    Projectivization K (Module.Dual K V) :=
  Projectivization.mk'' W.dualAnnihilator (by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    omega)

lemma center_submodule (W : Submodule K V)
    (hW : Module.finrank K W + 1 = Module.finrank K V) :
    (center W hW).submodule = W.dualAnnihilator := by
  simp [center]

lemma restrict_ne_zero (W : Submodule K V)
    (hW : Module.finrank K W + 1 = Module.finrank K V)
    (t : Projectivization K (Module.Dual K V)) (ht : t ≠ center W hW) :
    W.dualRestrict t.rep ≠ 0 := by
  intro h
  apply ht
  apply (rep_mem_line_iff t (center W hW)).mp
  rw [center_submodule, ← W.dualRestrict_ker_eq_dualAnnihilator]
  exact h

def restrict (W : Submodule K V)
    (hW : Module.finrank K W + 1 = Module.finrank K V)
    (t : {t : Projectivization K (Module.Dual K V) // t ≠ center W hW}) :
    Projectivization K (Module.Dual K W) :=
  Projectivization.mk K (W.dualRestrict t.val.rep) (restrict_ne_zero W hW t.val t.property)

end
end SharpLogRamsey.HeavyPlaneRestriction

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_HeavyPlaneInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedHeavyPlaneInput_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedHeavyPlaneInput_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedHeavyPlaneInput_4 (W : Submodule K V) : Fintype (Projectivization K W) := by
  let : Finite W := Module.finite_of_finite K
  exact Fintype.ofFinite _

local instance flat_JoinedHeavyPlaneInput_2_r98ddb2_1 : Fintype (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
def planeSupport (W : Submodule K V) (S : Finset (Projectivization K V)) :
    Finset (Projectivization K W) :=
  univ.filter (fun a => Projectivization.map W.subtype W.injective_subtype a∈S)

end
end SharpLogRamsey.HeavyPlaneRestriction

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Planar_HeavyPlanePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.HeavyPlaneRestriction
open Finset Real Filter SourceScales Incidence
open scoped Classical BigOperators Topology
noncomputable section
local instance flat_JoinedHeavyPlanePublic_2 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Fintype (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
local instance flat_JoinedHeavyPlanePublic_3 {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Fintype (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  let : Finite (Submodule K V) := Finite.of_injective
    (fun W : Submodule K V => (W:Set V)) SetLike.coe_injective
  exact Fintype.ofFinite _

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
abbrev HeavyHeaders (K V : Type) [Field K] [AddCommGroup V] [Module K V] (n m : ℕ) :=
  {W : Submodule K V // Module.finrank K W=3} × Fin (Nat.card K+1) × Fin (n+1) × Fin (m+1)
local instance flat_JoinedHeavyPlanePublic_4 (n m : ℕ) : Fintype (HeavyHeaders K V n m) := by
  unfold HeavyHeaders
  infer_instance
abbrev headerPlane {n m : ℕ} (j : HeavyHeaders K V n m) : Submodule K V := j.1.val
omit [Finite K] [FiniteDimensional K V] in
lemma header_rank {n m : ℕ} (j : HeavyHeaders K V n m) : Module.finrank K (headerPlane j)=3 := j.1.property
omit [Finite K] [FiniteDimensional K V] in
lemma header_codim (hV : Module.finrank K V=4) {n m : ℕ} (j : HeavyHeaders K V n m) :
    Module.finrank K (headerPlane j)+1=Module.finrank K V := by rw [header_rank,hV]
def headerDomain (hV : Module.finrank K V=4)
    (UT : Finset (Projectivization K (Module.Dual K V))) {n : ℕ}
    (j : HeavyHeaders K V n UT.card) := MultiplicityClass.domain
    (UT.subtype (· ≠ center (headerPlane j) (header_codim hV j)))
    (restrict (headerPlane j) (header_codim hV j)) j.2.1.val
def HeaderValid (hV : Module.finrank K V=4)
    (U : Finset (Projectivization K V)) (UT : Finset (Projectivization K (Module.Dual K V)))
    (n t : ℕ) (L b₁ : ℝ) (j : HeavyHeaders K V n UT.card) : Prop :=
    0<j.2.1.val ∧ 0<j.2.2.1.val ∧ 0<j.2.2.2.val ∧
    n≤50*j.2.2.1.val ∧ j.2.2.1.val≤(planeSupport (headerPlane j) U).card ∧
    j.2.2.2.val≤(headerDomain hV UT j).card ∧ j.2.1.val*(headerDomain hV UT j).card≤UT.card ∧
    (t:ℝ)≤4*j.2.1.val*L*j.2.2.2.val ∧
    (Nat.card K:ℝ)^3*exp (-b₁)≤(j.2.2.1.val:ℝ)*j.2.2.2.val ∧
    (j.2.2.1.val:ℝ)*j.2.2.2.val≤2*(Nat.card K:ℝ)^3

end
end SharpLogRamsey.HeavyPlaneRestriction

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_GeometricCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Incidence
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def Validated (q P H : ℝ) (r : ℕ)
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V)))
    (n t : ℕ) (τ : ℝ) : Prop :=
  ∃ F : Finset (Finset (Projectivization K V)),
    (∀ W∈F,W⊆U ∧ (W.card:ℝ)≤100000*q^r/t) ∧
    (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
      (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q →
      ∃ W∈F,(99/100:ℝ)*n≤(S∩W).card) ∧
    log ((F.card:ℝ)+1)≤H*q*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P)

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionMessageCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Validation
open scoped Classical
noncomputable section

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedProjectionMessageCost_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_QuotientHeader
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Incidence Projection
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]

def HeaderOK (q b : ℝ) (r N T Z W Udual a c : ℕ) : Prop :=
  0<a ∧ 0 < c ∧ a≤Z ∧ c≤W ∧
  (9/10:ℝ)*N≤a ∧ (T:ℝ)/(3*q) ≤ c ∧
  q^(r+3)*exp (-(b+log 4))≤(a:ℝ)*c ∧ (a:ℝ)*c≤2*q^(r+3) ∧
  (W:ℝ)≤100*Udual/q

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionFullDescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Incidence Projection CapComposition Validation
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedProjectionFullDescription_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_GeometricInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Filter SourceScales Incidence ProjectiveDuality Validation Projection
open scoped Classical Topology
noncomputable section

def Uniform (r : ℕ) (H : ℝ) : Prop :=
  ∀ η : ℝ,0<η → ∀ C : ℝ,1≤C →
  ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V],
    Module.finrank (ZMod q) V=r → ∀ D R,Admissible σ η D R →
    ∀ (U : Finset (Projectivization (ZMod q) V))
      (UT : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) V)))
      (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card →
    0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
    (q:ℝ)^r*exp (-b)≤(n:ℝ)*t → (n:ℝ)*t≤2*(q:ℝ)^r →
    Validated q (scaleP σ η D R) H r U UT n t τ

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ReadyProjectiveValidation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V I : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] in

lemma trimmed_sparse (S : Finset (Projectivization K V))
    (T T' : Finset (Projectivization K (Module.Dual K V))) (hT : T'⊆T)
    (C : ℝ) (hC : 0<C) (htrim : (T.card:ℝ)≤2*T'.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20000*C*Nat.card K)) :
    (incidenceCount S T':ℝ)≤(S.card:ℝ)*T'.card/(10000*C*Nat.card K) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos : 0<Nat.card K)
  have hi : incidenceCount S T'≤ incidenceCount S T := by
    apply sum_le_sum_of_subset_of_nonneg hT
    intros
    exact Nat.zero_le _
  apply (show (incidenceCount S T':ℝ)≤ incidenceCount S T by exact_mod_cast hi).trans
  apply hsparse.trans
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left htrim (Nat.cast_nonneg S.card))
    (show 0≤20000*C*(Nat.card K:ℝ) by positivity)
  convert hh using 1 <;> first | rfl | ring

theorem scheduled_from_original {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S X W : Finset (Projectivization K V)) (hS : S.Nonempty) (hX : X.Nonempty)
    (hXS : X⊆S) (hXW : X⊆W)
    (T T' U : Finset (Projectivization K (Module.Dual K V))) (hT' : T'.Nonempty)
    (hT'T : T'⊆T) (hT'U : T'⊆U) (htrim : (T.card:ℝ)≤2*T'.card)
    (C a : ℝ) (hC : 1≤C) (hcap : (S.card:ℝ)≤C*X.card)
    (hratio : (W.card:ℝ)≤exp a*X.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20000*C*Nat.card K)) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q U.card T'.card
    let m := scheduleCutoff q a h
    let M := 1000*C*q^(n+3)/S.card
    let accept := implementAccept X (GoodCap SharpLogRamsey.Incidence.Incident q U T' M)
    (9/10:ℝ)≤prob (uniformMass X) h (GoodCap SharpLogRamsey.Incidence.Incident q U T' M) ∧
    1-PublicTables.integral (rowLaw W (hX.mono hXW) h) accept (fun _ => 1) m≤exp (-q) ∧
    (∀ y,PublicTables.integral (rowLaw W (hX.mono hXW) h) accept
      (fun z => if ¬pass SharpLogRamsey.Incidence.Incident q z y then 1 else 0) m≤
        6*C*q*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass S x)) := by
  exact scheduled_validation hdim S X W hS hX hXS hXW T' U hT' hT'U C a hC hcap hratio
    (trimmed_sparse S T T' hT'T C (by linarith) htrim hsparse)

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PivotGeometry
open Finset Real Incidence Validation GeometricCover
open scoped Classical BigOperators
noncomputable section

lemma description_ratio {w Q A B X T b : ℝ} (hT : 0<T) (hX : 0≤X)
    (hAB : Q*exp (-b)≤A*B) (hA : A≤2*X) (hB : B≤2*T)
    (hB0 : 0≤B) (hW : w≤100000*Q/T) :
    w≤exp (b+log 1000000)*X := by
  have hQ : Q≤A*B*exp b := by
    have hh := mul_le_mul_of_nonneg_right hAB (exp_pos b).le
    have he : exp (-b)*exp b=1 := by rw [←exp_add]; simp
    simpa only [mul_assoc,he,mul_one] using hh
  have hprod : A*B≤(2*X)*(2*T) := mul_le_mul hA hB hB0 (by positivity)
  calc
    w ≤ 100000*Q/T := hW
    _ ≤ 100000*(A*B*exp b)/T := by gcongr
    _ ≤ 100000*((2*X)*(2*T)*exp b)/T := by gcongr
    _ = 400000*exp b*X := by field_simp; ring
    _ ≤ 1000000*exp b*X := by gcongr; norm_num
    _ = _ := by rw [exp_add,exp_log (by norm_num : (0:ℝ)<1000000)]; ring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma incidence_mono {A S : Finset (Projectivization K V)}
    {B T : Finset (Projectivization K (Module.Dual K V))} (hS : S⊆A) (hT : T⊆B) :
    incidenceCount S T≤ incidenceCount A B := by
  apply (sum_le_sum (fun y (_ : y∈T) => card_le_card (filter_subset_filter _ hS))).trans
  exact sum_le_sum_of_subset_of_nonneg hT (by intros; exact Nat.zero_le _)

theorem trimmed_inputs (A U : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V))) (q Q τ b : ℝ)
    (hq : 0<q) (hτ : 0≤τ) (htrimA : (A.card:ℝ)≤2*(A∩U).card)
    (htrimB : (B.card:ℝ)≤2*(B∩UT).card)
    (hprod : Q*exp (-b)≤(A.card:ℝ)*B.card)
    (hsp : (incidenceCount A B:ℝ)≤τ*(A.card:ℝ)*B.card/q) :
    Q*exp (-(b+log 4))≤((A∩U).card:ℝ)*(B∩UT).card ∧
    (incidenceCount (A∩U) (B∩UT):ℝ)≤4*τ*((A∩U).card:ℝ)*(B∩UT).card/q := by
  have hp : (A.card:ℝ)*B.card≤4*((A∩U).card:ℝ)*(B∩UT).card := by
    have hh := mul_le_mul htrimA htrimB (Nat.cast_nonneg _) (show 0≤2*((A∩U).card:ℝ) by positivity)
    nlinarith only [hh]
  constructor
  · have he : exp (-(b+log 4))=exp (-b)/4 := by
      rw [neg_add,exp_add,exp_neg (log 4),exp_log (by norm_num : (0:ℝ)<4)]; ring
    rw [he]
    linarith
  · have hm : (incidenceCount (A∩U) (B∩UT):ℝ)≤ incidenceCount A B := by
      exact_mod_cast incidence_mono (inter_subset_left) (inter_subset_left)
    apply hm.trans (hsp.trans _)
    have hh := mul_le_mul_of_nonneg_left hp hτ
    convert div_le_div_of_nonneg_right hh hq.le using 1 <;> ring

theorem first_source (A U : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V))) (q τ b : ℝ) (r : ℕ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hq : 0<q) (hτ : 0≤τ)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩UT).card)
    (hprod : q^r*exp (-b)≤(A.card:ℝ)*B.card)
    (hsp : (incidenceCount A B:ℝ)≤τ*(A.card:ℝ)*B.card/q)
    (F : Finset (Finset (Projectivization K V)))
    (hF : ∀ W∈F,W⊆U ∧ (W.card:ℝ)≤100000*q^r/(B∩UT).card)
    (hc : ∀ S T,S⊆U → S.card=(A∩U).card → T⊆UT → T.card=(B∩UT).card →
      (incidenceCount S T:ℝ)≤4*τ*((A∩U).card:ℝ)*(B∩UT).card/q →
      ∃ W∈F,(99/100:ℝ)*(A∩U).card≤(S∩W).card) :
    ∃ W∈F,W⊆U ∧ ((A∩U)∩W).Nonempty ∧
      (A.card:ℝ)≤2*((A∩U)∩W).card ∧
      (W.card:ℝ)≤exp (b+log 1000000)*((A∩U)∩W).card := by
  have hA' : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
  have hB' : (0:ℝ)<B.card := by exact_mod_cast card_pos.mpr hB
  have hcutA : (A.card:ℝ)≤2*(A∩U).card := by linarith
  have hcutB : (B.card:ℝ)≤2*(B∩UT).card := by linarith
  have hcutsp := (trimmed_inputs A U B UT q (q^r) τ b hq hτ hcutA hcutB hprod hsp).2
  obtain ⟨W,hW,hcapture⟩ := hc (A∩U) (B∩UT) inter_subset_right rfl inter_subset_right rfl hcutsp
  have hcap : (A.card:ℝ)≤2*((A∩U)∩W).card := by linarith
  have hx : (0:ℝ)<((A∩U)∩W).card := by linarith
  have ht : (0:ℝ)<(B∩UT).card := by linarith
  refine ⟨W,hW,(hF W hW).1,card_pos.mp (by exact_mod_cast hx),hcap,?_⟩
  exact description_ratio ht hx.le hprod hcap hcutB (Nat.cast_nonneg _) (hF W hW).2

theorem second_source {Ω : Type*} (B T W : Finset Ω)
    (hB : B.Nonempty) (htrim : (9/10:ℝ)*B.card≤T.card)
    (hcap : (99:ℝ)*T.card≤100*(T∩W).card) :
    (T∩W).Nonempty ∧ (B.card:ℝ)≤2*(T∩W).card := by
  have hb : (0:ℝ)<B.card := by exact_mod_cast card_pos.mpr hB
  have hc : (B.card:ℝ)≤2*(T∩W).card := by linarith
  refine ⟨card_pos.mp ?_,hc⟩
  exact_mod_cast (by linarith : (0:ℝ)<(T∩W).card)

end
end SharpLogRamsey.PivotGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_TreeDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.TreeDecoder
open BinaryTree List
open scoped Classical
noncomputable section
variable {A B I C : Type*}

abbrev Domains (A B : Type*) := Finset A × Finset B

abbrev CapReader (A B C : Type*) := Domains A B → C → Domains A B

def execute (read : CapReader A B C) (choose : I → Domains A B → Option C) :
    BinaryTree I → Domains A B → BinaryTree (I×C)
  | .nil, _ => .nil
  | .node i l r, U => match choose i U with
    | none => .nil
    | some c =>
      let V := read U c
      .node (i,c) (execute read choose l (V.1,U.2))
        (execute read choose r (U.1,V.2))

def flagDomain (R : A → B → Prop) (U : Domains A B) : Finset (A×B) :=
  (U.1×ˢU.2).filter (fun z => R z.1 z.2)

def retained (R : A → B → Prop) (U : Domains A B) (xs : List (A×B)) (n : ℕ) : List (A×B) :=
  (xs.filter (fun z => z∈flagDomain R U)).take n

def output (R : A → B → Prop) (read : CapReader A B C)
    (targets : I → List (A×B)) (counts : I → ℕ) : BinaryTree (I×C) → Domains A B → List (A×B)
  | .nil, _ => []
  | .node (i,c) l r, U =>
    let V := read U c
    output R read targets counts l (V.1,U.2) ++
      retained R V (targets i) (counts i) ++
        output R read targets counts r (U.1,V.2)

def message (R : A → B → Prop) (read : CapReader A B C)
    (targets : I → List (A×B)) (counts : I → ℕ) : BinaryTree (I×C) → Domains A B → BinaryTree (C×ℕ)
  | .nil, _ => .nil
  | .node (i,c) l r, U =>
    let V := read U c
    .node (c,(retained R V (targets i) (counts i)).length)
      (message R read targets counts l (V.1,U.2))
      (message R read targets counts r (U.1,V.2))

end
end SharpLogRamsey.TreeDecoder

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotValidation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PivotGeometry
open Finset Real Incidence Validation GeometricCover ProjectiveDuality
open scoped Classical BigOperators
noncomputable section

lemma second_ratio {w Q A B X b : ℝ} (hA : 0<A) (hX : 0≤ X)
    (hprod : Q*exp (-b)≤ A*B) (hsource : B≤2*X) (hW : w≤2000*Q/A) :
    w≤ exp (b+log 1000000)*X := by
  have hp : Q≤ A*B*exp b := by
    simpa only [mul_assoc, ←exp_add, neg_add_cancel, exp_zero, mul_one] using
      mul_le_mul_of_nonneg_right hprod (exp_pos b).le
  calc
    w ≤ 2000*Q/A := hW
    _ ≤ 2000*(A*B*exp b)/A := by gcongr
    _ = 2000*B*exp b := by field_simp
    _ ≤ 4000*X*exp b := by nlinarith [mul_le_mul_of_nonneg_right hsource (show 0≤2000*exp b by positivity)]
    _ ≤ 1000000*X*exp b := by gcongr; norm_num
    _ = _ := by rw [exp_add,exp_log (by norm_num : (0:ℝ)<1000000)]; ring

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

theorem second_scheduled {n : ℕ} (hdim : Module.finrank K V=n+3)
    (A U W : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩UT).card)
    (b : ℝ) (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card)
    (hsparse : (incidenceCount A B:ℝ)≤(A.card:ℝ)*B.card/(40000*Nat.card K))
    {h m : ℕ} (table : PublicTables.Table (Fin h→Projectivization K V) m) (i : Fin m)
    (hi : PublicTables.firstIndex (implementAccept ((A∩U)∩W)
      (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K) UT (B∩UT) (2000*(Nat.card K:ℝ)^(n+3)/A.card))) m table=some i) :
    let q : ℝ := Nat.card K
    let e := bidual (K:=K) (V:=V)
    let capB := cap SharpLogRamsey.Incidence.Incident q UT (PublicTables.rowAt m table i)
    let sourceB := (B∩UT)∩capB
    let targetA := (A∩U).image e
    let domainA := U.image e
    let h' := scheduleLength q domainA.card targetA.card
    let m' := scheduleCutoff q (b+log 1000000) h'
    let M' := 2000*q^(n+3)/B.card
    sourceB.Nonempty ∧ (B.card:ℝ)≤2*sourceB.card ∧
    (capB.card:ℝ)≤ exp (b+log 1000000)*sourceB.card ∧
    ∀ hcapB : capB.Nonempty,
      (9/10:ℝ)≤ prob (uniformMass sourceB) h' (GoodCap SharpLogRamsey.Incidence.Incident q domainA targetA M') ∧
      1-PublicTables.integral (rowLaw capB hcapB h')
        (implementAccept sourceB (GoodCap SharpLogRamsey.Incidence.Incident q domainA targetA M')) (fun _ => 1) m'≤ exp (-q) ∧
      ∀ y,PublicTables.integral (rowLaw capB hcapB h')
        (implementAccept sourceB (GoodCap SharpLogRamsey.Incidence.Incident q domainA targetA M'))
        (fun z => if ¬pass SharpLogRamsey.Incidence.Incident q z y then 1 else 0) m'≤
          12*q*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass B x) := by
  dsimp only
  let e := bidual (K:=K) (V:=V)
  let capB := cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT (PublicTables.rowAt m table i)
  let sourceB := (B∩UT)∩capB
  have hd := decoded_cap ((A∩U)∩W) SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT (B∩UT)
    inter_subset_right (2000*(Nat.card K:ℝ)^(n+3)/A.card) h m table i hi
  have hs := second_source B (B∩UT) capB hB htrimB hd.2.2
  have hApos : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
  have hA' : (A∩U).Nonempty := card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ)<(A∩U).card))
  have hratio := second_ratio hApos (Nat.cast_nonneg sourceB.card) hprod hs.2 hd.2.1
  refine ⟨hs.1,hs.2,hratio,?_⟩
  intro hcapB
  have hdu : Module.finrank K (Module.Dual K V)=n+3 := Subspace.dual_finrank_eq.trans hdim
  have hAa : (A.image e).card=A.card := card_image_of_injective _ e.injective
  have hTa : ((A∩U).image e).card=(A∩U).card := card_image_of_injective _ e.injective
  have hsp : (incidenceCount B (A.image e):ℝ)≤(B.card:ℝ)*(A.image e).card/(20000*2*Nat.card K) := by
    rw [incidenceCount_bidual,hAa]
    convert hsparse using 1 <;> first | rfl | ring
  have hh := scheduled_from_original hdu B sourceB capB hB hs.1
    (inter_subset_left.trans inter_subset_left) inter_subset_right
    (A.image e) ((A∩U).image e) (U.image e) (hA'.image e)
    (image_subset_image inter_subset_left) (image_subset_image inter_subset_right)
    (by rw [hAa,hTa]; linarith) 2 (b+log 1000000) (by norm_num) hs.2 hratio hsp
  dsimp only at hh
  norm_num only [show (1000:ℝ)*2=2000 by norm_num,
    show (6:ℝ)*2=12 by norm_num] at hh
  exact hh

end
end SharpLogRamsey.PivotGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_FreshFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset
open scoped Classical BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι→Type*} [∀ i,Fintype (α i)]

 def piLaw (p : ∀ i,Law (α i)) : Law (∀ i,α i) where
  mass z := ∏ i,(p i).mass (z i)
  nonneg z := prod_nonneg (fun i _=>(p i).nonneg (z i))
  total := by rw [←Fintype.prod_sum]; simp only [Law.total,prod_const_one]

abbrev Outside (i : ι) := ∀ j : {j // j≠i},α j

end
end SharpLogRamsey.PublicTables

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_ReadyTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ReadyTests
open Finset Real Incidence Validation SupportMixtures Selection
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

structure Call (S : Finset (Projectivization K V)) where
  source : Finset (Projectivization K V)
  proposal : Finset (Projectivization K V)
  targetOriginal : Finset (Projectivization K (Module.Dual K V))
  target : Finset (Projectivization K (Module.Dual K V))
  domain : Finset (Projectivization K (Module.Dual K V))
  overhead : ℝ
  source_nonempty : source.Nonempty
  source_original : source ⊆ S
  source_proposal : source ⊆ proposal
  target_nonempty : target.Nonempty
  target_original : target ⊆ targetOriginal
  target_domain : target ⊆ domain
  target_fraction : (targetOriginal.card : ℝ) ≤ 2 * target.card
  source_fraction : (S.card : ℝ) ≤ 2 * source.card
  proposal_ratio : (proposal.card : ℝ) ≤ exp overhead * source.card
  sparse : (incidenceCount S targetOriginal : ℝ) ≤
    (S.card : ℝ) * targetOriginal.card / (40000 * Nat.card K)

end
end SharpLogRamsey.ReadyTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotCalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ReadyTests
open Finset Real Incidence Validation Selection PivotGeometry GeometricCover ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

def firstCall (A U W : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (b : ℝ) (hB : B.Nonempty)
    (htrimB : (9/10:ℝ)*B.card ≤ (B∩UT).card)
    (hsource : ((A∩U)∩W).Nonempty)
    (hfrac : (A.card:ℝ) ≤ 2*((A∩U)∩W).card)
    (hratio : (W.card:ℝ) ≤ exp (b+log 1000000)*((A∩U)∩W).card)
    (hsparse : (incidenceCount A B:ℝ) ≤ (A.card:ℝ)*B.card/(40000*Nat.card K)) : Call A where
  source := (A∩U)∩W
  proposal := W
  targetOriginal := B
  target := B∩UT
  domain := UT
  overhead := b+log 1000000
  source_nonempty := hsource
  source_original := inter_subset_left.trans inter_subset_left
  source_proposal := inter_subset_right
  target_nonempty := by
    have hBpos : (0:ℝ)<B.card := by exact_mod_cast card_pos.mpr hB
    exact card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ)<(B∩UT).card))
  target_original := inter_subset_left
  target_domain := inter_subset_right
  target_fraction := by linarith
  source_fraction := hfrac
  proposal_ratio := hratio
  sparse := hsparse

variable [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def secondCall {n : ℕ} (hdim : Module.finrank K V=n+3)
    (A U W : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩UT).card)
    (b : ℝ) (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card)
    (hsparse : (incidenceCount A B:ℝ)≤(A.card:ℝ)*B.card/(40000*Nat.card K))
    {h m : ℕ} (table : PublicTables.Table (Fin h→Projectivization K V) m) (i : Fin m)
    (hi : PublicTables.firstIndex (implementAccept ((A∩U)∩W)
      (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K) UT (B∩UT)
        (2000*(Nat.card K:ℝ)^(n+3)/A.card))) m table=some i) : Call B := by
  let e := bidual (K:=K) (V:=V)
  let capB := cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT (PublicTables.rowAt m table i)
  let sourceB := (B∩UT)∩capB
  have hd := second_scheduled hdim A U W B UT hA hB htrimA htrimB b hprod hsparse table i hi
  dsimp only at hd
  have hAa : (A.image e).card=A.card := card_image_of_injective _ e.injective
  have hTa : ((A∩U).image e).card=(A∩U).card := card_image_of_injective _ e.injective
  refine {
    source := sourceB
    proposal := capB
    targetOriginal := A.image e
    target := (A∩U).image e
    domain := U.image e
    overhead := b+log 1000000
    source_nonempty := hd.1
    source_original := inter_subset_left.trans inter_subset_left
    source_proposal := inter_subset_right
    target_nonempty := ?_
    target_original := image_subset_image inter_subset_left
    target_domain := image_subset_image inter_subset_right
    target_fraction := ?_
    source_fraction := hd.2.1
    proposal_ratio := hd.2.2.1
    sparse := ?_ }
  · have hAp : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
    exact (card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ)<(A∩U).card))).image e
  · rw [hAa,hTa]
    linarith
  · rw [incidenceCount_bidual,hAa]
    convert hsparse using 1
    all_goals try with_reducible_and_instances rfl
    ring

end
end SharpLogRamsey.ReadyTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_ScheduledBanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ScheduledBanks
open Finset Real Validation PublicTables
open scoped Classical BigOperators
noncomputable section
variable (P Q : Type*) [Fintype P] [Fintype Q]

abbrev Address := {W : Finset P // W.Nonempty} × Finset Q × Fin (Fintype.card Q+1)

variable {P Q}
def length (q : ℝ) (a : Address P Q) : ℕ :=
  scheduleLength q a.2.1.card a.2.2.val

def cutoff (q b : ℝ) (a : Address P Q) : ℕ := scheduleCutoff q b (length q a)

abbrev At (q b : ℝ) (a : Address P Q) := Table (Fin (length q a) → P) (cutoff q b a)

abbrev Bank (q b : ℝ) := ∀ a : Address P Q, At q b a

def atLaw (q b : ℝ) (a : Address P Q) : Law (At q b a) where
  mass := tableWeight (rowLaw a.1.1 a.1.2 (length q a)) (cutoff q b a)
  nonneg := tableWeight_nonneg _ _
  total := tableWeight_total _ _

def bankLaw (q b : ℝ) : Law (Bank (P:=P) (Q:=Q) q b) := piLaw (atLaw q b)

end
end SharpLogRamsey.ScheduledBanks

namespace SharpLogRamsey.ReadyTests
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

def Call.address {S : Finset (Projectivization K V)} (c : Call S) :
    Address (Projectivization K V) (Projectivization K (Module.Dual K V)) :=
  ((⟨c.proposal, c.source_nonempty.mono c.source_proposal⟩), c.domain,
    ⟨c.target.card, Nat.lt_succ_of_le (card_le_univ _)⟩)

def Call.accept {S : Finset (Projectivization K V)} (c : Call S) (n : ℕ) :
    (Fin (length (Nat.card K) c.address) → Projectivization K V) → Prop :=
  implementAccept c.source
    (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K) c.domain c.target
      (2000*(Nat.card K:ℝ)^(n+3)/S.card))

def Call.bankRow {S : Finset (Projectivization K V)} (c : Call S)
    (b : ℝ) (n : ℕ)
    (z : Bank (P:=Projectivization K V) (Q:=Projectivization K (Module.Dual K V)) (Nat.card K) b) :
    Option (Fin (length (Nat.card K) c.address) → Projectivization K V) :=
  first (c.accept n) (cutoff (Nat.card K) b c.address) (z c.address)

def Call.bankIndex {S : Finset (Projectivization K V)} (c : Call S)
    (b : ℝ) (n : ℕ)
    (z : Bank (P:=Projectivization K V) (Q:=Projectivization K (Module.Dual K V)) (Nat.card K) b) :
    Option (Fin (cutoff (Nat.card K) b c.address)) :=
  firstIndex (c.accept n) (cutoff (Nat.card K) b c.address) (z c.address)

end
end SharpLogRamsey.ReadyTests

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_NullFreeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω : Type*} [Fintype Ω]

lemma Law.nullFree_sum (μ : Law Ω) (f : Ω→ℝ) :
    (∑ ω : {ω // μ.mass ω≠0},μ.mass ω*f ω) = ∑ ω,μ.mass ω*f ω := by
  calc
    _ = ∑ ω∈univ.filter (fun ω=>μ.mass ω≠0),μ.mass ω*f ω :=
      (sum_subtype _ (by simp) _).symm
    _ = _ := by
      apply sum_subset (filter_subset _ _)
      intro ω hω hn
      have hh : μ.mass ω=0 := by simpa using hn
      simp [hh]

def Law.nullFree (μ : Law Ω) : Law {ω // μ.mass ω≠0} where
  mass ω := μ.mass ω
  nonneg ω := μ.nonneg ω
  total := by simpa only [mul_one,μ.total] using μ.nullFree_sum (fun _=>1)

lemma Law.nullFree_integral (μ : Law Ω) (f : Ω→ℝ) :
    (∑ ω,μ.nullFree.mass ω*f ω)=∑ ω,μ.mass ω*f ω := μ.nullFree_sum f

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_HistoryLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]

def Law.sigma (μ : Law Θ) {A : Θ→Type*} [∀ z,Fintype (A z)]
    (ρ : ∀ z,Law (A z)) : Law (Sigma A) where
  mass x := μ.mass x.1*(ρ x.1).mass x.2
  nonneg x := mul_nonneg (μ.nonneg x.1) ((ρ x.1).nonneg x.2)
  total := by
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ z,μ.mass z := by
        apply sum_congr rfl
        intro z _
        change (∑ y,μ.mass z*(ρ z).mass y)=μ.mass z
        rw [←mul_sum,(ρ z).total,mul_one]
      _ = 1 := μ.total

lemma Law.sigma_sum (μ : Law Θ) {A : Θ→Type*} [∀ z,Fintype (A z)]
    (ρ : ∀ z,Law (A z)) (f : Sigma A→ℝ) :
    (∑ x,(μ.sigma ρ).mass x*f x)=∑ z,μ.mass z*∑ a,(ρ z).mass a*f ⟨z,a⟩ := by
  simp only [Law.sigma,Fintype.sum_sigma,mul_sum,mul_assoc]

lemma Law.history_sum (μ : Law Ω) (θ : Ω→Θ) (f : Ω→ℝ) :
    (∑ z,(μ.map θ).mass z*∑ ω,(μ.cond θ z).mass ω*f ω)=∑ ω,μ.mass ω*f ω := by
  have h:=μ.history_observable_sum θ id (fun _ ω=>f ω)
  simpa only [Law.sum_map,id_eq] using h.symm

lemma Law.nullFree_map {B : Type*} [Fintype B] (μ : Law Ω) (f : Ω→B) :
    μ.nullFree.map (fun ω=>f ω.val)=μ.map f := by
  ext b
  change (∑ ω : {ω // μ.mass ω≠0} with f ω.val=b,μ.mass ω.val)=∑ ω with f ω=b,μ.mass ω
  simpa only [sum_filter,mul_ite,mul_one,mul_zero,Law.nullFree] using
    μ.nullFree_integral (fun ω=>if f ω=b then 1 else 0)

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_ExposureModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section

variable {β C ι : Type} [Fintype β] [Fintype C] [Fintype ι] [DecidableEq ι]

structure ExposureModel (ι β C : Type) [Fintype β] where
  History : Type
  [finiteHistory : Fintype History]
  historyLaw : @Law History finiteHistory
  Index : History→Type
  [finiteIndex : ∀ z,Fintype (Index z)]
  [decIndex : ∀ z,DecidableEq (Index z)]
  tupleLaw : ∀ z,Law (Index z→β)
  remaining : History→ℕ
  embedding : ∀ z,C×Fin (remaining z) ↪ Index z
  owner : ∀ z,Index z→Option C
  origin : ∀ z,Index z↪ι
  restore : ∀ z,(Index z→β)→ι→β
  restore_origin : ∀ z x i,restore z x (origin z i)=x i

attribute [instance] ExposureModel.finiteHistory ExposureModel.finiteIndex ExposureModel.decIndex

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_SourceCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {X Ω B : Type*} [Fintype X] [Fintype Ω] [Fintype B]

def Law.attach (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B) : Law (Σ _x : X,Ω) :=
  q.sigma (fun x=>μ.cond g (f x))

theorem Law.attach_source (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B)
    (h : q.map f=μ.map g) (φ : Ω→ℝ) :
    (∑ x,(q.attach μ f g).mass x*φ x.2)=∑ ω,μ.mass ω*φ ω := by
  rw [Law.attach,Law.sigma_sum]
  change (∑ x,q.mass x*(fun b=>∑ ω,(μ.cond g b).mass ω*φ ω) (f x))=_
  rw [←q.sum_map f (fun b=>∑ ω,(μ.cond g b).mass ω*φ ω),h]
  exact μ.history_sum g φ

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_ChronologicalTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ChronologicalTree

open BinaryTree

def balanced (lo n : ℕ) : BinaryTree ℕ :=
  if h : n = 0 then .nil else
    .node (lo+n/2) (balanced lo (n/2))
      (balanced (lo+n/2+1) (n-n/2-1))
termination_by n
decreasing_by
  · exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
  · omega

def inorder {α : Type*} : BinaryTree α → List α
  | .nil => []
  | .node a l r => inorder l ++ a :: inorder r

@[simp] lemma inorder_length {α : Type*} (t : BinaryTree α) :
    (inorder t).length=t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [inorder,hl,hr]; omega

end SharpLogRamsey.ChronologicalTree

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_FreshExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I]
variable {α : I→Type*}

def arrive (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) (target : I) :
    BinaryTree I→Domains A B→Option (Domains A B)
  | .nil,_=>none
  | .node i l r,U=>if i=target then some U else
      match choose i (z i) U with
      | none=>none
      | some c=>
        let V:=read i (z i) U c
        (arrive choose read z target l (V.1,U.2)).orElse
          (fun _=>arrive choose read z target r (U.1,V.2))

def outsideState (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I) (dummy : α target)
    (t : BinaryTree I) (U : Domains A B) (s : Outside (α:=α) target) :
    Option (Domains A B) :=
  arrive choose read ((Equiv.piSplitAt target α).symm (dummy,s)) target t U

def produced (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I)
    (f : Domains A B→α target→ℝ) (t : BinaryTree I) (U : Domains A B)
    (z : ∀ i,α i) : ℝ :=
  match arrive choose read z target t U with
  | none=>0
  | some V=>f V (z target)

variable [Fintype I] [∀ i,Fintype (α i)]

def fixedRead (read : ∀ i,α i→CapReader A B C) (z : ∀ i,α i) :
    CapReader A B (I×C) := fun U c=>read c.1 (z c.1) U c.2

def fixedChoose (choose : ∀ i,α i→Domains A B→Option C) (z : ∀ i,α i) :
    I→Domains A B→Option (I×C) := fun i U=>(choose i (z i) U).map (fun c=>(i,c))

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_FreshAccrual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables ChronologicalTree
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def labels (t : BinaryTree I) : Finset I := (inorder t).toFinset

@[simp] lemma labels_nil : labels (.nil : BinaryTree I)=∅ := rfl

@[simp] lemma labels_node (i : I) (l r : BinaryTree I) :
    labels (.node i l r)=insert i (labels l∪labels r) := by
  ext j
  simp only [labels,inorder,List.mem_toFinset,List.mem_append,List.mem_cons,
    mem_insert,mem_union]
  tauto

def Separated : BinaryTree I→Prop
  | .nil=>True
  | .node i l r=>Separated l ∧ Separated r ∧ i∉labels l ∧ i∉labels r ∧
      Disjoint (labels l) (labels r)

def accrued (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (f : ∀ i,Domains A B→α i→ℝ)
    (z : ∀ i,α i) : BinaryTree I→Domains A B→ℝ
  | .nil,_=>0
  | .node i l r,U=>f i U (z i)+match choose i (z i) U with
    | none=>0
    | some c=>
      let V:=read i (z i) U c
      accrued choose read f z l (V.1,U.2)+accrued choose read f z r (U.1,V.2)

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def leftPath (target : I) : BinaryTree I→Finset I
  | .nil=>∅
  | .node i l r=>if i=target then ∅ else
      if target∈labels l then insert i (leftPath target l) else leftPath target r

def firstLoss (choose : ∀ i,α i→Domains A B→Option C)
    (mask : ∀ i,α i→CapReader A B C) (Y : Finset A)
    (i : I) (U : Domains A B) (x : α i) : ℝ :=
  match choose i x U with
  | none=>0
  | some c=>((Y\(mask i x U c).1).card:ℝ)

variable [Fintype I] [∀ i,Fintype (α i)]

def firstTrim (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (Y : Finset A)
    (target : I) (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) : Prop :=
  ∃ V,arrive choose read z target t U=some V ∧
    ((Y∩V.1).card:ℝ)<(9/10:ℝ)*Y.card

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def plannedPath (target : I) : BinaryTree I→Finset I
  | .nil=>∅
  | .node i l r=>if i=target then {i} else
      insert i (if target∈labels l then plannedPath target l else plannedPath target r)

def trialFailure (choose : ∀ i,α i→Domains A B→Option C)
    (i : I) (V : Domains A B) (x : α i) : ℝ := if choose i x V=none then 1 else 0

def pivotSuccess (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (target : I)
    (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) : ℝ :=
  produced choose read target (fun V x=>1-trialFailure choose target V x) t U z

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedSecondTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def rightPath (target : I) : BinaryTree I→Finset I
  | .nil=>∅
  | .node i l r=>if i=target then ∅ else
      if target∈labels r then insert i (rightPath target r) else rightPath target l

def secondLoss (choose : ∀ i,α i→Domains A B→Option C)
    (mask : ∀ i,α i→CapReader A B C) (Y : Finset B)
    (i : I) (U : Domains A B) (x : α i) : ℝ :=
  match choose i x U with
  | none=>0
  | some c=>((Y\(mask i x U c).2).card:ℝ)

variable [Fintype I] [∀ i,Fintype (α i)]

def secondTrim (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (Y : Finset B)
    (target : I) (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) : Prop :=
  ∃ V,arrive choose read z target t U=some V ∧
    ((Y∩V.2).card:ℝ)<(9/10:ℝ)*Y.card

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def targetFailure (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (a : A) (b : B) (i : I)
    (t : BinaryTree I) (U : Domains A B) (z : ∀ i,α i) : ℝ :=
  match arrive choose read z i t U with
  | none=>1
  | some V=>match choose i (z i) V with
    | none=>1
    | some c=>if a∈(read i (z i) V c).1 ∧ b∈(read i (z i) V c).2 then 0 else 1

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def compatible (R : A→B→Prop) (U : Domains A B) (xs : List (A×B)) : ℝ :=
  (xs.filter (fun z=>z∈flagDomain R U)).length

def fullOutput (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) : List (A×B) :=
  output R (fixedRead read z) targets (fun i=>(targets i).length)
    (execute (fixedRead read z) (fixedChoose choose z) t U) U

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedOutputCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C : Type*} [DecidableEq I] {α : I→Type*}

def keptCount (R : A→B→Prop) (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (i : I) (U : Domains A B) (x : α i) : ℝ :=
  match choose i x U with
  | none=>0
  | some c=>compatible R (read i x U c) (targets i)

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] {α : I→Type*}

def fullMessage (R : A→B→Prop)
    (choose : ∀ i,α i→Domains A B→Option C)
    (read : ∀ i,α i→CapReader A B C) (targets : I→List (A×B))
    (z : ∀ i,α i) (t : BinaryTree I) (U : Domains A B) : BinaryTree ((I×C)×ℕ) :=
  message R (fixedRead read z) targets (fun i=>(targets i).length)
    (execute (fixedRead read z) (fixedChoose choose z) t U) U

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedLawExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] [Fintype I] [Fintype Ω]
  {α : I→Type*} [∀ i,Fintype (α i)]

def sourcePublicLaw (μ : Law Ω) (p : ∀ i,Law (α i)) : Law (Ω×(∀ i,α i)) where
  mass x := μ.mass x.1*(piLaw p).mass x.2
  nonneg x := mul_nonneg (μ.nonneg x.1) ((piLaw p).nonneg x.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [←mul_sum,(piLaw p).total,mul_one,μ.total]

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B I C : Type*}

def potential (Q : ℝ) (U : Domains A B) : ℝ :=
  max (log ((U.1.card:ℝ)*U.2.card/Q)) 0

def annotate (read : CapReader A B C) (choose : I→Domains A B→Option C) :
    BinaryTree I→Domains A B→BinaryTree (I×Domains A B×C)
  | .nil,_ => .nil
  | .node i l r,U => match choose i U with
    | none => .nil
    | some c =>
      let V := read U c
      .node (i,U,c) (annotate read choose l (V.1,U.2))
        (annotate read choose r (U.1,V.2))

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B C I Ω : Type*}

def codeTree (read : CapReader A B C) (choose : I→Domains A B→Option C)
    (t : BinaryTree I) (U : Domains A B) : BinaryTree C :=
  (execute read choose t U).map Prod.snd

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedFullMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ExecutedPotential
open Finset Real BinaryTree TreeDecoder
open scoped Classical
noncomputable section
variable {A B C I Ω : Type*}

def countReader (read : CapReader A B C) : CapReader A B (C×ℕ) :=
  fun U x=>read U x.1

def countChoose (R : A→B→Prop) (read : CapReader A B C)
    (choose : I→Domains A B→Option C) (targets : I→List (A×B)) (counts : I→ℕ) :
    I→Domains A B→Option (C×ℕ) := fun i U=>
      (choose i U).map (fun c=>(c,(retained R (read U c) (targets i) (counts i)).length))

def countAlphabet (allowed : Domains A B→Finset C) (n : ℕ) (U : Domains A B) : Finset (C×ℕ) :=
  allowed U ×ˢ range (n+1)

end
end SharpLogRamsey.ExecutedPotential

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PivotGeometry
open Finset Real Incidence Validation ProjectiveDuality PublicTables TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def primalCap {h : ℕ} (U : Finset (Projectivization K V))
    (u : Fin h→Projectivization K (Module.Dual K V)) : Finset (Projectivization K V) :=
  U.filter (fun x => pass SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) u (bidual x))

end
end SharpLogRamsey.PivotGeometry

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotBanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables
  ReadyTests PivotGeometry ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

structure Input (n : ℕ) (A : Finset (Projectivization K V))
    (B : Finset (Projectivization K (Module.Dual K V))) (b : ℝ) where
  U : Finset (Projectivization K V)
  UT : Finset (Projectivization K (Module.Dual K V))
  W : Finset (Projectivization K V)
  nonemptyA : A.Nonempty
  nonemptyB : B.Nonempty
  trimA : (9/10:ℝ)*A.card ≤ (A∩U).card
  trimB : (9/10:ℝ)*B.card ≤ (B∩UT).card
  source_nonempty : ((A∩U)∩W).Nonempty
  source_fraction : (A.card:ℝ) ≤ 2*((A∩U)∩W).card
  proposal_ratio : (W.card:ℝ) ≤ exp (b+log 1000000)*((A∩U)∩W).card
  product : (Nat.card K:ℝ)^(n+3)*exp (-b) ≤ (A.card:ℝ)*B.card
  sparse : (incidenceCount A B:ℝ) ≤ (A.card:ℝ)*B.card/(40000*Nat.card K)

variable {n : ℕ} {A : Finset (Projectivization K V)}
  {B : Finset (Projectivization K (Module.Dual K V))} {b : ℝ}

def Input.firstCall (d : Input n A B b) : Call A :=
  ReadyTests.firstCall A d.U d.W B d.UT b d.nonemptyB d.trimB
    d.source_nonempty d.source_fraction d.proposal_ratio d.sparse

abbrev FirstBank (b : ℝ) := Bank (P:=Projectivization K V)
  (Q:=Projectivization K (Module.Dual K V)) (Nat.card K) (b+log 1000000)
abbrev SecondBank (b : ℝ) := Bank (P:=Projectivization K (Module.Dual K V))
  (Q:=Projectivization K (Module.Dual K (Module.Dual K V))) (Nat.card K) (b+log 1000000)

abbrev Input.FirstRow (d : Input n A B b) :=
  Fin (length (Nat.card K) d.firstCall.address) → Projectivization K V

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma Input.first_valid (d : Input n A B b) (z : FirstBank (K:=K) (V:=V) b)
    (r : d.FirstRow) (hr : d.firstCall.bankRow (b+log 1000000) n z=some r) :
    d.firstCall.accept n r := by
  exact PublicTables.first_valid _ _ _ _ hr

def Input.secondCall (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (r : d.FirstRow) (hr : d.firstCall.accept n r) : Call B := by
  have hi : firstIndex (d.firstCall.accept n) 1 (r,PUnit.unit)=some 0 := by
    simp only [firstIndex, ite_eq_left hr]
  exact ReadyTests.secondCall hdim A d.U d.W B d.UT d.nonemptyA d.nonemptyB
    d.trimA d.trimB b d.product d.sparse
    (h:=length (Nat.card K) d.firstCall.address) (m:=1) (r,PUnit.unit) 0 hi

def Input.next (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) : Option (Call B) :=
  match hr : d.firstCall.bankRow (b+log 1000000) n z with
  | none => none
  | some r => some (d.secondCall hdim r (d.first_valid z r hr))

def Input.failure (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) : ℝ :=
  (d.next hdim z).elim 1 (fun c => if c.bankRow (b+log 1000000) n w=none then 1 else 0)

def Input.secondLoss (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (y : Projectivization K (Module.Dual K (Module.Dual K V)))
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) : ℝ :=
  (d.next hdim z).elim 0 (fun c => (c.bankRow (b+log 1000000) n w).elim 0
    (fun r => if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K) r y then 1 else 0))

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables
  ReadyTests PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

abbrev FirstCode (b : ℝ) := Σ a : Address (Projectivization K V)
  (Projectivization K (Module.Dual K V)), Fin (cutoff (Nat.card K) (b+log 1000000) a)
abbrev SecondCode (b : ℝ) := Σ a : Address (Projectivization K (Module.Dual K V))
  (Projectivization K (Module.Dual K (Module.Dual K V))),
  Fin (cutoff (Nat.card K) (b+log 1000000) a)
abbrev Code (b : ℝ) := FirstCode (K:=K) (V:=V) b × SecondCode (K:=K) (V:=V) b

def read (b : ℝ) (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) :
    CapReader (Projectivization K V) (Projectivization K (Module.Dual K V)) (Code (K:=K) (V:=V) b) :=
  fun U c => (primalCap U.1 (rowAt _ (w c.2.1) c.2.2),
    cap SharpLogRamsey.Incidence.Incident (Nat.card K) U.2 (rowAt _ (z c.1.1) c.1.2))

variable {n : ℕ} {A : Finset (Projectivization K V)}
  {B : Finset (Projectivization K (Module.Dual K V))} {b : ℝ}

def Input.choose (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) : Option (Code (K:=K) (V:=V) b) :=
  match hi : d.firstCall.bankIndex (b+log 1000000) n z with
  | none => none
  | some i =>
    let r := rowAt _ (z d.firstCall.address) i
    let c := d.secondCall hdim r (index_valid _ _ _ i hi)
    (c.bankIndex (b+log 1000000) n w).map (fun j => (⟨d.firstCall.address,i⟩,⟨c.address,j⟩))

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotLosses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables
  ReadyTests PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def mask (b : ℝ) (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) :
    CapReader (Projectivization K V) (Projectivization K (Module.Dual K V))
      (Code (K:=K) (V:=V) b) := fun _ c=>read b z w (univ,univ) c

variable {n : ℕ} {A : Finset (Projectivization K V)}
  {B : Finset (Projectivization K (Module.Dual K V))} {b : ℝ}

def Input.dualLoss (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (y : Projectivization K (Module.Dual K V))
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) : ℝ :=
  (d.choose hdim z w).elim 0 (fun c=>if y∉(mask b z w (d.U,d.UT) c).2 then 1 else 0)

def Input.primalLoss (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (x : Projectivization K V)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) : ℝ :=
  (d.choose hdim z w).elim 0 (fun c=>if x∉(mask b z w (d.U,d.UT) c).1 then 1 else 0)

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_Pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence GeometricCover PivotGeometry TreeDecoder SourceScales Filter
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def Header (q b : ℝ) (r : ℕ)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (s t : ℕ) : Prop :=
  0 < s ∧ 0<t ∧ s≤U.1.card ∧ t≤U.2.card ∧
    q^r*exp (-(b+log 4))≤(s:ℝ)*t ∧ (s:ℝ)*t≤2*q^r

structure Book (q b τ P H : ℝ) (r : ℕ) where
  library : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)) →
    ℕ → ℕ → Finset (Finset (Projectivization K V))
  valid : ∀ U s t,Header q b r U s t →
    (∀ W∈library U s t,W⊆U.1 ∧ (W.card:ℝ)≤100000*q^r/t) ∧
    (∀ S T,S⊆U.1 → S.card=s → T⊆U.2 → T.card=t →
      (incidenceCount S T:ℝ)≤(4*τ)*(s:ℝ)*t/q →
      ∃ W∈library U s t,(99/100:ℝ)*s≤(S∩W).card) ∧
    log (((library U s t).card:ℝ)+1)≤
      H*q*P*(log ((U.1.card:ℝ)/s)+log ((U.2.card:ℝ)/t)+P)
  invalid : ∀ U s t,¬Header q b r U s t → library U s t=∅

def Book.ofValidated (q b τ P H : ℝ) (r : ℕ)
    (hv : ∀ U s t,Header (K:=K) (V:=V) q b r U s t →
      Validated q P H r U.1 U.2 s t (4*τ)) : Book (K:=K) (V:=V) q b τ P H r where
  library U s t := if hh : Header q b r U s t then (hv U s t hh).choose else ∅
  valid U s t hh := by
    simp only [dite_eq_left hh]
    exact (hv U s t hh).choose_spec
  invalid U s t hh := dite_eq_right hh

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma trimmed_header {n : ℕ} (hdim : Module.finrank K V=n+3)
    (A : Finset (Projectivization K V)) (B : Finset (Projectivization K (Module.Dual K V)))
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (b τ : ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hτ : 0≤τ)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U.1).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩U.2).card)
    (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card)
    (hsp : (incidenceCount A B:ℝ)≤τ*(A.card:ℝ)*B.card/Nat.card K)
    (hsparse : (incidenceCount A B:ℝ)≤(A.card:ℝ)*B.card/(40000*Nat.card K)) :
    Header (Nat.card K) b (n+3) U (A∩U.1).card (B∩U.2).card := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
  have ha : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
  have hb : (0:ℝ)<B.card := by exact_mod_cast card_pos.mpr hB
  refine ⟨by exact_mod_cast (by linarith : (0:ℝ)<(A∩U.1).card),
    by exact_mod_cast (by linarith : (0:ℝ)<(B∩U.2).card),
    card_le_card inter_subset_right,card_le_card inter_subset_right,?_,?_⟩
  · exact (trimmed_inputs A U.1 B U.2 (Nat.card K) ((Nat.card K:ℝ)^(n+3)) τ b
      hq hτ (by linarith) (by linarith) hprod hsp).1
  · apply le_trans _ (sparse_product_bound_two hdim A B (hsparse.trans ?_))
    · exact mul_le_mul (by exact_mod_cast card_le_card (inter_subset_left (s₁:=A) (s₂:=U.1)))
        (by exact_mod_cast card_le_card (inter_subset_left (s₁:=B) (s₂:=U.2)))
        (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem Book.input {n : ℕ} (hdim : Module.finrank K V=n+3) {b τ P H : ℝ}
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
    (A : Finset (Projectivization K V)) (B : Finset (Projectivization K (Module.Dual K V)))
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hτ : 0≤τ)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U.1).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩U.2).card)
    (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card)
    (hsp : (incidenceCount A B:ℝ)≤τ*(A.card:ℝ)*B.card/Nat.card K)
    (hsparse : (incidenceCount A B:ℝ)≤(A.card:ℝ)*B.card/(40000*Nat.card K)) :
    ∃ d : Input n A B b,(d.U,d.UT)=U ∧ d.W∈book.library U (A∩U.1).card (B∩U.2).card ∧ d.W⊆U.1 := by
  have hh := trimmed_header hdim A B U b τ hA hB hτ htrimA htrimB hprod hsp hsparse
  obtain ⟨hF,hc,_⟩ := book.valid U _ _ hh
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
  obtain ⟨W,hW,hWU,hn,hfrac,hratio⟩ := first_source A U.1 B U.2 (Nat.card K) τ b (n+3)
    hA hB hq hτ htrimA htrimB hprod hsp (book.library U _ _) hF hc
  exact ⟨⟨U.1,U.2,W,hA,hB,htrimA,htrimB,hn,hfrac,hratio,hprod,hsparse⟩,rfl,hW,hWU⟩

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

structure Original (n : ℕ) (b : ℝ) where
  A : Finset (Projectivization K V)
  B : Finset (Projectivization K (Module.Dual K V))
  nonemptyA : A.Nonempty
  nonemptyB : B.Nonempty
  product : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card

abbrev Banks (b : ℝ) := FirstBank (K:=K) (V:=V) b × SecondBank (K:=K) (V:=V) b

def banksLaw (b : ℝ) : PublicTables.Law (Banks (K:=K) (V:=V) b) where
  mass x := (bankLaw (Nat.card K) (b+log 1000000)).mass x.1 *
    (bankLaw (Nat.card K) (b+log 1000000)).mass x.2
  nonneg x := mul_nonneg ((bankLaw _ _).nonneg x.1) ((bankLaw _ _).nonneg x.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [←mul_sum,PublicTables.Law.total,mul_one]

variable {n : ℕ} {b τ P H : ℝ}

def Original.Ready (s : Original (K:=K) (V:=V) n b) (τ : ℝ)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) : Prop :=
  (9/10:ℝ)*s.A.card≤(s.A∩U.1).card ∧ (9/10:ℝ)*s.B.card≤(s.B∩U.2).card ∧
    (incidenceCount s.A s.B:ℝ)≤τ*(s.A.card:ℝ)*s.B.card/Nat.card K

variable (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3)) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

omit [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma Original.sparse (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (hr : s.Ready τ U) (hτsmall : τ≤1/40000) :
    (incidenceCount s.A s.B:ℝ)≤(s.A.card:ℝ)*s.B.card/(40000*Nat.card K) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
  apply hr.2.2.trans
  have h := mul_le_mul_of_nonneg_right hτsmall (show 0≤(s.A.card:ℝ)*s.B.card/Nat.card K by positivity)
  convert h using 1 <;> ring

def Book.prepare (s : Original (K:=K) (V:=V) n b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (hr : s.Ready τ U) :
    Input n s.A s.B b :=
  (book.input hdim s.A s.B U s.nonemptyA s.nonemptyB hτ hr.1 hr.2.1 s.product hr.2.2
    (s.sparse U hr hτsmall)).choose

def Book.choose (s : Original (K:=K) (V:=V) n b)
    (z : Banks (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) :
    Option (Code (K:=K) (V:=V) b) :=
  if hr : s.Ready τ U then (book.prepare hdim hτ hτsmall s U hr).choose hdim z.1 z.2 else none

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_ChronologicalExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder FreshExecution SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

abbrev ChronoDomains := Domains (Projectivization K (Module.Dual K V)) (Projectivization K V)

def chronoRead (b : ℝ) (z : Banks (K:=K) (V:=V) b) :
    CapReader (Projectivization K (Module.Dual K V)) (Projectivization K V) (Code (K:=K) (V:=V) b) :=
  fun U c=>(read b z.1 z.2 U.swap c).swap

def chronoMask (b : ℝ) (z : Banks (K:=K) (V:=V) b) :
    CapReader (Projectivization K (Module.Dual K V)) (Projectivization K V) (Code (K:=K) (V:=V) b) :=
  fun U c=>(mask b z.1 z.2 U.swap c).swap

variable {n : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=n+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3)) (hτ : 0≤τ) (hτsmall : τ≤1/40000)

def Book.chronoChoose (s : Original (K:=K) (V:=V) n b)
    (z : Banks (K:=K) (V:=V) b) (U : ChronoDomains (K:=K) (V:=V)) :
    Option (Code (K:=K) (V:=V) b) := book.choose hdim hτ hτsmall s z U.swap

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

abbrev FirstSize := Fin (Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V)))+1)
abbrev SecondSize := Fin (Fintype.card (Projectivization K (Module.Dual K V))+1)

def firstBound (b : ℝ)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (t : ℕ) : ℕ :=
  scheduleCutoff (Nat.card K) (b+log 1000000) (scheduleLength (Nat.card K) U.2.card t)

def secondBound (b : ℝ)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) (s : ℕ) : ℕ :=
  scheduleCutoff (Nat.card K) (b+log 1000000)
    (scheduleLength (Nat.card K) (U.1.image (bidual (K:=K) (V:=V))).card s)

variable {n : ℕ} {b τ P H : ℝ}
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))

abbrev Book.LocalRaw
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) :=
  Σ s : FirstSize (K:=K) (V:=V), Σ t : SecondSize (K:=K) (V:=V),
    (book.library U s t) × Fin (firstBound b U t) × Fin (secondBound b U s)

def Book.decodeRaw (z : FirstBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (v : book.LocalRaw U) : Option (Code (K:=K) (V:=V) b) :=
  if hW : v.2.2.1.val.Nonempty then
    let a : Address (Projectivization K V) (Projectivization K (Module.Dual K V)) :=
      (⟨v.2.2.1.val,hW⟩,U.2,v.2.1)
    let i : Fin (cutoff (Nat.card K) (b+log 1000000) a) := v.2.2.2.1
    let B := cap SharpLogRamsey.Incidence.Incident (Nat.card K) U.2 (rowAt _ (z a) i)
    if hB : B.Nonempty then
      let a' : Address (Projectivization K (Module.Dual K V))
          (Projectivization K (Module.Dual K (Module.Dual K V))) :=
        (⟨B,hB⟩,U.1.image (bidual (K:=K) (V:=V)),v.1)
      let j : Fin (cutoff (Nat.card K) (b+log 1000000) a') := v.2.2.2.2
      some (⟨a,i⟩,⟨a',j⟩)
    else none
  else none

def Book.allowed (z : FirstBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V))) :
    Finset (Code (K:=K) (V:=V) b) :=
  univ.biUnion (fun v : book.LocalRaw U=>(book.decodeRaw z U v).toFinset)

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_PivotAlphabetCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {n : ℕ} {b τ P H : ℝ}

def headerCost : ℝ :=
  log ((Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))):ℝ)+1)+
  log ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1)

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_ReciprocalEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder FreshExecution ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [Fintype Ω]
  {n : ℕ} {b τ P H : ℝ}

def Book.publicAlphabet (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
    (z : I→Banks (K:=K) (V:=V) b) (U : ChronoDomains (K:=K) (V:=V)) :
    Finset (I×Code (K:=K) (V:=V) b) :=
  univ.biUnion (fun i=>(book.allowed (z i).1 U.swap).image (fun c=>(i,c)))

variable (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))

variable (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
include hb hH hP haP

local instance publicCodeDecidableEq : DecidableEq (I×Code (K:=K) (V:=V) b) := Classical.decEq _

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.ActualPivot
open Finset Real TreeDecoder FreshExecution BinaryTree ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω Ξ : Type*} [Fintype I] [Fintype Ω]
  {n : ℕ} {b τ P H : ℝ}
local instance flat_ActualExecutedReplacement_1 : DecidableEq I := Classical.decEq _
local instance replacementBanksFintype : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

abbrev Flag := Projectivization K (Module.Dual K V)×Projectivization K V

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_ReciprocalScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Real Filter
open scoped Topology
noncomputable section

def treeError (q τ h ε εA εB δA δB : ℝ) : ℝ :=
  20*(12*q*((4*exp 1)*(4*exp 1)*ε))*h^2+
    (q*((4*exp 1)*(4*exp 1)*ε)/τ+2*exp (-q))*h+
    δA+δB+(h+1)*(12*q*((4*exp 1)*εA)+12*q*((4*exp 1)*εB))

def treeErrorEnvelope (β C x : ℝ) : ℝ :=
  240*(4*exp 1)^2*C*x^(-1998*β)+
  (4*exp 1)^2*C*x^(-1899*β)+
  2*(x^β*exp (-x))+2*C*x^(-2*β)+48*(4*exp 1)*C*x^(-1999*β)

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedGoodTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] {α : I→Type*}

def goodSingleton (good : Prop) (a : A) : Finset A := if good then {a} else ∅

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ExecutedFailureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.FreshExecution
open Finset BinaryTree TreeDecoder PublicTables
open scoped Classical BigOperators
noncomputable section
variable {I A B C Ω : Type*} [DecidableEq I] {α : I→Type*}

def readyFailure (choose : ∀ i,α i→Domains A B→Option C)
    (S : Finset A) (T : Finset B) (bad : Prop)
    (i : I) (V : Domains A B) (x : α i) : ℝ :=
  if ¬((S∩V.1).card:ℝ)<(9/10:ℝ)*S.card ∧
      ¬((T∩V.2).card:ℝ)<(9/10:ℝ)*T.card ∧ ¬bad
    then trialFailure choose i V x else 0

end
end SharpLogRamsey.FreshExecution

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_OriginalTreeLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence PublicTables FreshExecution TreeDecoder SupportMixtures BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

local instance banksFintype (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

def density (S : Finset (Projectivization K (Module.Dual K V)))
    (T : Finset (Projectivization K V)) : ℝ :=
  pairing (kernel S) (kernel T) (fun y x=>if y.rep x.rep=0 then 1 else 0)

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_OriginalTargetLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence PublicTables FreshExecution TreeDecoder SupportMixtures BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

local instance targetBanksFintype (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

def firstTargetDensity (good : Prop) (y : Projectivization K (Module.Dual K V))
    (T : Finset (Projectivization K V)) : ℝ :=
  if good then ∑ x,kernel T x*(if y.rep x.rep=0 then 1 else 0) else 0

def secondTargetDensity (good : Prop) (x : Projectivization K V)
    (S : Finset (Projectivization K (Module.Dual K V))) : ℝ :=
  if good then ∑ y,kernel S y*(if y.rep x.rep=0 then 1 else 0) else 0

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_OriginalFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence SupportMixtures Selection Selection.AuxiliarySupport
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I : Type*} [Fintype I]
  {p : I→Law (Projectivization K (Module.Dual K V))}
  {r : I→Law (Projectivization K V)}
  {goodA : I→Finset (Projectivization K (Module.Dual K V))}
  {goodB : I→Finset (Projectivization K V)} {MA MB κA κB : I→ℝ}

variable (X : ∀ i,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
  (Y : ∀ i,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))

abbrev OriginalChoice := {z // (familyLaw X Y).mass z≠0}

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma originalChoice_size (z : OriginalChoice X Y) (i : I) :
    MA i*exp (-κA i)/2≤((z.val.1 i).card:ℝ) ∧
    MB i*exp (-κB i)/2≤((z.val.2 i).card:ℝ) :=
  ⟨((familyLaw_support X Y z.val z.property).1 i).2.1,
   ((familyLaw_support X Y z.val z.property).2 i).2.1⟩

def originalFamily {n : ℕ} {b : ℝ} (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
    (hprod : ∀ i,(Nat.card K:ℝ)^(n+3)*exp (-b)≤
      (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))
    (z : OriginalChoice X Y) (i : I) : Original (K:=K) (V:=V) n b where
  A := z.val.2 i
  B := z.val.1 i
  nonemptyA := by
    apply card_pos.mp
    exact_mod_cast lt_of_lt_of_le (div_pos (mul_pos (hMB i) (exp_pos _)) (by norm_num) : 0<MB i*exp (-κB i)/2)
      (originalChoice_size X Y z i).2
  nonemptyB := by
    apply card_pos.mp
    exact_mod_cast lt_of_lt_of_le (div_pos (mul_pos (hMA i) (exp_pos _)) (by norm_num) : 0<MA i*exp (-κA i)/2)
      (originalChoice_size X Y z i).1
  product := by
    apply (hprod i).trans
    rw [mul_comm ((z.val.2 i).card:ℝ)]
    exact mul_le_mul (originalChoice_size X Y z i).1 (originalChoice_size X Y z i).2
      (div_nonneg (mul_nonneg (hMB i).le (exp_pos _).le) (by norm_num)) (by positivity)

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence SupportMixtures Selection Selection.AuxiliarySupport
open FreshExecution TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [Fintype Ω]
  {p : I→Law (Projectivization K (Module.Dual K V))}
  {r : I→Law (Projectivization K V)}
  {goodA : I→Finset (Projectivization K (Module.Dual K V))}
  {goodB : I→Finset (Projectivization K V)} {MA MB κA κB : I→ℝ}

local instance reciprocalBanksFintype (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

def goodIncidence (p : Law (Projectivization K (Module.Dual K V)))
    (r : Law (Projectivization K V))
    (A : Finset (Projectivization K (Module.Dual K V))) (B : Finset (Projectivization K V)) : ℝ :=
  (p.prod r).event (univ.filter (fun ay=>ay.1∈A ∧ ay.2∈B ∧ ay.1.rep ay.2.rep=0))

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalPopulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence SupportMixtures Selection Selection.AuxiliarySupport
open FreshExecution TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [Fintype Ω]
  {p : I→Law (Projectivization K (Module.Dual K V))}
  {r : I→Law (Projectivization K V)}
  {goodA : I→Finset (Projectivization K (Module.Dual K V))}
  {goodB : I→Finset (Projectivization K V)} {MA MB κA κB : I→ℝ}
local instance flat_ActualReciprocalPopulation_1 : DecidableEq I := Classical.decEq _
local instance populationBanksFintype (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_EmptySupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card_lower {d : ℕ} (hdim : Module.finrank K V=d+1) :
    (Nat.card K:ℝ)^d≤Fintype.card (Projectivization K V) := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
  push_cast
  exact single_le_sum (fun i hi=>pow_nonneg (Nat.cast_nonneg _) _) (mem_range.mpr (by omega))

def emptyOriginal {n : ℕ} {b : ℝ} (hdim : Module.finrank K V=n+3) (hb : 0≤b) :
    Original (K:=K) (V:=V) n b where
  A := univ
  B := univ
  nonemptyA := by
    have h:=projective_card_lower (show Module.finrank K V=(n+2)+1 by omega)
    have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
    have : 0<Fintype.card (Projectivization K V) := by exact_mod_cast (pow_pos hq (n+2)).trans_le h
    exact card_pos.mp (by simpa using this)
  nonemptyB := by
    have hdim' : Module.finrank K (Module.Dual K V)=(n+2)+1 := by rw [Subspace.dual_finrank_eq]; omega
    have h:=projective_card_lower hdim'
    have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
    have : 0<Fintype.card (Projectivization K (Module.Dual K V)) := by exact_mod_cast (pow_pos hq (n+2)).trans_le h
    exact card_pos.mp (by simpa using this)
  product := by
    have ha:=projective_card_lower (show Module.finrank K V=(n+2)+1 by omega)
    have hdim' : Module.finrank K (Module.Dual K V)=(n+2)+1 := by rw [Subspace.dual_finrank_eq]; omega
    have hb':=projective_card_lower hdim'
    have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
    calc
      _ ≤ (Nat.card K:ℝ)^(n+3)*1 := mul_le_mul_of_nonneg_left
        (exp_le_one_iff.mpr (by linarith)) (pow_nonneg (by linarith) _)
      _ ≤ (Nat.card K:ℝ)^((n+2)+(n+2)) := by rw [mul_one]; exact pow_le_pow_right₀ hq (by omega)
      _ = (Nat.card K:ℝ)^(n+2)*(Nat.card K:ℝ)^(n+2) := pow_add ..
      _ ≤ _ := by simpa only [card_univ] using mul_le_mul ha hb' (pow_nonneg (by linarith) _) (by positivity)

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_BalancedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ChronologicalTree
open BinaryTree Finset FreshExecution
open scoped Classical
noncomputable section

variable {I : Type*} [LinearOrder I]
local instance liveEq : DecidableEq I := Classical.decEq _

def liveTree (S : Finset I) (fallback : I) : BinaryTree I :=
  (balanced 0 S.card).map (fun j=>(S.sort (·≤·)).getD j fallback)

end
end SharpLogRamsey.ChronologicalTree

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_LiveFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Selection Selection.AuxiliarySupport
open FreshExecution TreeDecoder BinaryTree ChronologicalTree
open scoped Classical BigOperators
noncomputable section
variable {I : Type*} [Fintype I] [LinearOrder I]
local instance liveDecEq : DecidableEq I := Classical.decEq _

def liveRetraction (S : Finset I) (h : S.Nonempty) (i : I) : S :=
  if hi : i∈S then ⟨i,hi⟩ else ⟨h.choose,h.choose_spec⟩

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {Ω : Type*} [Fintype Ω]
  {p : I→Law (Projectivization K (Module.Dual K V))}
  {r : I→Law (Projectivization K V)}
  {goodA : I→Finset (Projectivization K (Module.Dual K V))}
  {goodB : I→Finset (Projectivization K V)} {MA MB κA κB : I→ℝ}
local instance liveBanksFintype (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

variable (S : Finset I) (hS : S.Nonempty)
  (X : ∀ i : S,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
  (Y : ∀ i : S,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))

abbrev liveX (i : I) := X (liveRetraction S hS i)
abbrev liveY (i : I) := Y (liveRetraction S hS i)

variable {d : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=d+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
  (hτ : 0<τ) (hτsmall : τ≤1/40000)
  (hMA : ∀ i∈S,0<MA i) (hMB : ∀ i∈S,0<MB i)
  (hprod : ∀ i∈S,(Nat.card K:ℝ)^(d+3)*exp (-b)≤
    (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))

abbrev liveOriginal (z : OriginalChoice (liveX S hS X) (liveY S hS Y)) (i : I) :
    Original (K:=K) (V:=V) d b :=
  originalFamily (liveX S hS X) (liveY S hS Y)
    (fun i=>hMA _ (liveRetraction S hS i).property)
    (fun i=>hMB _ (liveRetraction S hS i).property)
    (fun i=>hprod _ (liveRetraction S hS i).property) z i

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_LiveRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.ActualPivot
open Finset Real Selection Selection.AuxiliarySupport
open FreshExecution TreeDecoder BinaryTree ChronologicalTree
open scoped Classical BigOperators
noncomputable section
variable {K V I Y₀ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype I] [LinearOrder I] [Fintype Y₀] {d : ℕ} {b τ P H : ℝ}
local instance realDecEq : DecidableEq I := Classical.decEq _
local instance realizationBanksFintype : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

structure Realization (q : Law Y₀) where
  Ω : Type
  inst : Fintype Ω
  μ : Law Ω
  source : Ω→Y₀
  supports : Ω→I→Original (K:=K) (V:=V) d b
  marginal : μ.map source=q

attribute [instance] Realization.inst

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_MixtureRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]
lemma Law.eq_of_integrals (p q : Law A)
    (h : ∀ f : A→ℝ,(∑ a,p.mass a*f a)=∑ a,q.mass a*f a) : p=q := by
  ext a
  simpa using h (fun x=>if x=a then 1 else 0)
end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.ActualPivot
open Finset Selection
open scoped Classical BigOperators
noncomputable section
variable {K V I Y₀ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  {d : ℕ} {b : ℝ} [Fintype Y₀]

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma Realization.integral {q : Law Y₀} (e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q)
    (f : Y₀→ℝ) : (∑ ω,e.μ.mass ω*f (e.source ω))=∑ y,q.mass y*f y := by
  rw [←e.μ.sum_map e.source f,e.marginal]

variable {Θ : Type} [Fintype Θ] {Y : Θ→Type} [∀ θ,Fintype (Y θ)]

def Realization.mix (ν : Law Θ) (q : ∀ θ,Law (Y θ))
    (e : ∀ θ : {θ // ν.mass θ≠0},Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) (q θ)) :
    Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) (ν.sigma q) where
  Ω := Σ θ : {θ // ν.mass θ≠0},(e θ).Ω
  inst := inferInstance
  μ := ν.nullFree.sigma (fun θ=>(e θ).μ)
  source ω := ⟨ω.1.val,(e ω.1).source ω.2⟩
  supports ω := (e ω.1).supports ω.2
  marginal := by
    apply Law.eq_of_integrals
    intro f
    rw [Law.sum_map,Law.sigma_sum,Law.sigma_sum]
    calc
      _ = ∑ z,ν.nullFree.mass z*∑ y,(q z).mass y*f ⟨z.val,y⟩ := by
        apply sum_congr rfl
        intro z _
        congr 1
        exact (e z).integral (fun y=>f ⟨z.val,y⟩)
      _ = _ := ν.nullFree_integral (fun θ=>∑ y,(q θ).mass y*f ⟨θ,y⟩)

def Realization.attach {Ω B : Type} [Fintype Ω] [Fintype B]
    {q : Law Y₀} (e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q)
    (p : Law Ω) (tag : Y₀→B) (g : Ω→B)
    (h : q.map tag=p.map g) :
    Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) p where
  Ω := Σ _x : e.Ω,Ω
  inst := inferInstance
  μ := e.μ.attach p (tag∘e.source) g
  source ω := ω.2
  supports ω := e.supports ω.1
  marginal := by
    apply Law.eq_of_integrals
    intro f
    rw [Law.sum_map]
    apply Law.attach_source
    rw [←Law.map_map,e.marginal,h]

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_HighRankMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection
open scoped Classical BigOperators
noncomputable section

structure StreamReplacement {Ω F ι Γ : Type} [Fintype Ω] [Fintype F] [Fintype Γ]
    (p : Law Ω) (G : Ω→ι→F) (pos : ι→ℕ) (m : ℕ) (DD : Γ→Finset F) (B C : ℝ) where
  X : Type
  finiteX : Fintype X
  μ : @Law X finiteX
  source : X→Ω
  msg : X→Γ
  index : X→Fin m→ι
  ordered : ∀ x,StrictMono (fun i=>pos (index x i))
  supported : ∀ x,μ.mass x≠0→p.mass (source x)≠0
  hit : ∀ x,μ.mass x≠0→∀ i,G (source x) (index x i)∈DD (msg x)
  size : ∀ x,((DD (msg x)).card:ℝ)≤B
  dominated : letI:=finiteX; ∀ a,(μ.map source).mass a≤4*p.mass a
  cost : letI:=finiteX; entropy (μ.map msg)≤C
attribute [instance] StreamReplacement.finiteX

end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Exposure_StreamTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Selection
open scoped Classical
noncomputable section
variable {Ω F F' ι ι' Γ : Type} [Fintype Ω] [Fintype F] [Fintype F'] [Fintype Γ]

def StreamReplacement.transport {p : Law Ω} {G : Ω→ι→F} {pos : ι→ℕ} {m : ℕ}
    {DD : Γ→Finset F} {B C : ℝ} (e : StreamReplacement p G pos m DD B C)
    (f : F≃F') (j : ι→ι') (G' : Ω→ι'→F') (pos' : ι'→ℕ)
    (htime : ∀ i,pos' (j i)=pos i) (hvalue : ∀ x i,G' x (j i)=f (G x i)) :
    StreamReplacement p G' pos' m (fun c=>(DD c).map f.toEmbedding) B C where
  X:=e.X
  finiteX:=e.finiteX
  μ:=e.μ
  source:=e.source
  msg:=e.msg
  index x i:=j (e.index x i)
  ordered x:=by simpa only [htime] using e.ordered x
  supported:=e.supported
  hit x hx i:=by
    rw [hvalue]
    exact mem_map.mpr ⟨_,e.hit x hx i,rfl⟩
  size x:=by simpa only [card_map] using e.size x
  dominated:=e.dominated
  cost:=e.cost
end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_ContextOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section

structure ContextOutput {Ω F : Type} [Fintype Ω] [Fintype F] {ℓ : ℕ}
    (p : Law Ω) (G : Ω→Fin ℓ→F) (m : ℕ) (B C L : ℝ) where
  X : Type
  Γ : Type
  finiteX : Fintype X
  finiteΓ : Fintype Γ
  μ : @Law X finiteX
  source : X→Ω
  msg : X→Γ
  chosen : X→Fin m↪o Fin ℓ
  domains : Γ→Fin m→Finset F
  supported : ∀ x,p.mass (source x)≠0
  hit : ∀ x i,G (source x) (chosen x i)∈domains (msg x) i
  size : ∀ c i,((domains c i).card:ℝ)≤B
  dominated : letI:=finiteX; ∀ a,(μ.map source).mass a≤L*p.mass a
  cost : letI:=finiteX; letI:=finiteΓ; entropy (μ.map msg)≤C
attribute [instance] ContextOutput.finiteX ContextOutput.finiteΓ

end
end SharpLogRamsey.Selection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_UnifiedContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Selection
open scoped Classical BigOperators
noncomputable section
variable {Ω F Γ : Type} [Fintype Ω] [Fintype F] [Fintype Γ]
  {ℓ m : ℕ} {p : Law Ω} {G : Ω→Fin ℓ→F} {DD : Γ→Finset F} {B C : ℝ}

def StreamReplacement.toContextOutput (e : StreamReplacement p G Fin.val m DD B C) :
    ContextOutput p G m B C 4 := by
  let X':={x : e.X // e.μ.mass x≠0}
  let S:=univ.image e.msg
  let msg : X'→S:=fun x=>⟨e.msg x.val,mem_image.mpr ⟨x.val,mem_univ _,rfl⟩⟩
  refine ⟨X',S,inferInstance,inferInstance,e.μ.nullFree,(fun x=>e.source x.val),msg,
    (fun x=>OrderEmbedding.ofStrictMono (e.index x.val) (e.ordered x.val)),
    (fun c _=>DD c.val),?_,?_,?_,?_,?_⟩
  · intro x
    exact e.supported x.val x.property
  · intro x i
    exact e.hit x.val x.property i
  · intro c i
    obtain ⟨x,_,hx⟩:=mem_image.mp c.property
    rw [←hx]
    exact e.size x
  · intro a
    rw [Law.nullFree_map]
    exact e.dominated a
  · have he:=entropy_map_eq_of_injective (e.μ.nullFree.map msg) (Subtype.val : S→Γ) Subtype.val_injective
    rw [Law.map_map] at he
    change entropy (e.μ.nullFree.map (fun x=>e.msg x.val))=entropy (e.μ.nullFree.map msg) at he
    rw [Law.nullFree_map] at he
    exact he ▸ e.cost
end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_ClassTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.Marking
open Finset Selection ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev CovectorPair := Projectivization K (Module.Dual K V) × Projectivization K V

end
end SharpLogRamsey.Marking

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_ReciprocalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Selection TreeDecoder FreshExecution BinaryTree ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) ]
  {I X Ω : Type} [Fintype I] [Fintype X] [Fintype Ω]
  {d ℓ : ℕ} {b τ P H : ℝ}
local instance outEqI : DecidableEq I := Classical.decEq _
local instance outBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

def reciprocalOutputCost (W ht m : ℕ) : ℝ :=
  ((2*W+1:ℕ):ℝ)*log 2+
    (W:ℝ)*(log ((Fintype.card I:ℝ)+1)+headerCost (K:=K) (V:=V)+log (m+1:ℕ))+
    (2*(H+22)*(Nat.card K:ℝ)*P)*
      ((ht:ℝ)*(potential ((Nat.card K:ℝ)^(d+3)) ((univ,univ) : ChronoDomains (K:=K) (V:=V))+(W:ℝ)*(b+log 4+2*log 2000))+(W:ℝ)*P)

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_InitialTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey
open Finset Real Selection Marking
open scoped Classical BigOperators
noncomputable section

namespace Selection
variable {α : Type} [Fintype α] [Nonempty α]
def uniformLaw : Law α where
  mass _:=1/(Fintype.card α:ℝ)
  nonneg _:=by positivity
  total:=by simp [Fintype.card_ne_zero]

lemma uniformLaw_event (E : Finset α) : uniformLaw.event E=FiniteStreamTail.probability E:=by
  simp only [Law.event,uniformLaw,sum_const,nsmul_eq_mul,FiniteStreamTail.probability]
  ring

end Selection

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma independent_selected {N k : ℕ} (z : Fin N→Flag K V)
    (h : k ≤ (flagGraph K V z).indepNum) :
    ∃ e : Fin k↪o Fin N,Consistent (fun j=>z (e j)) := by
  obtain ⟨S,hS⟩:=(flagGraph K V z).exists_isNIndepSet_indepNum
  obtain ⟨T,hTS,hTk⟩:=exists_subset_card_eq (s:=S) (n:=k) (by rwa [hS.card_eq])
  let e:=T.orderEmbOfFin hTk
  refine ⟨e,?_⟩
  have hc : ConsistentOn z T:=(consistentOn_iff_compl_isClique _ _).mpr (by
    rw [SimpleGraph.isClique_compl]
    exact hS.isIndepSet.mono (by exact_mod_cast hTS))
  intro a b hab hi
  exact hc (e a) (T.orderEmbOfFin_mem hTk a) (e b) (T.orderEmbOfFin_mem hTk b) (e.strictMono hab) hi

end
end SharpLogRamsey

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Construction_InitialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.InitialExperiment
open Finset Real Filter Selection Marking FiniteStreamTail RectangleStreamEvent
open scoped Classical BigOperators Topology
noncomputable section
local instance initLawFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance initLawProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance initLawFiniteDouble_r98ddb2_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance initLawDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _

def occupancyConstant (i : ℕ) : ℝ := (((i+4)^2:ℕ)+5:ℝ)/log 2

variable (i q : ℕ) [Fact q.Prime] (N k : ℕ)

local instance initLawDoubleProjective_r98ddb2_1 {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _
local instance initLawFlagNonempty : Nonempty (Flag (ZMod q) (Fin (i+4)→ZMod q)):=
  Fintype.card_pos_iff.mp (by
    have hh:=flags_card_pos (K:=ZMod q) (V:=Fin (i+4)→ZMod q) (d:=i+3) (by omega) (by simp)
    simpa only [←Nat.card_eq_fintype_card] using hh)

def goodEvent : Finset (Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q)):=
  univ.filter (fun z=>∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
    (hits (rectangle W) z:ℝ)<occupancyConstant i*log (q:ℝ))

lemma goodEvent_half (hN : (N:ℝ) ≤ (q:ℝ)^(i+3)*log (q:ℝ)) :
    (1:ℝ)/2 ≤ probability (goodEvent i q N) := by
  have hh:=simultaneous_good_probability (d:=i+3) (N:=N) (K:=ZMod q) (V:=Fin (i+4)→ZMod q)
    (by omega) (by simp) (by simpa only [Nat.card_zmod] using hN)
  have hq : 2 ≤ (q:ℝ):=by exact_mod_cast (Fact.out : q.Prime).two_le
  have hq0 : (0:ℝ) < q:=by linarith
  have hdiv : 1/(q:ℝ) ≤ 1/2:=(div_le_iff₀ hq0).mpr (by linarith)
  have hin : (1:ℝ)/2 ≤ 1-1/q:=by linarith
  apply hin.trans
  simpa only [goodEvent,occupancyConstant,Nat.card_zmod,show i+3+1=i+4 by omega,
    probability,hits,rectangle,mem_filter,mem_univ,true_and,←Fintype.card_subtype,
    ←Nat.card_eq_fintype_card] using hh

def law (hN : (N:ℝ) ≤ (q:ℝ)^(i+3)*log (q:ℝ)) : Law (goodEvent i q N):=
  uniformLaw.onEvent (goodEvent i q N) (by rw [uniformLaw_event]; have:=goodEvent_half i q N hN;linarith)

variable (h : ∀ z : Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q),
  k ≤ (flagGraph (ZMod q) (Fin (i+4)→ZMod q) z).indepNum)

def chosen (z : Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q)) : Fin k↪o Fin N:=
  Classical.choose (independent_selected z (h z))

def tuple (z : goodEvent i q N) : Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q):=
  fun j=>z.val (chosen i q N k h z.val j.rev)

end
end SharpLogRamsey.InitialExperiment

end

end OAI
end


