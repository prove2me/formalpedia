-- Prove2me | Definitions.Def_GibbsTransition_SizeCopies_Supplement_Access
-- name    : GibbsTransition_SizeCopies_Supplement_Access
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:34:07.229192+00:00
-- url     : https://prove2.me/theorems/f03bb621-b448-4539-b3e6-5784d9680b2f
-- title:
--   Ground-state access, stopped output laws, and spin minimax
-- statement:
--   A query is a dyadic field in $[0,1]$ and a positive integer side length. Its state supplier returns the actual Gibbs density or the normalized whole-ground-space projector. Each query tensors one independent fresh state onto arbitrary retained quantum memory. Instance-independent completely positive instruments act on this joint state, with arbitrary measurable classical outcomes and no fixed stopping horizon.
--   $$N=\#\{\text{queries}\},\qquad V=\sum_tL_t^3,\qquad V_\beta^*(\epsilon)=\inf_{A\in\mathcal A^\beta_{\epsilon,1/10}(\mathcal C^*)}\sup_{u\in\mathcal C^*}\mathbb E_u^A[V].$$
--   Stopped costs are extended nonnegative expectations. The infimum over an empty admissible learner class is infinity. The pre-oversized-query object is the entire rational output subprobability measure on stopping without a query of side exceeding $R$; the oversized-query probability also includes nonterminating continuations.
--
--   The general access extension reuses the published instrument and memory laws. The minimax quantity uses the published Gibbs experiment directly, including almost-sure termination and arbitrary memory.
--
--   Execution measurability is required for physical state suppliers. The definition imposes no execution condition on arbitrary nonphysical matrices.
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Section 2.2, (8)–(10), Lemma 4.3, printed pp. 4,8 (PDF pp. 6,10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Experiment
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Field
set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GibbsTransition.SizeCopies.Supplement
attribute [local instance] Classical.propDecidable

inductive AccessMode where
  | ground
  | gibbs (beta : ℚ)

def ValidMode : AccessMode → Prop
  | .ground => True
  | .gibbs beta => 0 < beta

abbrev Supplier (q : ℕ) := (query : CubeQuery) → Cube q query.side

def fieldSupplier {q : ℕ} (p : FieldData q) (u : FieldInteraction q)
    (mode : AccessMode) : Supplier q := fun query =>
  match mode with
  | .ground => fieldGround p u query.side query.field
  | .gibbs beta => fieldGibbs p u query.side query.field beta

def starSupplier (u : Interaction) (mode : AccessMode) : Supplier 3 := fun query =>
  match mode with
  | .ground => groundDensity u query.side query.field
  | .gibbs beta => gibbsDensity u query.side query.field beta

/-- Exactly the published experiment control and instrument types, with a
parameterized local dimension. No bound on memory, outcomes, or stopping. -/
structure AccessExperiment (q : ℕ) (O ι : Type) [MeasurableSpace O] where
  initial : Measure (O × MemoryMatrix ι)
  action : List O → CubeQuery ⊕ ℚ
  instrument : (h : List O) → (query : CubeQuery) →
    InstrumentData O (ι × Config q query.side) ι

abbrev AccessRecord (O ι : Type) := ExperimentRecord O ι

def accessAppend {q : ℕ} {ι : Type} (S : Supplier q) (A : MemoryMatrix ι)
    (query : CubeQuery) : MemoryMatrix (ι × Config q query.side) :=
  fun x y => A x.1 y.1 * S query x.2 y.2

def accessStep {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) (S : Supplier q) (r : AccessRecord O ι) :
    Measure (AccessRecord O ι) :=
  match A.action r.1.1 with
  | .inr _ => Measure.dirac r
  | .inl query => Measure.map
      (fun os : O × MemoryMatrix ι => ((r.1.1 ++ [os.1], r.1.2 ++ [query]), os.2))
      ((A.instrument r.1.1 query).apply (accessAppend S r.2 query))

def accessRun {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) (S : Supplier q) : ℕ → Measure (AccessRecord O ι)
  | 0 => Measure.map (fun os : O × MemoryMatrix ι => (([os.1], []), os.2)) A.initial
  | t+1 => (accessRun A S t).bind (accessStep A S)

/-- Physicality and measurable control only, no correctness claims. -/
def IsAccessExperiment {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) : Prop :=
  A.initial Set.univ = 1 ∧ (∀ᵐ os ∂A.initial, IsMemoryState os.2) ∧
  Measurable A.action ∧ (∀ h query, IsInstrument (A.instrument h query)) ∧
  (∀ h x, A.action h = .inr x → x ∈ Set.Icc (1/4 : ℚ) (3/4)) ∧
  ∀ S : Supplier q, (∀ query, IsMemoryState (S query)) →
    Measurable (accessStep A S)

def accessStopped {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) (r : AccessRecord O ι) : Prop :=
  ∃ x, A.action r.1.1 = .inr x

def accessTerminates {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) (S : Supplier q) : Prop :=
  (⨆ t, accessRun A S t {r | accessStopped A r}) = 1

def accessError {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) (S : Supplier q) (theta : ℝ) (epsilon : ℚ) : ℝ≥0∞ :=
  ⨆ t, accessRun A S t {r | ∃ x, A.action r.1.1 = .inr x ∧ |(x : ℝ)-theta| > epsilon}

def accessCorrect {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) (S : Supplier q) (theta : ℝ) (epsilon delta : ℚ) : Prop :=
  accessTerminates A S ∧ accessError A S theta epsilon ≤ ENNReal.ofReal delta

def accessCopies {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) (S : Supplier q) : ℝ≥0∞ :=
  ⨆ t, ∫⁻ r, (r.1.2.length : ℝ≥0∞) ∂accessRun A S t

def accessSpins {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) (S : Supplier q) : ℝ≥0∞ :=
  ⨆ t, ∫⁻ r, (((r.1.2.map (fun query => query.side^3)).sum : ℕ) : ℝ≥0∞) ∂accessRun A S t

/-- This is the event of ever issuing a first oversized query; it includes runs
that subsequently continue forever. It is not restricted to stopped outputs. -/
def oversizedProbability {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) (S : Supplier q) (R : ℕ) : ℝ≥0∞ :=
  ⨆ t, accessRun A S t {r | ∃ query ∈ r.1.2, R < query.side}

def reported {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) (r : AccessRecord O ι) : ℚ :=
  match A.action r.1.1 with | .inl _ => 1/2 | .inr x => x

/-- Entire rational output subprobability measure on stopping without any
oversized query, not just its mass or its success probability. -/
def beforeOversizedOutput {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) (S : Supplier q) (R : ℕ) : Measure ℚ :=
  ⨆ t, Measure.map (reported A) ((accessRun A S t).restrict
    {r | accessStopped A r ∧ ∀ query ∈ r.1.2, query.side ≤ R})

def accessCap {q : ℕ} {O ι : Type} [MeasurableSpace O]
    (A : AccessExperiment q O ι) (S : Supplier q) (R : ℕ) : Prop :=
  ∀ t, ∀ᵐ r ∂accessRun A S t, ∀ query ∈ r.1.2, query.side ≤ R

/-- Actual minimax quantity (10), using the published Gibbs experiment.
ENNReal gives inf empty = infinity and admits infinite stopped costs. -/
def spinMinimax (beta epsilon : ℚ) : ℝ≥0∞ :=
  sInf {v | ∃ (O ι : Type) (mO : MeasurableSpace O)
    (A : @Experiment O ι mO),
    @IsExperiment O ι mO A ∧ @LearnsClass O ι mO A beta epsilon (1/10) ∧
    v = ⨆ u : {u : Interaction // InClass u}, @experimentSpins O ι mO A u.val beta}

/-- Generic success criterion for a rational output probability law. -/
def LawCorrect (law : Measure ℚ) (theta : ℝ) (epsilon delta : ℚ) : Prop :=
  law Set.univ = 1 ∧ law (Set.Icc (1/4 : ℚ) (3/4)) = 1 ∧
  law {x | |(x : ℝ)-theta| > epsilon} ≤ ENNReal.ofReal delta

end GibbsTransition.SizeCopies.Supplement


