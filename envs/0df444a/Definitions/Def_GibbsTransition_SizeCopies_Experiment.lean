-- Prove2me | Definitions.Def_GibbsTransition_SizeCopies_Experiment
-- name    : GibbsTransition_SizeCopies_Experiment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T21:52:53.024404+00:00
-- url     : https://prove2.me/theorems/55267c39-d4ec-4247-a347-ed88a1b31641
-- title:
--   Unrestricted measurable fresh-state experiments and stopped costs
-- statement:
--   Retained memory is represented by matrix coordinates on an arbitrary orthonormal-basis type $\iota$. Positivity is tested on every finite quadratic form; a positive kernel is trace class when its diagonal is summable. A state has trace one. There is no dimension bound, finite outcome restriction, or fixed stopping horizon.
--
--   A measurable instrument gives a joint outcome/posterior-state kernel and complex linear event operations. The latter are completely positive at every finite ancilla size. On each positive trace-one input the outcome measure has mass one, posterior states have trace one, and its entrywise integrals and event probabilities agree with the event operation and its trace. Integrability is explicit. Only classical outcomes are available to the query policy; the posterior matrix remains quantum memory.
--
--   A query is a positive integer cube size and a dyadic field in $[0,1]$. It appends the actual independent Gibbs matrix to retained memory by tensor multiplication, followed by the public instrument. The law is recursively induced by those operations. Termination, error, size caps, expected copies and expected spins are limits of the absorbing finite-horizon laws, in $\mathbb R_{\ge0}\cup\{\infty\}$. No correctness, closeness, or resource claim is part of instrument validity.
--
--   Memory is measurable in the Borel sigma algebra of its trace-class topology, specified by positive-decomposition neighborhoods equivalent to trace-norm neighborhoods. This covers nonseparable memory without imposing coordinate-only measurability.
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), §2.2, Equations (7)–(11), printed p. 4 (PDF p. 6); Lemma 5.3 proof, printed p. 11 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Physics

set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GibbsTransition.SizeCopies

/-- Finite histories carry the disjoint-union finite-product sigma algebra. -/
instance historyMeasurableSpace (O : Type) [MeasurableSpace O] :
    MeasurableSpace (List O) :=
  MeasurableSpace.comap
    (fun l : List O => (⟨l.length, fun i : Fin l.length => l[i]⟩ : Σ n : ℕ, Fin n → O))
    inferInstance

/-- A positive trace-class operator in matrix coordinates on an arbitrary
orthonormal basis. No bound on the dimension of retained memory is imposed. -/
abbrev MemoryMatrix (ι : Type) := ι → ι → ℂ

def KernelPositive {ι : Type} (A : MemoryMatrix ι) : Prop :=
  (∀ i j, star (A i j) = A j i) ∧
  ∀ (s : Finset ι) (v : ι → ℂ),
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (v i) * A i j * v j).re

def PositiveFinite {ι : Type} (A : MemoryMatrix ι) : Prop :=
  KernelPositive A ∧ Summable (fun i => (A i i).re)

def KernelTrace {ι : Type} (A : MemoryMatrix ι) : ℝ := ∑' i, (A i i).re

def IsMemoryState {ι : Type} (A : MemoryMatrix ι) : Prop :=
  PositiveFinite A ∧ KernelTrace A = 1

/-- Complex linear span of positive finite-trace kernels. -/
def TraceKernel {ι : Type} (X : MemoryMatrix ι) : Prop :=
  ∃ A B C D : MemoryMatrix ι,
    PositiveFinite A ∧ PositiveFinite B ∧ PositiveFinite C ∧ PositiveFinite D ∧
    X = A - B + Complex.I • C - Complex.I • D

/-- Trace-class neighborhoods. The decomposition gauge is equivalent to the
trace norm: norm(X)<=gauge(X)<=2 norm(X), by real/imaginary Jordan parts.
Using its topology (not merely the coordinate sigma algebra) also covers
normal instruments on nonseparable Hilbert spaces. Other raw-kernel cosets
are off-domain and do not change the physical trace-class topology. -/
def memoryBall {ι : Type} (center : MemoryMatrix ι) (radius : ℝ) : Set (MemoryMatrix ι) :=
  {X | ∃ A B C D : MemoryMatrix ι,
    PositiveFinite A ∧ PositiveFinite B ∧ PositiveFinite C ∧ PositiveFinite D ∧
    X - center = A - B + Complex.I • C - Complex.I • D ∧
    KernelTrace A + KernelTrace B + KernelTrace C + KernelTrace D < radius}

@[instance_reducible] def memoryTopology (ι : Type) : TopologicalSpace (MemoryMatrix ι) :=
  TopologicalSpace.generateFrom {U | ∃ (center : MemoryMatrix ι) (radius : ℝ),
    0 < radius ∧ U = memoryBall center radius}

instance (priority := 2000) memoryMeasurableSpace (ι : Type) : MeasurableSpace (MemoryMatrix ι) :=
  @borel (MemoryMatrix ι) (memoryTopology ι)

structure CubeQuery where
  side : ℕ
  field : ℚ
  positive_side : 1 ≤ side
  field_range : field ∈ Set.Icc (0 : ℚ) 1
  dyadic : ∃ m n : ℕ, field = (m : ℚ) / 2 ^ n
  deriving Countable

instance : MeasurableSpace CubeQuery := ⊤

/-- A raw instrument contains its joint outcome/post-state kernel and the
linear operation for each measurable outcome event. Neither depends on u.
Only the outcome, not the posterior matrix, is available to classical control. -/
structure InstrumentData (O ι κ : Type) [MeasurableSpace O] where
  apply : MemoryMatrix ι → Measure (O × MemoryMatrix κ)
  eventMap : Set O → MemoryMatrix ι →ₗ[ℂ] MemoryMatrix κ

/-- Complete positivity on trace-class inputs, and Born/posterior consistency.
The integrability clause prevents Bochner's off-domain zero convention.
These are physical instrument laws, not correctness or resource claims. -/
def IsInstrument {O ι κ : Type} [MeasurableSpace O]
    (I : InstrumentData O ι κ) : Prop :=
  Measurable I.apply ∧
  (∀ A, IsMemoryState A →
    I.apply A Set.univ = 1 ∧
    (∀ᵐ os ∂I.apply A, IsMemoryState os.2) ∧
    ∀ S, MeasurableSet S →
      PositiveFinite (I.eventMap S A) ∧
      KernelTrace (I.eventMap S A) = ((I.apply A) (Prod.fst ⁻¹' S)).toReal ∧
      ∀ a b,
        Integrable (fun os : O × MemoryMatrix κ => os.2 a b)
          ((I.apply A).restrict (Prod.fst ⁻¹' S)) ∧
        I.eventMap S A a b =
          ∫ os in Prod.fst ⁻¹' S, os.2 a b ∂I.apply A) ∧
  (∀ S, MeasurableSet S → ∀ (n : ℕ)
      (X : Fin n → Fin n → MemoryMatrix ι),
    (∀ a b, TraceKernel (X a b)) →
    KernelPositive (fun a b : Fin n × ι => X a.1 b.1 a.2 b.2) →
    KernelPositive (fun a b : Fin n × κ => I.eventMap S (X a.1 b.1) a.2 b.2))

/-- Adjoining precisely one fresh, independent finite-cube density matrix. -/
def appendFresh {ι : Type} (A : MemoryMatrix ι) (u : Interaction)
    (beta : ℚ) (q : CubeQuery) : MemoryMatrix (ι × Configuration q.side) :=
  fun a b => A a.1 b.1 * gibbsDensity u q.side q.field beta a.2 b.2

abbrev ExperimentRecord (O ι : Type) := (List O × List CubeQuery) × MemoryMatrix ι

/-- Unrestricted adaptive fresh-state experiments. Memory has an arbitrary
orthonormal-basis type; outcomes have an arbitrary measurable space; there is
no finite horizon. All choices are public functions of classical outcomes. -/
structure Experiment (O ι : Type) [MeasurableSpace O] where
  initial : Measure (O × MemoryMatrix ι)
  action : List O → CubeQuery ⊕ ℚ
  instrument : (h : List O) → (q : CubeQuery) →
    InstrumentData O (ι × Configuration q.side) ι

def experimentStep {O ι : Type} [MeasurableSpace O] (A : Experiment O ι)
    (u : Interaction) (beta : ℚ) (r : ExperimentRecord O ι) :
    Measure (ExperimentRecord O ι) :=
  match A.action r.1.1 with
  | Sum.inr _ => Measure.dirac r
  | Sum.inl q => Measure.map
      (fun os : O × MemoryMatrix ι => ((r.1.1 ++ [os.1], r.1.2 ++ [q]), os.2))
      ((A.instrument r.1.1 q).apply (appendFresh r.2 u beta q))

def experimentRun {O ι : Type} [MeasurableSpace O] (A : Experiment O ι)
    (u : Interaction) (beta : ℚ) : ℕ → Measure (ExperimentRecord O ι)
  | 0 => Measure.map (fun os : O × MemoryMatrix ι => (([os.1], []), os.2)) A.initial
  | t+1 => (experimentRun A u beta t).bind (experimentStep A u beta)

/-- Measurability and physicality only. All maps are instance independent;
the sole u-dependence of the execution is the density in appendFresh. -/
def IsExperiment {O ι : Type} [MeasurableSpace O] (A : Experiment O ι) : Prop :=
  A.initial Set.univ = 1 ∧
  (∀ᵐ os ∂A.initial, IsMemoryState os.2) ∧
  Measurable A.action ∧
  (∀ h q, IsInstrument (A.instrument h q)) ∧
  (∀ h x, A.action h = Sum.inr x → x ∈ Set.Icc (1/4 : ℚ) (3/4)) ∧
  ∀ u, Admissible u → ∀ beta : ℚ, 0 < beta →
    Measurable (experimentStep A u beta)

def stopped {O ι : Type} [MeasurableSpace O] (A : Experiment O ι)
    (r : ExperimentRecord O ι) : Prop := ∃ x, A.action r.1.1 = Sum.inr x

def experimentTerminates {O ι : Type} [MeasurableSpace O] (A : Experiment O ι)
    (u : Interaction) (beta : ℚ) : Prop :=
  (⨆ t, experimentRun A u beta t {r | stopped A r}) = 1

def experimentError {O ι : Type} [MeasurableSpace O] (A : Experiment O ι)
    (u : Interaction) (beta epsilon : ℚ) : ℝ≥0∞ :=
  ⨆ t, experimentRun A u beta t {r | ∃ x,
    A.action r.1.1 = Sum.inr x ∧ |(x : ℝ) - transitionPoint u| > epsilon}

def experimentCorrect {O ι : Type} [MeasurableSpace O] (A : Experiment O ι)
    (u : Interaction) (beta epsilon delta : ℚ) : Prop :=
  experimentTerminates A u beta ∧ experimentError A u beta epsilon ≤ ENNReal.ofReal delta

def LearnsClass {O ι : Type} [MeasurableSpace O] (A : Experiment O ι)
    (beta epsilon delta : ℚ) : Prop :=
  ∀ u, InClass u → experimentCorrect A u beta epsilon delta

def experimentCap {O ι : Type} [MeasurableSpace O] (A : Experiment O ι)
    (u : Interaction) (beta : ℚ) (R : ℕ) : Prop :=
  ∀ t, ∀ᵐ r ∂experimentRun A u beta t, ∀ q ∈ r.1.2, q.side ≤ R

def experimentCopies {O ι : Type} [MeasurableSpace O] (A : Experiment O ι)
    (u : Interaction) (beta : ℚ) : ℝ≥0∞ :=
  ⨆ t, ∫⁻ r, (r.1.2.length : ℝ≥0∞) ∂experimentRun A u beta t

def experimentSpins {O ι : Type} [MeasurableSpace O] (A : Experiment O ι)
    (u : Interaction) (beta : ℚ) : ℝ≥0∞ :=
  ⨆ t, ∫⁻ r, (((r.1.2.map (fun q => q.side ^ 3)).sum : ℕ) : ℝ≥0∞)
    ∂experimentRun A u beta t

end GibbsTransition.SizeCopies


