-- Prove2me | Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Queries
-- name    : QuantumFunctionalEstimation_Master_Supplement_Queries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:57:27.784053+00:00
-- url     : https://prove2.me/theorems/582104c1-e8dc-4809-935c-4cd3809d2e9b
-- title:
--   Operational adaptive purified state-preparation queries
-- statement:
--   A preparation unitary $U$ acts on an environment of size $e$ and a state register of size $d$ and prepares
--   $$\rho=\operatorname{tr}_{\rm env}\bigl(U|0,0\rangle\langle0,0|U^*\bigr).$$
--   An algorithm is an input-independent finite adaptive interaction tree with arbitrary finite quantum workspace, an initial density matrix and a final real-outcome POVM. Each stage applies a quantum instrument, observes its classical outcome, chooses a controlled forward or adjoint oracle application, and continues with the corresponding subtree. Instrument operations are completely positive linear densities with respect to a reference Borel probability measure; their integral preserves trace. This permits discrete or continuous intermediate classical outcomes. Branch Born weights are integrated on unnormalized matrices. Measurability is required for each integrand, independently of any success guarantee.
--
--   A controlled call counts as one query. Uncontrolled calls fix the control to true, while false controls pad shorter branches. Calls to $U,U^*,cU,cU^*$ are available. The algorithm must succeed for every state and every unitary completion preparing that state, rather than a favorable purification. Bounds range over every $e\ge d$, so every state is preparable. A known second state in a closeness task is available through input-independent operations. This model gives an operational meaning to the introductory query lower bounds, without a lifting axiom or an assigned cost field.
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed pp. 2–3 (PDF pp. 4–5), §1.2 purified quantum query access and sample-to-query lifting

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Observables
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal Matrix.Norms.Elementwise
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- A finite quantum register coupled to an arbitrary real classical outcome. CP densities
with respect to a reference probability measure encode discrete and continuous instruments.
The normalization is on the integral, not on each conditional operation. -/
structure Instrument (ι : Type) [Fintype ι] where
  reference : ProbabilityMeasure ℝ
  operation : ℝ → (Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ)
  completelyPositive : ∀ z, QAlgorithms.Entanglement.IsCompletelyPositive (operation z)
  integrable : ∀ X i j, Integrable (fun z => operation z X i j) (reference : Measure ℝ)
  tracePreserving : ∀ X, (∫ z, (operation z X).trace.re ∂(reference : Measure ℝ)) = X.trace.re

abbrev QueryRegister (e d w : ℕ) := Fin w × (Bool × (Fin e × Fin d))

/-- One controlled forward or adjoint oracle application, identity on arbitrary workspace.
Disabling the control also permits padding a bounded-query adaptive algorithm. -/
def queryMatrix {e d w : ℕ} (adjoint : Bool)
    (U : Matrix (Fin e × Fin d) (Fin e × Fin d) ℂ) :
    Matrix (QueryRegister e d w) (QueryRegister e d w) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2.1 = y.2.1 then
    if x.2.1 then (if adjoint then Uᴴ else U) x.2.2 y.2.2
    else if x.2.2 = y.2.2 then 1 else 0
  else 0

/-- Actual bounded-depth interaction tree. The next operation and query direction can depend
on each previous instrument outcome; no part depends on the unknown oracle itself. -/
inductive QueryProcess (e d w : ℕ) : ℕ → Type
  | output (E : QAlgorithms.Measurements.OperatorPOVM (QueryRegister e d w) ℝ) : QueryProcess e d w 0
  | step {Q : ℕ} (I : Instrument (QueryRegister e d w)) (adjoint : ℝ → Bool)
      (next : ℝ → QueryProcess e d w Q) : QueryProcess e d w (Q + 1)

/-- Born weights of the unnormalized branches; integration sums their actual probabilities. -/
def queryMass {e d w Q : ℕ} (A : QueryProcess e d w Q)
    (U : Matrix (Fin e × Fin d) (Fin e × Fin d) ℂ)
    (X : Matrix (QueryRegister e d w) (QueryRegister e d w) ℂ) (B : Set ℝ) : ℝ≥0∞ :=
  match A with
  | .output E => ENNReal.ofReal (QAlgorithms.effectProb (E.operator B) X)
  | .step I adj next => ∫⁻ z,
      queryMass (next z) U
        (queryMatrix (adj z) U * I.operation z X * (queryMatrix (adj z) U)ᴴ) B
      ∂(I.reference : Measure ℝ)

/-- Measurability of every branch integrand. This is physical well-formedness, not a success
or complexity condition. Borel classical outputs cover standard measurable output spaces. -/
def QueryProcess.Measurable {e d w Q : ℕ} (A : QueryProcess e d w Q) : Prop :=
  match A with
  | .output _ => True
  | .step I adj next => (∀ z, (next z).Measurable) ∧
      ∀ (U : Matrix (Fin e × Fin d) (Fin e × Fin d) ℂ)
        (X : Matrix (QueryRegister e d w) (QueryRegister e d w) ℂ) (B : Set ℝ),
        MeasurableSet B → AEMeasurable (fun z => queryMass (next z) U
          (queryMatrix (adj z) U * I.operation z X * (queryMatrix (adj z) U)ᴴ) B)
          (I.reference : Measure ℝ)

structure QueryAlgorithm (e d Q : ℕ) where
  workspace : ℕ
  workspacePositive : 0 < workspace
  initial : Matrix (QueryRegister e d workspace) (QueryRegister e d workspace) ℂ
  initialDensity : QAlgorithms.IsDensityMatrix initial
  process : QueryProcess e d workspace Q
  measurable : process.Measurable

/-- Partial trace of U|0,0><0,0|U*. The zero input vector is explicit even on empty types;
all estimator bounds below use e>=d>=2, so it is an actual unit basis vector. -/
def prepared {e d : ℕ} (U : Matrix (Fin e × Fin d) (Fin e × Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  let ψ := U.mulVec (fun z => if z.1.val = 0 ∧ z.2.val = 0 then 1 else 0)
  fun i j => ∑ k : Fin e, ψ (k, i) * star (ψ (k, j))

/-- Uniform over all input states and ALL unitary completions of their purification.
In particular no favorable purification can be selected after seeing the state. -/
def QuerySuccessful {d e Q : ℕ} (F : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (ε : ℝ) (A : QueryAlgorithm e d Q) : Prop :=
  ∀ ρ : State d, ∀ U : Matrix (Fin e × Fin d) (Fin e × Fin d) ℂ,
    Uᴴ * U = 1 → U * Uᴴ = 1 → prepared U = ρ.val →
    (2 / 3 : ℝ≥0∞) ≤ queryMass A.process U A.initial (Set.Icc (F ρ.val - ε) (F ρ.val + ε))

end QuantumFunctionalEstimation.Master.Supplement


