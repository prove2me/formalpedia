-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34
-- name    : QAlgorithms_Papers_Independent_Support50_P34
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T21:35:34.814609+00:00
-- url     : https://prove2.me/theorems/f6570bff-9a50-49fd-affc-dcf83764f220
-- title:
--   Definitions for Continuity of the von Neumann entropy
-- statement:
--   The objects the formalized statements of *Continuity of the von Neumann entropy* (arXiv:0904.1963) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `QuantumState`: PDF p.3: a distinct wrapper installs trace norm, rather than the ambient operator topology.
--   - `stateOp`: PDF p.3: the bounded operator underlying a normalized density operator.
--   - `PositiveCone`: PDF p.3: positive trace-class operators, with no trace upper bound.
--   - `coneOp`: PDF p.3: inclusion of the positive cone into bounded operators.
--   - `RankLE`: PDF p.6: actual rank at most k, via containment in a span of k vectors. This does not use natural-valued finrank on an infinite-dimensional range.
--   - `rankStates`: PDF p.6: the rank-constrained state set.
--   - `finiteRankStates`: PDF p.6: all finite-rank states; approximation orders start at one.
--   - `StateConvex`: PDF p.3: convexity in the real space of self-adjoint operators.
--   - `stateClosedHull`: PDF pp.3,5: trace-norm closed convex hull, without operator-norm closure.
--   - `StateBarycenter`: PDF p.4: matrix-element characterization of the actual Bochner barycenter. For Borel probabilities on states the inclusion is trace-norm integrable, since states have trace norm one. Requiring scalar integrability rules out default-zero scalar integrals. This predicate does not postulate continuity or openness.
--   - `AtomicProbability`: PDF p.4: countably atomic, with the weak probability topology inherited separately.
--   - `stateFiber`: PDF p.4: all Borel probabilities in the prescribed barycenter fiber.
--   - `StateBarycenterOpen`: PDF pp.5,8: openness of the barycenter relation, with its actual weak domain. The scalar characterization defines the image uniquely, without choosing a state from a potentially empty state space. Surjectivity is a separate conclusion.
--   - `BarycenterOpenIntoHull`: PDF pp.5–6: relative openness into the closed convex hull, as required in Lemma 2B. This is distinct from openness into the whole state space in Theorem 1.
--   - `AtomicBarycenterOpen`: PDF p.8: the same openness statement restricted to countably atomic probabilities.
--   - `LowerBounded`: PDF p.4: lower boundedness means a real lower bound, while allowing +infinity.
--   - `UpperBounded`: PDF p.4: upper boundedness allows -infinity but requires a real upper bound.
--   - `FiniteERealContinuousOn`: PDF p.7: continuity includes finiteness, in addition to real-valued continuity.
--   - `StateConcaveOn`: PDF p.4: concavity on a state set, with zero coefficients annihilating infinite values.
--   - `StateConvexOn`: PDF p.4: convexity has the reverse Jensen inequality, on the same domain.
--   - `MuConcave`: PDF pp.4–5: universal completion-measurability and integral Jensen for every state law.
--   - `lowerRoof`: PDF p.5, Lemma 2A: the extended infimum over precisely the barycenter fiber.
--   - `upperRoof`: PDF p.6, Lemma 2B: the extended supremum over all Borel barycentric measures.
--   - `sigmaRoof`: PDF pp.11–12: sigma roof uses countably atomic measures, not finite-support ones. For these probabilities the extended integral is the source's countable weighted sum.
--   - `rankMuRoof`: PDF p.13: rank-k mu roof of a function on all states.
--   - `rankSigmaRoof`: PDF p.13: rank-k sigma roof, defined independently of the mu roof.
--   - `UniformExtendedApproximation`: PDF p.15: additive uniform approximation before finiteness has been established. For real bounded approximants these inequalities force the limit to be finite.
--   - `StateSymmetry`: PDF p.13, footnote 12: affine homeomorphisms preserving every rank stratum.
--   - `StateEnsemble`: PDF p.8: trace-norm average of an enumerated ensemble, including summability guards.
--   - `coneEntropyRaw`: PDF p.17: homogeneous quantum entropy on positive trace class; normalization is inside the bounded continuous functional calculus of -x log x. At trace zero this formula is zero, including the zero-dimensional Hilbert space.
--   - `coneEntropy`: PDF p.17: restriction of the homogeneous formula to its source domain.
--   - `FiniteEntropyContinuousOn`: PDF p.7 applied to a nonnegative extended entropy: continuity and finiteness.
--   - `ConeEnsemble`: PDF p.18: actual countable positive-cone ensembles, with trace-norm-convergent average.
--   - `coneApproximator`: PDF p.18: the cone k-approximator is the stated discrete ensemble supremum.
--   - `entropyDefect`: PDF p.18, (7): relative-entropy defect, independent of the H-H_k identity.
--   - `HasUA`: PDF p.23: uniform approximation, using an extended nonnegative supremum.
--   - `coneSumSet`: PDF p.27: the Minkowski sum on the actual positive cone.
--   - `ConeConvex`: PDF p.27: real convexity of a positive-operator set.
--   - `coneClosedHull`: PDF p.27: closed convex hull in trace norm, in the positive cone.
--   - `ConeBounded`: PDF p.24: trace-norm boundedness, on positive operators equivalent to bounded traces.
--   - `finiteConeHull`: PDF p.24: exactly m convex terms, allowing zero weights and repeated atoms.
--   - `EntropyConverges`: PDF p.29: a finite-valued entropy limit, not unrestricted convergence to infinity.
--   - `normalizedConeSet`: PDF p.34: normalization is computed from trace, not a prescribed state map.
--   - `ChoquetDominates`: PDF p.10: Choquet domination tests all bounded continuous real convex functions.
--   - `stateEntropyExt`: PDF p.16: the accepted natural-log state entropy as an extended signed cost.
--   - `StateUnitaryInvariant`: PDF p.16: unitary invariance, with actual unitaries, independent of any symmetry premise.
--   - `stateRelativeDefect`: PDF p.16: independent relative-entropy infima for countably atomic and arbitrary laws. The Bool selects the domain, not an assumed equality between the two infima.
--   - `CountableProbabilityWeights`: PDF p.7: a countable probability vector; total variation is used when this domain is topologized.
--   - `homogeneousClassicalEntropy`: PDF p.17: homogeneous classical entropy on nonnegative summable sequences. Normalization and the prefactor preserve the correction -eta(total mass).
--   - `UniformWeightTails`: PDF p.24: uniform homogeneous entropy tails for the restricted weight set. Coordinate i here is source coordinate i+1; dropping finitely many initial orders leaves precisely the source's limit with tail i>m.
--   - `restrictedConeHull`: PDF p.24: actual restricted countable convex averages, with trace-norm convergence.
--   - `contractionSumSet`: PDF p.32: each A_i is shared across all its m conjugations; contractions are independent.
--   - `scalarEta`: Appendix 7.2, PDF p.38: reuse the accepted natural-log entropy weight.
--   - `PositiveL1Ball`: Appendix 7.2, PDF p.38: positive part of the real l1 unit ball. An ENNReal mass bound enforces summability and coordinate bounds 0 <= x_j <= 1.
--   - `convergenceExponent`: Appendix 7.2, PDF p.38: convergence exponent; empty admissible set has infimum infinity.
--   - `weightedEntropyTail`: Appendix 7.2, PDF p.38: supremum of unnormalized entropy tails on the submass ball. Lean coordinate j represents source coordinate j+1, so source tail >=m+1 is j>=m.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, https://arxiv.org/abs/0904.1963v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P25
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

/-!
Statements from Shirokov, arXiv:0904.1963v3. All logarithms are natural.
The accepted nuclear operator realization supplies trace class and its trace-norm
 topology. Barycenters on bounded state domains are characterized by their scalar
matrix elements, with explicit scalar integrability; these uniquely characterize
the genuine trace-norm Bochner integral, not an operator-norm integral.
Local definitions have complete bodies. Deferred nodes are inventoried in HARD.md.
Compilation is pending the worker's mechanical handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Support50.P34

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State PositiveTraceClass traceNormValue stateTraceNormTopology traceNormTopology
   operatorTrace IsPositive IsTraceClass stateEntropy relativeEntropy entropyWeight)
open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)
open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*}

/-- PDF p.3: a distinct wrapper installs trace norm, rather than the ambient operator topology. -/
def QuantumState (b : HilbertBasis I ℂ H) := State b

/-- PDF p.3: the bounded operator underlying a normalized density operator. -/
def stateOp (b : HilbertBasis I ℂ H) (rho : QuantumState b) : H →L[ℂ] H :=
  rho.val.val

/-- PDF p.3: reuse the accepted trace-norm topology on density operators. -/
instance quantumStateTopology (b : HilbertBasis I ℂ H) : TopologicalSpace (QuantumState b) :=
  stateTraceNormTopology b

/-- PDF p.4: Borel measurable sets for the trace-norm state topology. -/
instance quantumStateMeasurableSpace (b : HilbertBasis I ℂ H) : MeasurableSpace (QuantumState b) :=
  borel (QuantumState b)

/-- PDF p.4: the installed state measurable space is its Borel space. -/
instance quantumStateBorelSpace (b : HilbertBasis I ℂ H) : BorelSpace (QuantumState b) := ⟨rfl⟩

/-- PDF p.3: positive trace-class operators, with no trace upper bound. -/
def PositiveCone (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] := PositiveTraceClass H

/-- PDF p.3: inclusion of the positive cone into bounded operators. -/
def coneOp (A : PositiveCone H) : H →L[ℂ] H := A.val.val

/-- PDF p.3: the positive cone inherits the accepted trace-norm topology. -/
instance positiveConeTopology : TopologicalSpace (PositiveCone H) :=
  @TopologicalSpace.induced (PositiveCone H)
    (QAlgorithms.Papers.Independent.Dependency50.P13.TraceClass H)
    (fun A => A.val) traceNormTopology

/-- PDF p.4: Borel sets of the positive trace-class cone. -/
instance positiveConeMeasurableSpace : MeasurableSpace (PositiveCone H) := borel (PositiveCone H)

/-- PDF p.4: the installed cone measurable space is its Borel space. -/
instance positiveConeBorelSpace : BorelSpace (PositiveCone H) := ⟨rfl⟩

/-- PDF p.6: actual rank at most k, via containment in a span of k vectors.
This does not use natural-valued finrank on an infinite-dimensional range. -/
def RankLE (k : ℕ) (T : H →L[ℂ] H) : Prop :=
  ∃ v : Fin k → H, ∀ x, T x ∈ Submodule.span ℂ (Set.range v)

/-- PDF p.6: the rank-constrained state set. -/
def rankStates (b : HilbertBasis I ℂ H) (k : ℕ) : Set (QuantumState b) :=
  {rho | RankLE k (stateOp b rho)}

/-- PDF p.6: all finite-rank states; approximation orders start at one. -/
def finiteRankStates (b : HilbertBasis I ℂ H) : Set (QuantumState b) :=
  {rho | ∃ k : ℕ, 0 < k ∧ rho ∈ rankStates b k}

/-- PDF p.3: convexity in the real space of self-adjoint operators. -/
def StateConvex (b : HilbertBasis I ℂ H) (A : Set (QuantumState b)) : Prop :=
  Convex ℝ (stateOp b '' A)

/-- PDF pp.3,5: trace-norm closed convex hull, without operator-norm closure. -/
def stateClosedHull (b : HilbertBasis I ℂ H) (A : Set (QuantumState b)) :
    Set (QuantumState b) :=
  {rho | ∀ eps : ℝ, 0 < eps → ∃ T ∈ convexHull ℝ (stateOp b '' A),
    traceNormValue (stateOp b rho - T) < eps}

/-- PDF p.4: matrix-element characterization of the actual Bochner barycenter.
For Borel probabilities on states the inclusion is trace-norm integrable, since
states have trace norm one. Requiring scalar integrability rules out default-zero
scalar integrals. This predicate does not postulate continuity or openness. -/
def StateBarycenter (b : HilbertBasis I ℂ H) {X : Type*} [MeasurableSpace X]
    (s : X → QuantumState b) (mu : Measure X) (rho : QuantumState b) : Prop :=
  ∀ x y : H, Integrable (fun z => inner ℂ x (stateOp b (s z) y)) mu ∧
    inner ℂ x (stateOp b rho y) = ∫ z, inner ℂ x (stateOp b (s z) y) ∂mu

/-- PDF p.4: countably atomic, with the weak probability topology inherited separately. -/
def AtomicProbability {X : Type*} [MeasurableSpace X] (mu : ProbabilityMeasure X) : Prop :=
  ∃ S : Set X, S.Countable ∧ (mu : Measure X) Sᶜ = 0

/-- PDF p.4: all Borel probabilities in the prescribed barycenter fiber. -/
def stateFiber (b : HilbertBasis I ℂ H) (A : Set (QuantumState b))
    (rho : QuantumState b) : Set (ProbabilityMeasure A) :=
  {mu | StateBarycenter b (fun sigma : A => sigma.val) (mu : Measure A) rho}

/-- PDF pp.5,8: openness of the barycenter relation, with its actual weak domain.
The scalar characterization defines the image uniquely, without choosing a state
from a potentially empty state space. Surjectivity is a separate conclusion. -/
def StateBarycenterOpen (b : HilbertBasis I ℂ H) (A : Set (QuantumState b)) : Prop :=
  ∀ U : Set (ProbabilityMeasure A), IsOpen U →
    IsOpen {rho | ∃ mu ∈ U, mu ∈ stateFiber b A rho}

/-- PDF pp.5–6: relative openness into the closed convex hull, as required in Lemma 2B.
This is distinct from openness into the whole state space in Theorem 1. -/
def BarycenterOpenIntoHull (b : HilbertBasis I ℂ H) (A : Set (QuantumState b)) : Prop :=
  ∀ U : Set (ProbabilityMeasure A), IsOpen U →
    IsOpen {rho : stateClosedHull b A | ∃ mu ∈ U, mu ∈ stateFiber b A rho.val}

/-- PDF p.8: the same openness statement restricted to countably atomic probabilities. -/
def AtomicBarycenterOpen (b : HilbertBasis I ℂ H) (A : Set (QuantumState b)) : Prop :=
  ∀ U : Set {mu : ProbabilityMeasure A // AtomicProbability mu}, IsOpen U →
    IsOpen {rho | ∃ mu ∈ U, mu.val ∈ stateFiber b A rho}

/-- PDF p.4: lower boundedness means a real lower bound, while allowing +infinity. -/
def LowerBounded {X : Type*} (f : X → EReal) : Prop :=
  ∃ c : ℝ, ∀ x, (c : EReal) ≤ f x

/-- PDF p.4: upper boundedness allows -infinity but requires a real upper bound. -/
def UpperBounded {X : Type*} (f : X → EReal) : Prop :=
  ∃ c : ℝ, ∀ x, f x ≤ (c : EReal)

/-- PDF p.7: continuity includes finiteness, in addition to real-valued continuity. -/
def FiniteERealContinuousOn {X : Type*} [TopologicalSpace X] (f : X → EReal)
    (A : Set X) : Prop :=
  (∀ x ∈ A, f x ≠ ⊤ ∧ f x ≠ ⊥) ∧ ContinuousOn (fun x => (f x).toReal) A

/-- PDF p.4: concavity on a state set, with zero coefficients annihilating infinite values. -/
def StateConcaveOn (b : HilbertBasis I ℂ H) (A : Set (QuantumState b))
    (f : QuantumState b → EReal) : Prop :=
  StateConvex b A ∧ ∀ rho ∈ A, ∀ sigma ∈ A, ∀ tau ∈ A, ∀ a c : ℝ,
    0 ≤ a → 0 ≤ c → a + c = 1 →
    stateOp b tau = (a : ℂ) • stateOp b rho + (c : ℂ) • stateOp b sigma →
    (a : EReal) * f rho + (c : EReal) * f sigma ≤ f tau

/-- PDF p.4: convexity has the reverse Jensen inequality, on the same domain. -/
def StateConvexOn (b : HilbertBasis I ℂ H) (A : Set (QuantumState b))
    (f : QuantumState b → EReal) : Prop :=
  StateConvex b A ∧ ∀ rho ∈ A, ∀ sigma ∈ A, ∀ tau ∈ A, ∀ a c : ℝ,
    0 ≤ a → 0 ≤ c → a + c = 1 →
    stateOp b tau = (a : ℂ) • stateOp b rho + (c : ℂ) • stateOp b sigma →
    f tau ≤ (a : EReal) * f rho + (c : EReal) * f sigma

/-- PDF pp.4–5: universal completion-measurability and integral Jensen for every state law. -/
def MuConcave (b : HilbertBasis I ℂ H) (f : QuantumState b → EReal) : Prop :=
  (∀ mu : ProbabilityMeasure (QuantumState b), AEMeasurable f (mu : Measure _)) ∧
    ∀ (mu : ProbabilityMeasure (QuantumState b)) (rho : QuantumState b),
      StateBarycenter b id (mu : Measure _) rho →
      extendedIntegral (mu : Measure _) f ≤ f rho

/-- PDF p.5, Lemma 2A: the extended infimum over precisely the barycenter fiber. -/
def lowerRoof (b : HilbertBasis I ℂ H) (A : Set (QuantumState b))
    (f : A → EReal) (rho : QuantumState b) : EReal :=
  sInf {v | ∃ mu ∈ stateFiber b A rho, v = extendedIntegral (mu : Measure A) f}

/-- PDF p.6, Lemma 2B: the extended supremum over all Borel barycentric measures. -/
def upperRoof (b : HilbertBasis I ℂ H) (A : Set (QuantumState b))
    (f : A → EReal) (rho : QuantumState b) : EReal :=
  sSup {v | ∃ mu ∈ stateFiber b A rho, v = extendedIntegral (mu : Measure A) f}

/-- PDF pp.11–12: sigma roof uses countably atomic measures, not finite-support ones.
For these probabilities the extended integral is the source's countable weighted sum. -/
def sigmaRoof (b : HilbertBasis I ℂ H) (A : Set (QuantumState b))
    (f : A → EReal) (rho : QuantumState b) : EReal :=
  sSup {v | ∃ mu ∈ stateFiber b A rho, AtomicProbability mu ∧
    v = extendedIntegral (mu : Measure A) f}

/-- PDF p.13: rank-k mu roof of a function on all states. -/
def rankMuRoof (b : HilbertBasis I ℂ H) (f : QuantumState b → EReal) (k : ℕ) :=
  upperRoof b (rankStates b k) (fun rho => f rho.val)

/-- PDF p.13: rank-k sigma roof, defined independently of the mu roof. -/
def rankSigmaRoof (b : HilbertBasis I ℂ H) (f : QuantumState b → EReal) (k : ℕ) :=
  sigmaRoof b (rankStates b k) (fun rho => f rho.val)

/-- PDF p.15: additive uniform approximation before finiteness has been established.
For real bounded approximants these inequalities force the limit to be finite. -/
def UniformExtendedApproximation {X : Type*} (F : ℕ → X → EReal)
    (f : X → EReal) (A : Set X) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
    ∀ x ∈ A, f x ≤ F k x + (eps : EReal) ∧ F k x ≤ f x + (eps : EReal)

/-- PDF p.13, footnote 12: affine homeomorphisms preserving every rank stratum. -/
structure StateSymmetry (b : HilbertBasis I ℂ H) where
  map : QuantumState b ≃ₜ QuantumState b
  affine : ∀ rho sigma tau, ∀ a c : ℝ, 0 ≤ a → 0 ≤ c → a + c = 1 →
    stateOp b tau = (a : ℂ) • stateOp b rho + (c : ℂ) • stateOp b sigma →
    stateOp b (map tau) = (a : ℂ) • stateOp b (map rho) + (c : ℂ) • stateOp b (map sigma)
  rank : ∀ rho k, RankLE k (stateOp b (map rho)) ↔ RankLE k (stateOp b rho)

/-- PDF p.8: trace-norm average of an enumerated ensemble, including summability guards. -/
def StateEnsemble (b : HilbertBasis I ℂ H) (w : ℕ → ℝ)
    (s : ℕ → QuantumState b) (rho : QuantumState b) : Prop :=
  (∀ i, 0 ≤ w i) ∧ Summable w ∧ (∑' i, w i) = 1 ∧
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      traceNormValue ((∑ i ∈ Finset.range n, (w i : ℂ) • stateOp b (s i)) - stateOp b rho) < eps

example : RankLE 0 (0 : H →L[ℂ] H) := by
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  intro x
  exact Submodule.zero_mem _

example {X : Type*} : LowerBounded (fun _ : X => (0 : EReal)) := by
  exact ⟨0, by intro x; simp⟩

example {X : Type*} : UpperBounded (fun _ : X => (0 : EReal)) := by
  exact ⟨0, by intro x; simp⟩

example (b : HilbertBasis I ℂ H) : finiteRankStates b =
    {rho | ∃ k : ℕ, 0 < k ∧ RankLE k (stateOp b rho)} := by rfl

example (b : HilbertBasis I ℂ H) (A : Set (QuantumState b))
    (rho : QuantumState b) (mu : ProbabilityMeasure A) :
    mu ∈ stateFiber b A rho ↔
      StateBarycenter b (fun sigma : A => sigma.val) (mu : Measure A) rho := by rfl

example : entropyWeight 0 = 0 := by simp [entropyWeight]

/-- PDF p.17: homogeneous quantum entropy on positive trace class; normalization
is inside the bounded continuous functional calculus of -x log x. At trace zero
this formula is zero, including the zero-dimensional Hilbert space. -/
def coneEntropyRaw (b : HilbertBasis I ℂ H) (T : H →L[ℂ] H) : ℝ≥0∞ :=
  let t := (operatorTrace b T).re
  ENNReal.ofReal t * ∑' i, ENNReal.ofReal
    (inner ℂ (b i) ((cfc entropyWeight (((t⁻¹ : ℝ) : ℂ) • T)) (b i))).re

/-- PDF p.17: restriction of the homogeneous formula to its source domain. -/
def coneEntropy (b : HilbertBasis I ℂ H) (A : PositiveCone H) : ℝ≥0∞ :=
  coneEntropyRaw b (coneOp A)

/-- PDF p.7 applied to a nonnegative extended entropy: continuity and finiteness. -/
def FiniteEntropyContinuousOn {X : Type*} [TopologicalSpace X] (f : X → ℝ≥0∞)
    (A : Set X) : Prop :=
  (∀ x ∈ A, f x ≠ ⊤) ∧ ContinuousOn (fun x => (f x).toReal) A

/-- PDF p.18: actual countable positive-cone ensembles, with trace-norm-convergent average. -/
def ConeEnsemble (b : HilbertBasis I ℂ H) (T : H →L[ℂ] H)
    (w : ℕ → ℝ) (s : ℕ → PositiveCone H) : Prop :=
  (∀ i, 0 ≤ w i) ∧ Summable w ∧ (∑' i, w i) = 1 ∧
    ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      traceNormValue ((∑ i ∈ Finset.range n, (w i : ℂ) • coneOp (s i)) - T) < eps

/-- PDF p.18: the cone k-approximator is the stated discrete ensemble supremum. -/
def coneApproximator (b : HilbertBasis I ℂ H) (k : ℕ) (A : PositiveCone H) : ℝ≥0∞ :=
  sSup {v | ∃ (w : ℕ → ℝ) (s : ℕ → PositiveCone H),
    ConeEnsemble b (coneOp A) w s ∧ (∀ i, RankLE k (coneOp (s i))) ∧
    v = ∑' i, ENNReal.ofReal (w i) * coneEntropy b (s i)}

/-- PDF p.18, (7): relative-entropy defect, independent of the H-H_k identity. -/
def entropyDefect (b : HilbertBasis I ℂ H) (k : ℕ) (A : PositiveCone H) : ℝ≥0∞ :=
  sInf {v | ∃ (w : ℕ → ℝ) (s : ℕ → PositiveCone H),
    ConeEnsemble b (coneOp A) w s ∧ (∀ i, RankLE k (coneOp (s i))) ∧
    v = ∑' i, ENNReal.ofReal (w i) * relativeEntropy (s i).val A.val}

/-- PDF p.23: uniform approximation, using an extended nonnegative supremum. -/
def HasUA (b : HilbertBasis I ℂ H) (A : Set (PositiveCone H)) : Prop :=
  Tendsto (fun k : ℕ => ⨆ T : A, entropyDefect b (k + 1) T.val) atTop (nhds 0)

/-- PDF p.27: the Minkowski sum on the actual positive cone. -/
def coneSumSet (A B : Set (PositiveCone H)) : Set (PositiveCone H) :=
  {T | ∃ X ∈ A, ∃ Y ∈ B, coneOp T = coneOp X + coneOp Y}

/-- PDF p.27: real convexity of a positive-operator set. -/
def ConeConvex (A : Set (PositiveCone H)) : Prop := Convex ℝ (coneOp '' A)

/-- PDF p.27: closed convex hull in trace norm, in the positive cone. -/
def coneClosedHull (A : Set (PositiveCone H)) : Set (PositiveCone H) :=
  {T | ∀ eps : ℝ, 0 < eps → ∃ X ∈ convexHull ℝ (coneOp '' A),
    traceNormValue (coneOp T - X) < eps}

/-- PDF p.24: trace-norm boundedness, on positive operators equivalent to bounded traces. -/
def ConeBounded (b : HilbertBasis I ℂ H) (A : Set (PositiveCone H)) : Prop :=
  ∃ c : ℝ, ∀ T ∈ A, (operatorTrace b (coneOp T)).re ≤ c

/-- PDF p.24: exactly m convex terms, allowing zero weights and repeated atoms. -/
def finiteConeHull (m : ℕ) (A : Set (PositiveCone H)) : Set (PositiveCone H) :=
  {T | ∃ (w : Fin m → ℝ) (s : Fin m → PositiveCone H),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∀ i, s i ∈ A) ∧
    coneOp T = ∑ i, (w i : ℂ) • coneOp (s i)}

/-- PDF p.29: a finite-valued entropy limit, not unrestricted convergence to infinity. -/
def EntropyConverges (b : HilbertBasis I ℂ H) (u : ℕ → (H →L[ℂ] H))
    (T : H →L[ℂ] H) : Prop :=
  coneEntropyRaw b T ≠ ⊤ ∧ Tendsto (fun n => coneEntropyRaw b (u n)) atTop
    (nhds (coneEntropyRaw b T))

/-- PDF p.34: normalization is computed from trace, not a prescribed state map. -/
def normalizedConeSet (b : HilbertBasis I ℂ H) (A : Set (PositiveCone H)) :
    Set (QuantumState b) :=
  {rho | ∃ T ∈ A, stateOp b rho =
    ((((operatorTrace b (coneOp T)).re)⁻¹ : ℝ) : ℂ) • coneOp T}

example (b : HilbertBasis I ℂ H) : coneEntropyRaw b (0 : H →L[ℂ] H) = 0 := by
  simp [coneEntropyRaw, operatorTrace]

example : binaryEntropy 0 = 0 := by simp [binaryEntropy]

example (b : HilbertBasis I ℂ H) : HasUA b (∅ : Set (PositiveCone H)) := by
  simpa [HasUA] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0))

example : coneSumSet (∅ : Set (PositiveCone H)) ∅ = ∅ := by
  ext T
  simp [coneSumSet]

/-- PDF p.10: Choquet domination tests all bounded continuous real convex functions. -/
def ChoquetDominates (b : HilbertBasis I ℂ H)
    (nu mu : Measure (QuantumState b)) : Prop :=
  ∀ f : QuantumState b → ℝ, Continuous f →
    (∃ c : ℝ, ∀ rho, |f rho| ≤ c) →
    StateConvexOn b Set.univ (fun rho => (f rho : EReal)) →
    (∫ rho, f rho ∂mu) ≤ ∫ rho, f rho ∂nu

/-- PDF p.16: the accepted natural-log state entropy as an extended signed cost. -/
def stateEntropyExt (b : HilbertBasis I ℂ H) (rho : QuantumState b) : EReal :=
  (stateEntropy b rho : EReal)

/-- PDF p.16: unitary invariance, with actual unitaries, independent of any symmetry premise. -/
def StateUnitaryInvariant {Y : Type*} (b : HilbertBasis I ℂ H)
    (f : QuantumState b → Y) : Prop :=
  ∀ U : H →L[ℂ] H,
    U.adjoint.comp U = ContinuousLinearMap.id ℂ H →
    U.comp U.adjoint = ContinuousLinearMap.id ℂ H →
    ∀ rho sigma, stateOp b sigma = U.comp ((stateOp b rho).comp U.adjoint) →
      f sigma = f rho

/-- PDF p.16: independent relative-entropy infima for countably atomic and arbitrary laws.
The Bool selects the domain, not an assumed equality between the two infima. -/
def stateRelativeDefect (b : HilbertBasis I ℂ H) (k : ℕ) (atomic : Bool)
    (rho : QuantumState b) : ℝ≥0∞ :=
  sInf {v | ∃ mu ∈ stateFiber b (rankStates b k) rho,
    (atomic = true → AtomicProbability mu) ∧
    v = ∫⁻ sigma : rankStates b k, relativeEntropy sigma.val.val rho.val ∂(mu : Measure _)}

/-- PDF p.7: a countable probability vector; total variation is used when this domain is topologized. -/
def CountableProbabilityWeights (w : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ Summable w ∧ (∑' i, w i) = 1

/-- PDF p.17: homogeneous classical entropy on nonnegative summable sequences.
Normalization and the prefactor preserve the correction -eta(total mass). -/
def homogeneousClassicalEntropy (w : ℕ → ℝ) : ℝ≥0∞ :=
  let t := ∑' i, w i
  ENNReal.ofReal t * ∑' i, ENNReal.ofReal (entropyWeight (w i / t))

/-- PDF p.24: uniform homogeneous entropy tails for the restricted weight set.
Coordinate i here is source coordinate i+1; dropping finitely many initial orders
leaves precisely the source's limit with tail i>m. -/
def UniformWeightTails (P : Set (ℕ → ℝ)) : Prop :=
  (∀ w ∈ P, CountableProbabilityWeights w) ∧
    Tendsto (fun m : ℕ => ⨆ w : P,
      homogeneousClassicalEntropy (fun i => if m < i then w.val i else 0)) atTop (nhds 0)

/-- PDF p.24: actual restricted countable convex averages, with trace-norm convergence. -/
def restrictedConeHull (b : HilbertBasis I ℂ H) (A : Set (PositiveCone H))
    (P : Set (ℕ → ℝ)) : Set (PositiveCone H) :=
  {T | ∃ w ∈ P, ∃ s : ℕ → PositiveCone H,
    (∀ i, s i ∈ A) ∧ ConeEnsemble b (coneOp T) w s}

/-- PDF p.32: each A_i is shared across all its m conjugations; contractions are independent. -/
def contractionSumSet {n m : ℕ} (A : Fin n → Set (PositiveCone H)) :
    Set (PositiveCone H) :=
  {T | ∃ s : Fin n → PositiveCone H, ∃ V : Fin n → Fin m → (H →L[ℂ] H),
    (∀ i, s i ∈ A i) ∧ (∀ i j, ‖V i j‖ ≤ 1) ∧
    coneOp T = ∑ i, ∑ j, (V i j).comp ((coneOp (s i)).comp (V i j).adjoint)}

example : homogeneousClassicalEntropy (fun _ => 0) = 0 := by
  simp [homogeneousClassicalEntropy]

example (b : HilbertBasis I ℂ H) (A : Set (PositiveCone H)) :
    restrictedConeHull b A ∅ = ∅ := by
  ext T
  simp [restrictedConeHull]

section Statements

variable [hsep : TopologicalSpace.SeparableSpace H] [hI : Countable I]
include hsep hI

end Statements

end Operators

/-- Appendix 7.2, PDF p.38: reuse the accepted natural-log entropy weight. -/
abbrev scalarEta (x : ℝ) : ℝ := entropyWeight x

/-- Appendix 7.2, PDF p.38: positive part of the real l1 unit ball.
An ENNReal mass bound enforces summability and coordinate bounds 0 <= x_j <= 1. -/
def PositiveL1Ball : Set (ℕ → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ (∑' j, ENNReal.ofReal (x j)) ≤ 1}

/-- Appendix 7.2, PDF p.38: convergence exponent; empty admissible set has infimum infinity. -/
def convergenceExponent (h : ℕ → ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ lam : ℝ, 0 < lam ∧
    Summable (fun j : ℕ => Real.exp (-lam * h j)) ∧ r = ENNReal.ofReal lam}

/-- Appendix 7.2, PDF p.38: supremum of unnormalized entropy tails on the submass ball.
Lean coordinate j represents source coordinate j+1, so source tail >=m+1 is j>=m. -/
def weightedEntropyTail (h : ℕ → ℝ) (m : ℕ) : ℝ≥0∞ :=
  ⨆ x : PositiveL1Ball, ∑' j : ℕ,
    if m ≤ j then ENNReal.ofReal (scalarEta (x.val j) / h j) else 0

example : scalarEta 0 = 0 := by simp [scalarEta, entropyWeight]

example : scalarEta 1 = 0 := by simp [scalarEta, entropyWeight]

example : (fun _ : ℕ => (0 : ℝ)) ∈ PositiveL1Ball := by simp [PositiveL1Ball]

example (h : ℕ → ℝ) (m : ℕ) :
    (∑' j : ℕ, if m ≤ j then ENNReal.ofReal
      (scalarEta ((fun _ : ℕ => (0 : ℝ)) j) / h j) else 0) = 0 := by
  simp [scalarEta, entropyWeight]

end QAlgorithms.Papers.Independent.Support50.P34


