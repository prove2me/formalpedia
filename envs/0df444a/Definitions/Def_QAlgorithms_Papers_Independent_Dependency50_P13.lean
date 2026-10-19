-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
-- name    : QAlgorithms_Papers_Independent_Dependency50_P13
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:09:22.439749+00:00
-- url     : https://prove2.me/theorems/4a228bcb-b9ba-4747-bf7e-2a8f59103921
-- title:
--   Definitions for Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme
-- statement:
--   The objects the formalized statements of *Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme* (arXiv:2105.08091) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `NuclearRepresentation`: PDF p.4: absolutely summable rank-one representation. Inner is conjugate linear first.
--   - `IsTraceClass`: PDF p.4: on a Hilbert space nuclear operators are precisely trace-class operators.
--   - `TraceClass`: PDF p.4: the full trace-class operator space, without positivity or normalization.
--   - `traceNormValue`: PDF p.4: trace norm as the nuclear norm. The extended infimum is finite on the trace-class operators and their differences where this real-valued function is used.
--   - `IsPositive`: PDF p.4: positivity includes self-adjointness. A real-part inequality alone is insufficient.
--   - `operatorTrace`: PDF p.4: basis trace. Used only on trace-class operators or their bounded products, where the complex series is absolutely summable, independently of the chosen Hilbert basis.
--   - `State`: PDF p.4: states are positive trace-class operators of trace one.
--   - `entropyWeight`: PDF p.5, (2): continuous spectral entropy weight, with 0 log 0 equal to zero.
--   - `stateEntropy`: PDF p.5, (2): extended von Neumann entropy in nats, on normalized states. The positive bounded operator f(rho), f(x)=-x log x, need not be trace-class. Its nonnegative diagonal trace is therefore summed in ENNReal, retaining infinity.
--   - `stateEntropyBits`: PDF p.5, (2), with the explicit change of logarithm base for downstream interfaces. Division is by the positive finite constant ln 2, preserving infinite entropy.
--   - `spectralEnergy`: PDF pp.8,28: extended mean energy for an actual nonnegative diagonal Hamiltonian in its complete eigenbasis. The unbounded observable is encoded by its eigenvalues; no finite-energy restriction is imposed on the state.
--   - `meanPhotonNumber`: PDF p.23, (95): single-mode extended mean photon number in the number basis.
--   - `PositiveTraceClass`: PDF p.4: positive operators need not have trace one or trace at most one.
--   - `CompactTest`: PDF p.4: compact, rather than arbitrary bounded, weak-star test operators.
--   - `weakStarTopology`: PDF p.4: initial topology of all compact trace pairings.
--   - `traceNormTopology`: PDF p.4: initial topology of distances to all centres, hence exactly trace-norm topology.
--   - `stateTraceNormTopology`: PDF p.4: restriction of trace-norm topology to normalized states.
--   - `freeCone`: PDF pp.4,7: ray-generated cone, including when F is nonconvex; no convex hull is inserted.
--   - `ConvexStates`: PDF p.7: convexity in the underlying real vector space of operators.
--   - `WeakStarClosedCone`: PDF p.7: cone closedness in the full compact-test weak-star topology.
--   - `TraceClosedStates`: PDF p.8: trace-norm closedness of a state set.
--   - `TraceCompactStates`: PDF p.7: trace-norm compactness of a state set.
--   - `finiteRelativeEntropy`: PDF p.5, (3): finite-dimensional extended relative entropy on positive operators. qRelEntropy includes Tr(Y-X); kernel inclusion enforces support inclusion.
--   - `compression`: PDF p.6, proof of Lemma 4: matrix of a finite-projector compression.
--   - `relativeEntropy`: PDF pp.5–6, (3),(8): extended spectral relative entropy via the source's equivalent finite-projection formula. Rank zero contributes 0. The supremum retains infinity. Its equivalence to (3) is used by the source before the semicontinuity argument.
--   - `resourceDistance`: PDF p.6, (9): extended resource distance; the empty infimum equals infinity.
--   - `minimisers`: PDF p.7: the actual attaining free states.
--   - `ResourceLowerSemicontinuous`: PDF p.7, (10): lower semicontinuity for the trace-norm state topology.
--   - `TraceTendsto`: PDF p.4: trace-norm convergence of states.
--   - `conjugateOperator`: PDF p.8: compression T maps to M T M-adjoint.
--   - `PreservesCone`: PDF p.8, Theorem 7(iii): M preserves the entire cone.
--   - `firstNumberEnergy`: PDF p.8, Example 8: first-factor number energy in the product number basis (k,l). Summation over the second coordinate performs the partial trace. Divergent energy is infinity.
--   - `numberEnergyFreeSet`: PDF p.8, (11), at E=1: the counterexample's actual free set.
--   - `TraceLinearOperation`: PDF pp.16–17: a linear map on T(H), represented on ambient bounded operators. Only trace-class arguments constrain linearity and output; values elsewhere are irrelevant. Thus every linear map on T(H) has such a representation.
--   - `PositiveTraceNonIncreasing`: PDF p.16: positivity and trace decrease on all positive trace-class arguments.
--   - `FreeSubnormalisedOutputs`: PDF p.16, (62): free-state outputs lie in cone(F) intersected with the trace unit ball.
--   - `FiniteRankState`: PDF p.17: finite rank, without a uniform bound on rank.
--   - `TraceRelativelyCompact`: PDF p.18: relative compactness in trace norm.
--   - `TraceClusterPoint`: PDF p.18: cluster points along n tending to infinity, excluding isolated early terms.
--   - `bellState`: PDF p.19: Bell projector, reusing the accepted one-EPR-pair vector. The bijection Bool to (Fin 1 → Bool) sends a bit to the constant one-bit string.
--   - `qubitPairProjector`: PDF p.19, (74): computational-basis projector.
--   - `bellSigmaOne`: PDF p.19, (74): first closest separable state, full rank.
--   - `bellSigmaTwo`: PDF p.19, (74): second closest separable state, rank three.
--   - `twoQubitRelativeEntropy`: PDF p.19, (75): support-aware two-qubit relative entropy, in nats.
--   - `twoQubitEntanglement`: PDF p.18, (71),(72): two-qubit REE. In finite dimensions the finite convex hull of product density matrices equals the closed convex hull of pure products.
--   - `operatorResolvent`: PDF p.41, (A3): bounded resolvent. For positive T and s>0, T+sI is invertible. Ring.inverse returns the bounded algebra inverse in precisely that domain.
--   - `traceCrossEntropy`: PDF p.41, (A3): cross entropy of a state with a positive operator C<=I, as an extended nonnegative resolvent integral. This retains infinity at support failure.
--   - `traceResolventIntegrand`: PDF p.40, (A2), and p.13, (44): scalar trace-resolvent integrand. No bounded operator-valued logarithmic derivative is postulated.
--   - `traceGamma`: PDF p.40, (A2): scalar Gamma functional. Its integrability is a theorem conclusion, so no zero default for a nonintegrable Bochner integral is used to assert finiteness.
--   - `operatorMixture`: PDF p.40: the constructed convex interpolation of xi and xi-prime.
--   - `logDifferenceQuotient`: PDF p.40, (A1),(A2): cross-entropy difference quotient, with the source's sign. It is used only for 0<lambda<1 with finite cross entropy at xi; the interpolated cross entropy is then finite as concluded in Lemma 42.
-- source:
--   Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme, arXiv:2105.08091v3, https://arxiv.org/abs/2105.08091v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability

/-!
Paper-local operator model for arXiv:2105.08091v3, Sections II and III.
Nuclear representations give the actual trace-class operators on a complex Hilbert space.
Their nuclear norm equals the trace norm. Weak star tests compact operators only.
Relative entropy uses the finite-projection representation (8), PDF p.6, including
Tr(Y-X) and infinity on support failure. No unbounded cfc logarithm is used.
The countable Hilbert basis is a coordinate convention, not a spectral assumption.
Deferred nodes are recorded in the unit's GAPS.json. Compilation is pending handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P13

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.4: absolutely summable rank-one representation. Inner is conjugate linear first. -/
def NuclearRepresentation (T : H →L[ℂ] H) (u v : ℕ → H) : Prop :=
  Summable (fun r => ‖u r‖ * ‖v r‖) ∧
    ∀ x, T x = ∑' r, (inner ℂ (v r) x) • u r

/-- PDF p.4: on a Hilbert space nuclear operators are precisely trace-class operators. -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ u v : ℕ → H, NuclearRepresentation T u v

/-- PDF p.4: the full trace-class operator space, without positivity or normalization. -/
abbrev TraceClass (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] := {T : H →L[ℂ] H // IsTraceClass T}

/-- PDF p.4: trace norm as the nuclear norm. The extended infimum is finite on the
trace-class operators and their differences where this real-valued function is used. -/
def traceNormValue (T : H →L[ℂ] H) : ℝ :=
  (sInf {c : ℝ≥0∞ | ∃ u v : ℕ → H, NuclearRepresentation T u v ∧
    c = ∑' r, ENNReal.ofReal (‖u r‖ * ‖v r‖)}).toReal

/-- PDF p.4: positivity includes self-adjointness. A real-part inequality alone is insufficient. -/
def IsPositive (T : H →L[ℂ] H) : Prop :=
  T.adjoint = T ∧ ∀ x, 0 ≤ (inner ℂ x (T x)).re

/-- PDF p.4: basis trace. Used only on trace-class operators or their bounded products,
where the complex series is absolutely summable, independently of the chosen Hilbert basis. -/
def operatorTrace {I : Type*} (b : HilbertBasis I ℂ H) (T : H →L[ℂ] H) : ℂ :=
  ∑' i, inner ℂ (b i) (T (b i))

/-- PDF p.4: states are positive trace-class operators of trace one. -/
abbrev State {I : Type*} (b : HilbertBasis I ℂ H) :=
  {T : TraceClass H // IsPositive T.val ∧ operatorTrace b T.val = 1}

/-- PDF p.5, (2): continuous spectral entropy weight, with 0 log 0 equal to zero. -/
def entropyWeight (x : ℝ) : ℝ := -x * Real.log x

/-- PDF p.5, (2): extended von Neumann entropy in nats, on normalized states.
The positive bounded operator f(rho), f(x)=-x log x, need not be trace-class.
Its nonnegative diagonal trace is therefore summed in ENNReal, retaining infinity. -/
def stateEntropy {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal
    (inner ℂ (b i) ((cfc entropyWeight rho.val.val) (b i))).re

/-- PDF p.5, (2), with the explicit change of logarithm base for downstream interfaces.
Division is by the positive finite constant ln 2, preserving infinite entropy. -/
def stateEntropyBits {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b) : ℝ≥0∞ :=
  stateEntropy b rho / ENNReal.ofReal (Real.log 2)

/-- PDF pp.8,28: extended mean energy for an actual nonnegative diagonal Hamiltonian
in its complete eigenbasis. The unbounded observable is encoded by its eigenvalues;
no finite-energy restriction is imposed on the state. -/
def spectralEnergy {I : Type*} (b : HilbertBasis I ℂ H) (energy : I → ℝ≥0)
    (rho : State b) : ℝ≥0∞ :=
  ∑' i, (energy i : ℝ≥0∞) * ENNReal.ofReal (inner ℂ (b i) (rho.val.val (b i))).re

/-- PDF p.23, (95): single-mode extended mean photon number in the number basis. -/
def meanPhotonNumber (b : HilbertBasis ℕ ℂ H) (rho : State b) : ℝ≥0∞ :=
  spectralEnergy b (fun n => (n : ℝ≥0)) rho

example : entropyWeight 0 = 0 := by simp [entropyWeight]

example : entropyWeight 1 = 0 := by simp [entropyWeight]

/-- PDF p.4: positive operators need not have trace one or trace at most one. -/
abbrev PositiveTraceClass (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] := {T : TraceClass H // IsPositive T.val}

/-- PDF p.4: compact, rather than arbitrary bounded, weak-star test operators. -/
abbrev CompactTest (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] := {K : H →L[ℂ] H // IsCompactOperator K}

/-- PDF p.4: initial topology of all compact trace pairings. -/
def weakStarTopology {I : Type*} (b : HilbertBasis I ℂ H) : TopologicalSpace (TraceClass H) :=
  TopologicalSpace.induced
    (fun T : TraceClass H => fun K : CompactTest H => operatorTrace b (T.val.comp K.val))
    inferInstance

/-- PDF p.4: initial topology of distances to all centres, hence exactly trace-norm topology. -/
def traceNormTopology : TopologicalSpace (TraceClass H) :=
  TopologicalSpace.induced
    (fun T : TraceClass H => fun S : TraceClass H => traceNormValue (T.val - S.val))
    inferInstance

/-- PDF p.4: restriction of trace-norm topology to normalized states. -/
def stateTraceNormTopology {I : Type*} (b : HilbertBasis I ℂ H) : TopologicalSpace (State b) :=
  @TopologicalSpace.induced (State b) (TraceClass H) (fun rho => rho.val) traceNormTopology

/-- PDF pp.4,7: ray-generated cone, including when F is nonconvex; no convex hull is inserted. -/
def freeCone {I : Type*} {b : HilbertBasis I ℂ H} (F : Set (State b)) : Set (TraceClass H) :=
  {T | ∃ a : ℝ, 0 ≤ a ∧ ∃ sigma ∈ F, T.val = (a : ℂ) • sigma.val.val}

/-- PDF p.7: convexity in the underlying real vector space of operators. -/
def ConvexStates {I : Type*} {b : HilbertBasis I ℂ H} (F : Set (State b)) : Prop :=
  Convex ℝ {T : H →L[ℂ] H | ∃ sigma ∈ F, T = sigma.val.val}

/-- PDF p.7: cone closedness in the full compact-test weak-star topology. -/
def WeakStarClosedCone {I : Type*} {b : HilbertBasis I ℂ H} (F : Set (State b)) : Prop :=
  letI : TopologicalSpace (TraceClass H) := weakStarTopology b
  IsClosed (freeCone F)

/-- PDF p.8: trace-norm closedness of a state set. -/
def TraceClosedStates {I : Type*} {b : HilbertBasis I ℂ H} (F : Set (State b)) : Prop :=
  letI : TopologicalSpace (State b) := stateTraceNormTopology b
  IsClosed F

/-- PDF p.7: trace-norm compactness of a state set. -/
def TraceCompactStates {I : Type*} {b : HilbertBasis I ℂ H} (F : Set (State b)) : Prop :=
  letI : TopologicalSpace (State b) := stateTraceNormTopology b
  IsCompact F

/-- PDF p.5, (3): finite-dimensional extended relative entropy on positive operators.
qRelEntropy includes Tr(Y-X); kernel inclusion enforces support inclusion. -/
def finiteRelativeEntropy {J : Type*} [Fintype J] [DecidableEq J] (X Y : Matrix J J ℂ) : ℝ≥0∞ :=
  if LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin then
    ENNReal.ofReal (QAlgorithms.qRelEntropy X Y)
  else ⊤

/-- PDF p.6, proof of Lemma 4: matrix of a finite-projector compression. -/
def compression {n : ℕ} (v : Fin n → H) (T : H →L[ℂ] H) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => inner ℂ (v i) (T (v j))

/-- PDF pp.5–6, (3),(8): extended spectral relative entropy via the source's equivalent
finite-projection formula. Rank zero contributes 0. The supremum retains infinity.
Its equivalence to (3) is used by the source before the semicontinuity argument. -/
def relativeEntropy (X Y : TraceClass H) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ v : {v : Fin n → H // Orthonormal ℂ v},
    finiteRelativeEntropy (compression v.val X.val) (compression v.val Y.val)

/-- PDF p.6, (9): extended resource distance; the empty infimum equals infinity. -/
def resourceDistance {I : Type*} {b : HilbertBasis I ℂ H} (F : Set (State b))
    (rho : State b) : ℝ≥0∞ :=
  ⨅ sigma : F, relativeEntropy rho.val sigma.val.val

/-- PDF p.7: the actual attaining free states. -/
def minimisers {I : Type*} {b : HilbertBasis I ℂ H} (F : Set (State b))
    (rho : State b) : Set (State b) :=
  {sigma | sigma ∈ F ∧ relativeEntropy rho.val sigma.val = resourceDistance F rho}

/-- PDF p.7, (10): lower semicontinuity for the trace-norm state topology. -/
def ResourceLowerSemicontinuous {I : Type*} {b : HilbertBasis I ℂ H}
    (F : Set (State b)) : Prop :=
  letI : TopologicalSpace (State b) := stateTraceNormTopology b
  LowerSemicontinuous (resourceDistance F)

/-- PDF p.4: trace-norm convergence of states. -/
def TraceTendsto {I : Type*} {b : HilbertBasis I ℂ H}
    (rhoSeq : ℕ → State b) (rho : State b) : Prop :=
  letI : TopologicalSpace (State b) := stateTraceNormTopology b
  Tendsto rhoSeq atTop (nhds rho)

/-- PDF p.8: compression T maps to M T M-adjoint. -/
def conjugateOperator (M T : H →L[ℂ] H) : H →L[ℂ] H :=
  M.comp (T.comp M.adjoint)

/-- PDF p.8, Theorem 7(iii): M preserves the entire cone. -/
def PreservesCone {I : Type*} {b : HilbertBasis I ℂ H}
    (F : Set (State b)) (M : H →L[ℂ] H) : Prop :=
  ∀ T ∈ freeCone F, ∃ S ∈ freeCone F, S.val = conjugateOperator M T.val

/-- PDF p.8, Example 8: first-factor number energy in the product number basis (k,l).
Summation over the second coordinate performs the partial trace. Divergent energy is infinity. -/
def firstNumberEnergy (b : HilbertBasis (ℕ × ℕ) ℂ H) (rho : State b) : ℝ≥0∞ :=
  spectralEnergy b (fun p => (p.1 : ℝ≥0)) rho

/-- PDF p.8, (11), at E=1: the counterexample's actual free set. -/
def numberEnergyFreeSet (b : HilbertBasis (ℕ × ℕ) ℂ H) : Set (State b) :=
  {rho | firstNumberEnergy b rho ≤ 1}

/-- PDF pp.16–17: a linear map on T(H), represented on ambient bounded operators.
Only trace-class arguments constrain linearity and output; values elsewhere are irrelevant.
Thus every linear map on T(H) has such a representation. -/
def TraceLinearOperation (Phi : (H →L[ℂ] H) → (H →L[ℂ] H)) : Prop :=
  (∀ T, IsTraceClass T → IsTraceClass (Phi T)) ∧
  (∀ S T, IsTraceClass S → IsTraceClass T → Phi (S + T) = Phi S + Phi T) ∧
  (∀ a : ℂ, ∀ T, IsTraceClass T → Phi (a • T) = a • Phi T)

/-- PDF p.16: positivity and trace decrease on all positive trace-class arguments. -/
def PositiveTraceNonIncreasing {I : Type*} (b : HilbertBasis I ℂ H)
    (Phi : (H →L[ℂ] H) → (H →L[ℂ] H)) : Prop :=
  TraceLinearOperation Phi ∧ ∀ T, IsTraceClass T → IsPositive T →
    IsPositive (Phi T) ∧ (operatorTrace b (Phi T)).re ≤ (operatorTrace b T).re

/-- PDF p.16, (62): free-state outputs lie in cone(F) intersected with the trace unit ball. -/
def FreeSubnormalisedOutputs {I : Type*} {b : HilbertBasis I ℂ H}
    (F : Set (State b)) (Phi : (H →L[ℂ] H) → (H →L[ℂ] H)) : Prop :=
  ∀ sigma ∈ F, ∃ T ∈ freeCone F,
    T.val = Phi sigma.val.val ∧ (operatorTrace b T.val).re ≤ 1

/-- PDF p.17: finite rank, without a uniform bound on rank. -/
def FiniteRankState {I : Type*} {b : HilbertBasis I ℂ H} (rho : State b) : Prop :=
  FiniteDimensional ℂ (LinearMap.range rho.val.val.toLinearMap)

/-- PDF p.18: relative compactness in trace norm. -/
def TraceRelativelyCompact {I : Type*} {b : HilbertBasis I ℂ H}
    (sigma : ℕ → State b) : Prop :=
  letI : TopologicalSpace (State b) := stateTraceNormTopology b
  IsCompact (closure (Set.range sigma))

/-- PDF p.18: cluster points along n tending to infinity, excluding isolated early terms. -/
def TraceClusterPoint {I : Type*} {b : HilbertBasis I ℂ H}
    (sigma : ℕ → State b) (tau : State b) : Prop :=
  letI : TopologicalSpace (State b) := stateTraceNormTopology b
  MapClusterPt tau atTop sigma

example : IsTraceClass (0 : H →L[ℂ] H) := by
  refine ⟨0, 0, ?_, ?_⟩
  · simp
  · intro x
    simp

example {I : Type*} (b : HilbertBasis I ℂ H) : operatorTrace b 0 = 0 := by
  simp [operatorTrace]

example {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ)
    (h : ¬ LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) :
    finiteRelativeEntropy X Y = ⊤ := by
  simp [finiteRelativeEntropy, h]

example {I : Type*} {b : HilbertBasis I ℂ H} (rho : State b) :
    resourceDistance (∅ : Set (State b)) rho = ⊤ := by
  simp [resourceDistance]

/-- PDF p.19: Bell projector, reusing the accepted one-EPR-pair vector.
The bijection Bool to (Fin 1 → Bool) sends a bit to the constant one-bit string. -/
def bellState : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  QAlgorithms.pureDensity (WithLp.toLp 2 fun p : Bool × Bool =>
    QAlgorithms.maxEntangled 1 ((fun _ => p.1), (fun _ => p.2)))

/-- PDF p.19, (74): computational-basis projector. -/
def qubitPairProjector (p : Bool × Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun i j => if i = p ∧ j = p then 1 else 0

/-- PDF p.19, (74): first closest separable state, full rank. -/
def bellSigmaOne : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (1 / 2 : ℂ) • bellState + (1 / 6 : ℂ) • (1 - bellState)

/-- PDF p.19, (74): second closest separable state, rank three. -/
def bellSigmaTwo : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (1 / 2 : ℂ) • bellState + (1 / 4 : ℂ) •
    (qubitPairProjector (false, true) + qubitPairProjector (true, false))

/-- PDF p.19, (75): support-aware two-qubit relative entropy, in nats. -/
def twoQubitRelativeEntropy (rho sigma : Matrix (Bool × Bool) (Bool × Bool) ℂ) : ℝ≥0∞ :=
  finiteRelativeEntropy rho sigma

/-- PDF p.18, (71),(72): two-qubit REE. In finite dimensions the finite convex hull
of product density matrices equals the closed convex hull of pure products. -/
def twoQubitEntanglement (rho : Matrix (Bool × Bool) (Bool × Bool) ℂ) : ℝ≥0∞ :=
  ⨅ sigma : {sigma : Matrix (Bool × Bool) (Bool × Bool) ℂ //
      QAlgorithms.Entanglement.IsSeparableDensity sigma},
    twoQubitRelativeEntropy rho sigma.val

example : qubitPairProjector (false, true) (false, true) (false, true) = 1 := by
  simp [qubitPairProjector]

example : qubitPairProjector (false, true) (true, false) (true, false) = 0 := by
  simp [qubitPairProjector]

/-- PDF p.41, (A3): bounded resolvent. For positive T and s>0, T+sI is invertible.
Ring.inverse returns the bounded algebra inverse in precisely that domain. -/
def operatorResolvent (T : H →L[ℂ] H) (s : ℝ) : H →L[ℂ] H :=
  Ring.inverse (T + (s : ℂ) • ContinuousLinearMap.id ℂ H)

/-- PDF p.41, (A3): cross entropy of a state with a positive operator C<=I, as an
extended nonnegative resolvent integral. This retains infinity at support failure. -/
def traceCrossEntropy {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b)
    (C : H →L[ℂ] H) : ℝ≥0∞ :=
  ∫⁻ s : ℝ in Set.Ioi 0, ENNReal.ofReal
    (operatorTrace b (rho.val.val.comp
      (operatorResolvent C s - ((1 + s)⁻¹ : ℂ) • ContinuousLinearMap.id ℂ H))).re

/-- PDF p.40, (A2), and p.13, (44): scalar trace-resolvent integrand.
No bounded operator-valued logarithmic derivative is postulated. -/
def traceResolventIntegrand {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b)
    (xi X : H →L[ℂ] H) (s : ℝ) : ℝ :=
  (operatorTrace b (rho.val.val.comp
    ((operatorResolvent xi s).comp (X.comp (operatorResolvent xi s))))).re

/-- PDF p.40, (A2): scalar Gamma functional. Its integrability is a theorem conclusion,
so no zero default for a nonintegrable Bochner integral is used to assert finiteness. -/
def traceGamma {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b)
    (xi X : H →L[ℂ] H) : ℝ :=
  ∫ s : ℝ in Set.Ioi 0, traceResolventIntegrand b rho xi X s

/-- PDF p.40: the constructed convex interpolation of xi and xi-prime. -/
def operatorMixture (xi xiPrime : H →L[ℂ] H) (lam : ℝ) : H →L[ℂ] H :=
  ((1 - lam : ℝ) : ℂ) • xi + (lam : ℂ) • xiPrime

/-- PDF p.40, (A1),(A2): cross-entropy difference quotient, with the source's sign.
It is used only for 0<lambda<1 with finite cross entropy at xi; the interpolated
cross entropy is then finite as concluded in Lemma 42. -/
def logDifferenceQuotient {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b)
    (xi xiPrime : H →L[ℂ] H) (lam : ℝ) : ℝ :=
  ((traceCrossEntropy b rho (operatorMixture xi xiPrime lam)).toReal -
    (traceCrossEntropy b rho xi).toReal) / lam

example {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b)
    (xi : H →L[ℂ] H) (s : ℝ) : traceResolventIntegrand b rho xi 0 s = 0 := by
  simp [traceResolventIntegrand, operatorTrace]

end QAlgorithms.Papers.Independent.Dependency50.P13


