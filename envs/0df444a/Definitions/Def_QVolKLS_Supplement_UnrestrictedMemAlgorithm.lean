-- Prove2me | Definitions.Def_QVolKLS_Supplement_UnrestrictedMemAlgorithm
-- name    : QVolKLS_Supplement_UnrestrictedMemAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:34:05.743299+00:00
-- url     : https://prove2.me/theorems/09ca3b40-f3f4-44a1-a343-9989ae18371b
-- title:
--   Unrestricted finite-precision quantum membership-query algorithms
-- statement:
--   An **unrestricted finite-precision membership-query algorithm** in dimension $d$ is a finite quantum circuit with arbitrary input-independent unitary computation, arbitrary workspace, and finitely many dyadic coordinate formats. Its only body-dependent operations are exact coherent membership queries. A final computational-basis measurement is decoded by an arbitrary real-valued output function.
--
--   The module defines the total membership-query count, output probabilities, the relative-volume-error event, and the promise class of origin-centered ellipsoids
--   $$
--   B(0,1/2)\subseteq K\subseteq B(0,Cd^2).
--   $$
--
--   This is the unrestricted query model and hard-instance class of Theorem 7.3.
--
--   **Formalization Note** Intermediate measurements, adaptivity, and classical control are represented by deferred measurement. There is no fixed gate set, running-time bound, or common precision requirement; the body enters only through the exact coherent oracle, including boundary points.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §2.4, p.23; Theorem 7.3, pp.57-58

import Definitions.Def_QVolKLS_memOracle
import Definitions.Def_QVolKLS_fourthMomentNorm

set_option autoImplicit false

namespace QVolKLS.Supplement

open QAlgorithms MeasureTheory

/-!
# Unrestricted finite-precision membership-query algorithms and ellipsoid promises

R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…), §2.4, p.23 and Theorem 7.3,
p.57.

**Formalization Note.** `UnrestrictedMemAlgorithm` uses arbitrary unitary gates between exact
coherent membership-oracle calls and permits finitely many coordinate formats, each with arbitrary
finite precision. Intermediate measurements and adaptive classical control are represented by
deferred measurement, retaining the outcome in workspace; this is the model used in the proof of
Lemma 7.1, p.55. The final output decoding is an arbitrary real-valued function of the measured
basis outcome. Thus no gate set, fixed precision, nonadaptivity, or running-time restriction is
imposed. `OriginEllipsoidPromise` uses an invertible real matrix to define an ellipsoid centered at
the origin and includes the two ball containments printed in Theorem 7.3.
-/

/-- An unrestricted finite-precision quantum membership-query algorithm in dimension `d`.
The only body-dependent operations are exact coherent membership queries. -/
structure UnrestrictedMemAlgorithm (d : ℕ) where
  /-- Number of qubits. -/
  N : ℕ
  /-- Number of finite coordinate formats. -/
  s : ℕ
  /-- Format `(b,p)`: `b` two's-complement bits per coordinate and scale `2⁻ᵖ`. -/
  fmt : Fin s → ℕ × ℕ
  /-- Arbitrary input-independent unitaries interspersed with membership-oracle calls. -/
  circuit : OracleCircuit unitaryGateSet (fun k : Fin s ↦ d * (fmt k).1 + 1) N
  /-- Arbitrary output decoding after the final measurement. -/
  output : Qubits N → ℝ

namespace UnrestrictedMemAlgorithm

variable {d : ℕ}

/-- Worst-case query count (the circuit shape is body-independent). -/
def queries (A : UnrestrictedMemAlgorithm d) : ℕ :=
  ∑ k, A.circuit.queryCount k

/-- Final state on body `K`. -/
noncomputable def finalState (A : UnrestrictedMemAlgorithm d) (K : Set (Euc d)) :
    EuclideanSpace ℂ (Qubits A.N) :=
  act (A.circuit.unitary (fun k ↦ memOracle K (A.fmt k).1 (A.fmt k).2)) (zeroKet A.N)

/-- Probability that the real output lies in `S`. -/
noncomputable def outProb (A : UnrestrictedMemAlgorithm d) (K : Set (Euc d)) (S : Set ℝ) : ℝ :=
  haveI := Classical.decPred (fun z : Qubits A.N ↦ A.output z ∈ S)
  probEvent (A.finalState K) (fun z ↦ A.output z ∈ S)

end UnrestrictedMemAlgorithm

/-- The origin-centered ellipsoid `{x : xᵀ Bᵀ B x ≤ 1}` for an invertible real matrix `B`. -/
def IsOriginEllipsoid {d : ℕ} (K : Set (Euc d)) : Prop :=
  ∃ B : Matrix (Fin d) (Fin d) ℝ, B.det ≠ 0 ∧
    K = {x | ∑ i, (∑ j, B i j * x j) ^ 2 ≤ 1}

/-- The ellipsoid promise in Theorem 7.3: centered at zero, inner radius `1/2`, and outer radius
`C d²`. -/
def OriginEllipsoidPromise {d : ℕ} (C : ℝ) (K : Set (Euc d)) : Prop :=
  IsConvexBody K ∧ IsOriginEllipsoid K ∧
    Metric.closedBall (0 : Euc d) (1 / 2 : ℝ) ⊆ K ∧
    K ⊆ Metric.closedBall (0 : Euc d) (C * (d : ℝ) ^ 2)

/-- Relative-error event for a real estimate of the Lebesgue volume of `K`. -/
def volumeRelativeError {d : ℕ} (K : Set (Euc d)) (eps : ℝ) : Set ℝ :=
  {v | |v - (volume K).toReal| ≤ eps * (volume K).toReal}

end QVolKLS.Supplement


