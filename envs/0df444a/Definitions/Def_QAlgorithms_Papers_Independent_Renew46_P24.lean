-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24
-- name    : QAlgorithms_Papers_Independent_Renew46_P24
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:38:10.779303+00:00
-- url     : https://prove2.me/theorems/49e36df1-74d4-44da-8d43-1b16fb1f7f5c
-- title:
--   Definitions for Quantum Macrostates, Equivalence of Ensembles and an H-Theorem
-- statement:
--   The objects the formalized statements of *Quantum Macrostates, Equivalence of Ensembles and an H-Theorem* (arXiv:math-ph/0601027) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `volume`: PDF pp.3-4: positive physical volume; the thermodynamic index starts at one.
--   - `MacroscopicSystem`: PDF pp.3-4: observable data and the fixed radii of (2.3). The standing analytic and Hilbert-space assumptions are `IsMacroscopic`.
--   - `IsMacroscopic`: PDF pp.3-4: nonzero spaces, Hermitian observables, and a strict uniform operator-norm bound below each radius. No commutation or lattice hypothesis.
--   - `OperatorSequence`: PDF p.4: matrix sequences on the specified spaces.
--   - `IsStateSequence`: PDF p.6: every density is positive semidefinite and has ordinary trace one.
--   - `IsProjectionSequence`: PDF p.4, (2.2): projections must be nonzero before normalizing their trace.
--   - `traceExpectation`: PDF pp.6-7: the complex-valued state functional `Tr(rho A)`.
--   - `projectionDensity`: PDF p.4, (2.2): density of the normalized trace on a nonzero projection.
--   - `spectralWindow`: PDF pp.3,8: spectral projection on a closed interval. The indicator need only be continuous on the finite spectrum, not on the whole real line.
--   - `AnalyticTestSeries`: PDF p.4, (2.3): coefficients on arbitrary finite ordered words, absolutely summable with the fixed radii. No countability assumption on `K`.
--   - `wordOperator`: PDF p.4, (2.4): ordered monomial, with the empty word equal to the identity.
--   - `operatorEvaluation`: PDF p.4, (2.4): norm-convergent noncommutative analytic series.
--   - `scalarEvaluation`: PDF p.4, (2.5): scalar evaluation of the same ordered series.
--   - `singleVariableConcentrates`: PDF p.4, (2.1): all single-variable continuous tests concentrate.
--   - `projectionConcentrates`: PDF p.4, (2.1): nonzero projection traces concentrate at a real configuration.
--   - `stateConcentrates`: PDF p.6, (2.8): concentration of general states by all analytic tests. Normalization is imposed separately by `IsStateSequence`.
--   - `meanConcentrates`: PDF p.6: convergence in mean only; this is weaker than concentration.
--   - `densityEntropyNats`: PDF p.6, (2.10): natural-log von Neumann entropy, with `0 log 0 = 0`.
--   - `entropyDensity`: PDF pp.5-7: extended-real limsup of the entropy per positive volume.
--   - `projectionDimensionDensity`: PDF p.5, (2.6): extended-real logarithmic dimension density.
--   - `microcanonicalEntropy`: PDF p.5, (2.6): supremum OVER sequences, outside the limsup in volume. The empty feasible class has value minus infinity, and unbounded classes plus infinity.
--   - `canonicalEntropy`: PDF p.6, (2.9): entropy supremum over normalized concentrating states.
--   - `meanCanonicalEntropy`: PDF p.7, (2.11): entropy supremum over normalized mean-concentrating states.
--   - `microcanonicalMacrostate`: PDF p.5: a microcanonical macrostate attains the entropy supremum.
--   - `canonicalMacrostate`: PDF p.7: a canonical macrostate converges in mean and attains (2.11).
--   - `microcanonicalAdmissible`: PDF pp.5,12: the admissible microcanonical domain.
--   - `gibbsExponent`: PDF p.7, (2.14): fixed real coefficients and the PLUS-sign Gibbs exponent.
--   - `gibbsPartitionTrace`: PDF p.7, (2.14): the unnormalized partition function is a real positive trace.
--   - `gibbsFamily`: PDF p.7, (2.14): the Gibbs family is constructed from the observables.
--   - `exponentiallyConcentrates`: PDF p.8, (3.1): constants depend on coordinate and tolerance, never on volume.
--   - `scaledLogDensity`: PDF p.9, (3.4): scaled natural logarithm of the density.
--   - `centeredLogDensity`: PDF p.8, (3.2): centering subtracts a scalar multiple of the identity.
--   - `scaledLogMass`: PDF p.8, (3.2): log of zero mass is minus infinity, never `Real.log 0 = 0`.
--   - `asymptoticEquipartition`: PDF p.8, (3.2): subexponential mass of EVERY fixed positive centered window. This does not require the mass to tend to one.
--   - `generatingSequence`: PDF p.9, (3.3): the finite-volume generating function in natural units.
--   - `generatingFunction`: PDF p.9, (3.3): limit-defined generating function; existence is a theorem hypothesis on a neighborhood of zero, so the total limit's default is never used.
--   - `pressureSequence`: PDF pp.9-10, (3.6): finite-volume pressure.
--   - `pressure`: PDF pp.9-10, (3.6): the pressure is constructed by a limit, with local existence imposed explicitly in the pressure theorem.
--   - `relativeCanonicalEntropy`: PDF p.7, (2.12), as pinned by the proof on p.13: INF over mean-concentrating normalized sequences, followed by the volume liminf. The empty infimum is plus infinity.
--   - `relativeCanonicalMacrostate`: PDF p.13, proof of Theorem 4.2: a relative canonical macrostate MINIMIZES relative entropy density; it need not maximize ordinary entropy.
--   - `RelativeAdmissible`: PDF p.13: finite relative-entropy domain; the reference need not be faithful.
--   - `AutomorphismDynamics`: PDF p.12, (4.2): microscopic complex-linear unital star automorphisms.
--   - `AutomorphismCocycle`: PDF p.12, (4.2): composition order is exactly the printed Heisenberg order.
--   - `MacroscopicDynamics`: PDF pp.12-13: real-time two-parameter macroscopic maps.
--   - `microcanonicalAutonomy`: PDF p.12, (4.3): the SAME maximizing projection sequence for each x works for every analytic test and all intervals; maps preserve Omega.
--   - `macroscopicSemigroup`: PDF p.12, (4.4): semigroup condition on a specified invariant domain.
--   - `LinearDynamics`: PDF p.13, (4.5): microscopic Heisenberg maps on matrix algebras.
--   - `StationaryCPCocycle`: PDF p.13: completely positive, UNITAL, stationary microscopic cocycle. Unitality is the implicit Heisenberg convention needed to evolve normalized states.
--   - `meanAutonomy`: PDF p.13, (4.6): relative minimizers precede all coordinates and times. The macroscopic maps act on the finite-relative-entropy domain.
--   - `siteOperator`: PDF pp.5,14: a one-site matrix embedded in a tensor register. The frozen bit-index map fixes the orthonormal basis and wire order.
--   - `spinMagnetization`: PDF p.5, (2.7): the three Pauli averages on N spin-1/2 particles.
--   - `spinSystem`: PDF pp.5-6: the spin model, with fixed analytic radii 2 > 1.
--   - `magnetizationLength`: PDF p.6: Euclidean length of the three-component magnetization.
--   - `extendedEta`: PDF p.15, (4.10): extended eta, with zero endpoints and minus infinity outside [0,1]. All logarithms are natural.
--   - `kacAverage`: PDF p.14: two N-qubit registers; first scatterers, then spins. The density is divided by N, not by the total number 2N of qubits.
--   - `kacSystem`: PDF p.14: X_0 is the scatterer mean and X_1,X_2,X_3 the spin Pauli means.
--   - `kacConfiguration`: PDF p.14: x = (mu,m_1,m_2,m_3).
--   - `blochDensity`: PDF p.15: qubit density represented by its real Bloch vector.
--   - `kacChannel`: PDF p.15, (4.11): the explicit effective one-step Kac channel.
--   - `kacSpinStep`: PDF p.15: discrete macroscopic spin step, extracted from the reduced density.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, https://arxiv.org/abs/math-ph/0601027v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71

/-!
# Quantum Macrostates, Equivalence of Ensembles and an H-Theorem

De Roeck, Maes and Netocny, arXiv:math-ph/0601027v2.
All page references below are PDF pages. Sequence index `n` represents the
positive physical volume `N = n + 1`. Matrices use an orthonormal basis;
`specNorm` is the frozen Hilbert-space operator norm, not an entrywise norm.
General matrix primitives are reused from the pinned accepted library.
All new paper-specific definitions are local to this module. The three source
assertions deferred in HARD.md have no theorem here.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P24

open Filter
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

-- Exact primitives verified against the pinned accepted-library SHA256 catalogue.
open QAlgorithms.Papers.Independent.Information100.P23 (Operator)
open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction relativeEntropy)
open QAlgorithms.Papers.Independent.Information100.P10 (pauli)
open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3-4: positive physical volume; the thermodynamic index starts at one. -/
def volume (n : ℕ) : ℕ := n + 1

/-- PDF pp.3-4: observable data and the fixed radii of (2.3).
The standing analytic and Hilbert-space assumptions are `IsMacroscopic`. -/
structure MacroscopicSystem (K : Type*) where
  dimension : ℕ → ℕ
  observable : (n : ℕ) → K → Operator (dimension n)
  radius : K → ℝ

/-- PDF pp.3-4: nonzero spaces, Hermitian observables, and a strict uniform
operator-norm bound below each radius. No commutation or lattice hypothesis. -/
def IsMacroscopic {K : Type*} (S : MacroscopicSystem K) : Prop :=
  (∀ n, 0 < S.dimension n) ∧
  (∀ n k, (S.observable n k).IsHermitian) ∧
  ∀ k, ∃ B : ℝ, 0 ≤ B ∧ B < S.radius k ∧
    ∀ n, QAlgorithms.specNorm (S.observable n k) ≤ B

/-- PDF p.4: matrix sequences on the specified spaces. -/
abbrev OperatorSequence {K : Type*} (S : MacroscopicSystem K) :=
  (n : ℕ) → Operator (S.dimension n)

/-- PDF p.6: every density is positive semidefinite and has ordinary trace one. -/
def IsStateSequence {K : Type*} {S : MacroscopicSystem K}
    (rho : OperatorSequence S) : Prop :=
  ∀ n, QAlgorithms.IsDensityMatrix (rho n)

/-- PDF p.4, (2.2): projections must be nonzero before normalizing their trace. -/
def IsProjectionSequence {K : Type*} {S : MacroscopicSystem K}
    (P : OperatorSequence S) : Prop :=
  ∀ n, IsStarProjection (P n) ∧ P n ≠ 0

/-- PDF pp.6-7: the complex-valued state functional `Tr(rho A)`. -/
def traceExpectation {I : Type*} [Fintype I] [DecidableEq I]
    (rho A : Matrix I I ℂ) : ℂ := (rho * A).trace

/-- PDF p.4, (2.2): density of the normalized trace on a nonzero projection. -/
def projectionDensity {K : Type*} {S : MacroscopicSystem K}
    (P : OperatorSequence S) : OperatorSequence S :=
  fun n => (P n).trace⁻¹ • P n

/-- PDF pp.3,8: spectral projection on a closed interval. The indicator need
only be continuous on the finite spectrum, not on the whole real line. -/
def spectralWindow {d : ℕ} (A : Operator d) (a b : ℝ) : Operator d :=
  cfc (fun z : ℝ => if a ≤ z ∧ z ≤ b then (1 : ℝ) else 0) A

/-- PDF p.4, (2.3): coefficients on arbitrary finite ordered words, absolutely
summable with the fixed radii. No countability assumption on `K`. -/
structure AnalyticTestSeries {K : Type*} (S : MacroscopicSystem K) where
  coefficient : List K → ℂ
  summable : Summable (fun w : List K =>
    ‖coefficient w‖ * (w.map S.radius).prod)

/-- PDF p.4, (2.4): ordered monomial, with the empty word equal to the identity. -/
def wordOperator {K : Type*} {S : MacroscopicSystem K}
    (n : ℕ) (w : List K) : Operator (S.dimension n) :=
  (w.map (S.observable n)).prod

/-- PDF p.4, (2.4): norm-convergent noncommutative analytic series. -/
def operatorEvaluation {K : Type*} {S : MacroscopicSystem K}
    (G : AnalyticTestSeries S) (n : ℕ) : Operator (S.dimension n) :=
  ∑' w : List K, G.coefficient w • wordOperator n w

/-- PDF p.4, (2.5): scalar evaluation of the same ordered series. -/
def scalarEvaluation {K : Type*} {S : MacroscopicSystem K}
    (G : AnalyticTestSeries S) (x : K → ℝ) : ℂ :=
  ∑' w : List K, G.coefficient w * (w.map (fun k => (x k : ℂ))).prod

/-- PDF p.4, (2.1): all single-variable continuous tests concentrate. -/
def singleVariableConcentrates {K : Type*} (S : MacroscopicSystem K)
    (rho : OperatorSequence S) (x : K → ℝ) : Prop :=
  ∀ k (F : ℝ → ℂ), Continuous F →
    Tendsto (fun n => traceExpectation (rho n) (spectralFunction F (S.observable n k)))
      atTop (𝓝 (F (x k)))

/-- PDF p.4, (2.1): nonzero projection traces concentrate at a real configuration. -/
def projectionConcentrates {K : Type*} (S : MacroscopicSystem K)
    (P : OperatorSequence S) (x : K → ℝ) : Prop :=
  IsProjectionSequence P ∧ singleVariableConcentrates S (projectionDensity P) x

/-- PDF p.6, (2.8): concentration of general states by all analytic tests.
Normalization is imposed separately by `IsStateSequence`. -/
def stateConcentrates {K : Type*} (S : MacroscopicSystem K)
    (rho : OperatorSequence S) (x : K → ℝ) : Prop :=
  ∀ G : AnalyticTestSeries S,
    Tendsto (fun n => traceExpectation (rho n) (operatorEvaluation G n))
      atTop (𝓝 (scalarEvaluation G x))

/-- PDF p.6: convergence in mean only; this is weaker than concentration. -/
def meanConcentrates {K : Type*} (S : MacroscopicSystem K)
    (rho : OperatorSequence S) (x : K → ℝ) : Prop :=
  ∀ k, Tendsto (fun n => traceExpectation (rho n) (S.observable n k))
    atTop (𝓝 (x k : ℂ))

/-- PDF p.6, (2.10): natural-log von Neumann entropy, with `0 log 0 = 0`. -/
def densityEntropyNats {d : ℕ} (rho : Operator d) : ℝ :=
  -(cfc (fun z : ℝ => z * Real.log z) rho).trace.re

/-- PDF pp.5-7: extended-real limsup of the entropy per positive volume. -/
def entropyDensity {K : Type*} {S : MacroscopicSystem K}
    (rho : OperatorSequence S) : EReal :=
  Filter.limsup (fun n => (densityEntropyNats (rho n) / (volume n : ℝ) : EReal)) atTop

/-- PDF p.5, (2.6): extended-real logarithmic dimension density. -/
def projectionDimensionDensity {K : Type*} {S : MacroscopicSystem K}
    (P : OperatorSequence S) : EReal :=
  Filter.limsup (fun n =>
    (Real.log (P n).trace.re / (volume n : ℝ) : EReal)) atTop

/-- PDF p.5, (2.6): supremum OVER sequences, outside the limsup in volume.
The empty feasible class has value minus infinity, and unbounded classes plus infinity. -/
def microcanonicalEntropy {K : Type*} (S : MacroscopicSystem K) (x : K → ℝ) : EReal :=
  sSup {h | ∃ P : OperatorSequence S,
    projectionConcentrates S P x ∧ h = projectionDimensionDensity P}

/-- PDF p.6, (2.9): entropy supremum over normalized concentrating states. -/
def canonicalEntropy {K : Type*} (S : MacroscopicSystem K) (x : K → ℝ) : EReal :=
  sSup {h | ∃ rho : OperatorSequence S,
    IsStateSequence rho ∧ stateConcentrates S rho x ∧ h = entropyDensity rho}

/-- PDF p.7, (2.11): entropy supremum over normalized mean-concentrating states. -/
def meanCanonicalEntropy {K : Type*} (S : MacroscopicSystem K) (x : K → ℝ) : EReal :=
  sSup {h | ∃ rho : OperatorSequence S,
    IsStateSequence rho ∧ meanConcentrates S rho x ∧ h = entropyDensity rho}

/-- PDF p.5: a microcanonical macrostate attains the entropy supremum. -/
def microcanonicalMacrostate {K : Type*} (S : MacroscopicSystem K)
    (P : OperatorSequence S) (x : K → ℝ) : Prop :=
  projectionConcentrates S P x ∧
    projectionDimensionDensity P = microcanonicalEntropy S x

/-- PDF p.7: a canonical macrostate converges in mean and attains (2.11). -/
def canonicalMacrostate {K : Type*} (S : MacroscopicSystem K)
    (rho : OperatorSequence S) (x : K → ℝ) : Prop :=
  IsStateSequence rho ∧ meanConcentrates S rho x ∧
    entropyDensity rho = meanCanonicalEntropy S x

/-- PDF pp.5,12: the admissible microcanonical domain. -/
def microcanonicalAdmissible {K : Type*} (S : MacroscopicSystem K) (x : K → ℝ) : Prop :=
  0 ≤ microcanonicalEntropy S x

/-- PDF p.7, (2.14): fixed real coefficients and the PLUS-sign Gibbs exponent. -/
def gibbsExponent {q : ℕ} (S : MacroscopicSystem (Fin q))
    (lambda : Fin q → ℝ) (n : ℕ) : Operator (S.dimension n) :=
  (volume n : ℂ) • ∑ k, (lambda k : ℂ) • S.observable n k

/-- PDF p.7, (2.14): the unnormalized partition function is a real positive trace. -/
def gibbsPartitionTrace {q : ℕ} (S : MacroscopicSystem (Fin q))
    (lambda : Fin q → ℝ) (n : ℕ) : ℝ :=
  (NormedSpace.exp (gibbsExponent S lambda n)).trace.re

/-- PDF p.7, (2.14): the Gibbs family is constructed from the observables. -/
def gibbsFamily {q : ℕ} (S : MacroscopicSystem (Fin q))
    (lambda : Fin q → ℝ) : OperatorSequence S :=
  fun n => QAlgorithms.gibbsState (gibbsExponent S lambda n)

/-- PDF p.8, (3.1): constants depend on coordinate and tolerance, never on volume. -/
def exponentiallyConcentrates {K : Type*} (S : MacroscopicSystem K)
    (rho : OperatorSequence S) (x : K → ℝ) : Prop :=
  ∀ (delta : ℝ), 0 < delta → ∀ k, ∃ C : ℝ, 0 < C ∧
    ∃ n0 : ℕ, ∀ n > n0,
      1 - Real.exp (-C * (volume n : ℝ)) ≤
        (traceExpectation (rho n) (spectralWindow (S.observable n k)
          (x k - delta) (x k + delta))).re

/-- PDF p.9, (3.4): scaled natural logarithm of the density. -/
def scaledLogDensity {K : Type*} {S : MacroscopicSystem K}
    (rho : OperatorSequence S) : OperatorSequence S :=
  fun n => ((volume n : ℂ)⁻¹) • cfc Real.log (rho n)

/-- PDF p.8, (3.2): centering subtracts a scalar multiple of the identity. -/
def centeredLogDensity {K : Type*} {S : MacroscopicSystem K}
    (rho : OperatorSequence S) : OperatorSequence S :=
  fun n => scaledLogDensity rho n -
    traceExpectation (rho n) (scaledLogDensity rho n) • 1

/-- PDF p.8, (3.2): log of zero mass is minus infinity, never `Real.log 0 = 0`. -/
def scaledLogMass (n : ℕ) (p : ℝ) : EReal :=
  if 0 < p then (Real.log p / (volume n : ℝ) : EReal) else ⊥

/-- PDF p.8, (3.2): subexponential mass of EVERY fixed positive centered window.
This does not require the mass to tend to one. -/
def asymptoticEquipartition {K : Type*} {S : MacroscopicSystem K}
    (rho : OperatorSequence S) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    Tendsto (fun n => scaledLogMass n
      (traceExpectation (rho n)
        (spectralWindow (centeredLogDensity rho n) (-delta) delta)).re)
      atTop (𝓝 (0 : EReal))

/-- PDF p.9, (3.3): the finite-volume generating function in natural units. -/
def generatingSequence {K : Type*} (S : MacroscopicSystem K)
    (rho : OperatorSequence S) (k : K) (t : ℝ) (n : ℕ) : ℝ :=
  Real.log (traceExpectation (rho n)
    (NormedSpace.exp ((t * (volume n : ℝ) : ℂ) • S.observable n k))).re /
      (volume n : ℝ)

/-- PDF p.9, (3.3): limit-defined generating function; existence is a theorem
hypothesis on a neighborhood of zero, so the total limit's default is never used. -/
def generatingFunction {K : Type*} (S : MacroscopicSystem K)
    (rho : OperatorSequence S) (k : K) (t : ℝ) : ℝ :=
  Filter.limUnder atTop (generatingSequence S rho k t)

/-- PDF pp.9-10, (3.6): finite-volume pressure. -/
def pressureSequence {q : ℕ} (S : MacroscopicSystem (Fin q))
    (lambda : Fin q → ℝ) (n : ℕ) : ℝ :=
  Real.log (gibbsPartitionTrace S lambda n) / (volume n : ℝ)

/-- PDF pp.9-10, (3.6): the pressure is constructed by a limit, with local
existence imposed explicitly in the pressure theorem. -/
def pressure {q : ℕ} (S : MacroscopicSystem (Fin q)) (lambda : Fin q → ℝ) : ℝ :=
  Filter.limUnder atTop (pressureSequence S lambda)

/-- PDF p.7, (2.12), as pinned by the proof on p.13: INF over mean-concentrating
normalized sequences, followed by the volume liminf. The empty infimum is plus infinity. -/
def relativeCanonicalEntropy {K : Type*} (S : MacroscopicSystem K)
    (reference : OperatorSequence S) (x : K → ℝ) : EReal :=
  sInf {h | ∃ rho : OperatorSequence S,
    IsStateSequence rho ∧ meanConcentrates S rho x ∧
    h = Filter.liminf (fun n =>
      relativeEntropy (rho n) (reference n) / (volume n : EReal)) atTop}

/-- PDF p.13, proof of Theorem 4.2: a relative canonical macrostate MINIMIZES
relative entropy density; it need not maximize ordinary entropy. -/
def relativeCanonicalMacrostate {K : Type*} (S : MacroscopicSystem K)
    (reference rho : OperatorSequence S) (x : K → ℝ) : Prop :=
  IsStateSequence rho ∧ meanConcentrates S rho x ∧
    Filter.liminf (fun n =>
      relativeEntropy (rho n) (reference n) / (volume n : EReal)) atTop =
        relativeCanonicalEntropy S reference x

/-- PDF p.13: finite relative-entropy domain; the reference need not be faithful. -/
def RelativeAdmissible {K : Type*} (S : MacroscopicSystem K)
    (reference : OperatorSequence S) (x : K → ℝ) : Prop :=
  relativeCanonicalEntropy S reference x < ⊤

/-- PDF p.12, (4.2): microscopic complex-linear unital star automorphisms. -/
abbrev AutomorphismDynamics {K : Type*} (S : MacroscopicSystem K) :=
  (n : ℕ) → ℝ → ℝ →
    (Operator (S.dimension n) ≃⋆ₐ[ℂ] Operator (S.dimension n))

/-- PDF p.12, (4.2): composition order is exactly the printed Heisenberg order. -/
def AutomorphismCocycle {K : Type*} {S : MacroscopicSystem K}
    (tau : AutomorphismDynamics S) : Prop :=
  ∀ n (t u s : ℝ), 0 ≤ s → s ≤ u → u ≤ t → ∀ A,
    tau n t s A = tau n t u (tau n u s A)

/-- PDF pp.12-13: real-time two-parameter macroscopic maps. -/
abbrev MacroscopicDynamics (K : Type*) := ℝ → ℝ → (K → ℝ) → (K → ℝ)

/-- PDF p.12, (4.3): the SAME maximizing projection sequence for each x
works for every analytic test and all intervals; maps preserve Omega. -/
def microcanonicalAutonomy {K : Type*} (S : MacroscopicSystem K)
    (tau : AutomorphismDynamics S) (phi : MacroscopicDynamics K) : Prop :=
  (∀ x, microcanonicalAdmissible S x → ∀ (t s : ℝ), 0 ≤ s → s ≤ t →
    microcanonicalAdmissible S (phi t s x)) ∧
  ∀ x, microcanonicalAdmissible S x → ∃ P : OperatorSequence S,
    microcanonicalMacrostate S P x ∧
    ∀ (G : AnalyticTestSeries S) (t s : ℝ), 0 ≤ s → s ≤ t →
      Tendsto (fun n => traceExpectation (projectionDensity P n)
        (tau n t s (operatorEvaluation G n))) atTop
        (𝓝 (scalarEvaluation G (phi t s x)))

/-- PDF p.12, (4.4): semigroup condition on a specified invariant domain. -/
def macroscopicSemigroup {K : Type*} (domain : (K → ℝ) → Prop)
    (phi : MacroscopicDynamics K) : Prop :=
  ∀ x, domain x → ∀ (t u s : ℝ), 0 ≤ s → s ≤ u → u ≤ t →
    phi t u (phi u s x) = phi t s x

/-- PDF p.13, (4.5): microscopic Heisenberg maps on matrix algebras. -/
abbrev LinearDynamics {K : Type*} (S : MacroscopicSystem K) :=
  (n : ℕ) → ℝ → ℝ →
    (Operator (S.dimension n) →ₗ[ℂ] Operator (S.dimension n))

/-- PDF p.13: completely positive, UNITAL, stationary microscopic cocycle.
Unitality is the implicit Heisenberg convention needed to evolve normalized states. -/
def StationaryCPCocycle {K : Type*} {S : MacroscopicSystem K}
    (reference : OperatorSequence S) (tau : LinearDynamics S) : Prop :=
  (∀ n (t s : ℝ), 0 ≤ s → s ≤ t →
    QAlgorithms.Entanglement.IsCompletelyPositive (tau n t s) ∧
    tau n t s 1 = 1 ∧
    ∀ A, traceExpectation (reference n) (tau n t s A) = traceExpectation (reference n) A) ∧
  ∀ n (t u s : ℝ), 0 ≤ s → s ≤ u → u ≤ t → ∀ A,
    tau n t s A = tau n t u (tau n u s A)

/-- PDF p.13, (4.6): relative minimizers precede all coordinates and times.
The macroscopic maps act on the finite-relative-entropy domain. -/
def meanAutonomy {K : Type*} (S : MacroscopicSystem K)
    (reference : OperatorSequence S) (tau : LinearDynamics S)
    (phi : MacroscopicDynamics K) : Prop :=
  ∀ x, RelativeAdmissible S reference x → ∃ rho : OperatorSequence S,
    relativeCanonicalMacrostate S reference rho x ∧
    ∀ (k : K) (t s : ℝ), 0 ≤ s → s ≤ t →
      Tendsto (fun n => traceExpectation (rho n) (tau n t s (S.observable n k)))
        atTop (𝓝 (phi t s x k : ℂ))

/-- PDF pp.5,14: a one-site matrix embedded in a tensor register.
The frozen bit-index map fixes the orthonormal basis and wire order. -/
def siteOperator (T : ℕ) (M : Matrix Bool Bool ℂ) (site : Fin T) :
    Operator (2 ^ T) :=
  fun b c => M (QAlgorithms.natToBits T b site) (QAlgorithms.natToBits T c site) *
    ∏ j : Fin T, if j = site then 1 else
      if QAlgorithms.natToBits T b j = QAlgorithms.natToBits T c j then 1 else 0

/-- PDF p.5, (2.7): the three Pauli averages on N spin-1/2 particles. -/
def spinMagnetization (n : ℕ) (a : Fin 3) : Operator (2 ^ volume n) :=
  (volume n : ℂ)⁻¹ • ∑ i : Fin (volume n), siteOperator (volume n) (pauli a) i

/-- PDF pp.5-6: the spin model, with fixed analytic radii 2 > 1. -/
def spinSystem : MacroscopicSystem (Fin 3) where
  dimension n := 2 ^ volume n
  observable := spinMagnetization
  radius _ := 2

/-- PDF p.6: Euclidean length of the three-component magnetization. -/
def magnetizationLength (m : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (∑ a, m a ^ 2)

/-- PDF p.15, (4.10): extended eta, with zero endpoints and minus infinity
outside [0,1]. All logarithms are natural. -/
def extendedEta (p : ℝ) : EReal :=
  if 0 ≤ p ∧ p ≤ 1 then ((-p * Real.log p : ℝ) : EReal) else ⊥

/-- PDF p.14: two N-qubit registers; first scatterers, then spins.
The density is divided by N, not by the total number 2N of qubits. -/
def kacAverage (n : ℕ) (scatterer : Bool) (a : Fin 3) :
    Operator (2 ^ (2 * volume n)) :=
  (volume n : ℂ)⁻¹ • ∑ i : Fin (volume n),
    siteOperator (2 * volume n) (if scatterer then QAlgorithms.pauliZ else pauli a)
      ⟨if scatterer then i.val else volume n + i.val, by
        have hi := i.isLt
        split_ifs <;> omega⟩

/-- PDF p.14: X_0 is the scatterer mean and X_1,X_2,X_3 the spin Pauli means. -/
def kacSystem : MacroscopicSystem (Fin 4) where
  dimension n := 2 ^ (2 * volume n)
  observable n := Fin.cases (kacAverage n true 0) (fun a => kacAverage n false a)
  radius _ := 2

/-- PDF p.14: x = (mu,m_1,m_2,m_3). -/
def kacConfiguration (mu : ℝ) (m : Fin 3 → ℝ) : Fin 4 → ℝ :=
  Fin.cases mu m

/-- PDF p.15: qubit density represented by its real Bloch vector. -/
def blochDensity (m : Fin 3 → ℝ) : Matrix Bool Bool ℂ :=
  (2 : ℂ)⁻¹ • (1 + ∑ a, (m a : ℂ) • pauli a)

/-- PDF p.15, (4.11): the explicit effective one-step Kac channel. -/
def kacChannel (mu : ℝ) (V : Matrix.unitaryGroup Bool ℂ)
    (nu : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  (((1 - mu) / 2 : ℝ) : ℂ) • ((V : Matrix Bool Bool ℂ) * nu * star (V : Matrix Bool Bool ℂ)) +
    (((1 + mu) / 2 : ℝ) : ℂ) • nu

/-- PDF p.15: discrete macroscopic spin step, extracted from the reduced density. -/
def kacSpinStep (mu : ℝ) (V : Matrix.unitaryGroup Bool ℂ) (m : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun a => (traceExpectation (kacChannel mu V (blochDensity m)) (pauli a)).re

/-! Sanity checks pin the indexing, ordered-word identity, log-zero guard,
extended entropy endpoint, coordinate order, and printed Kac weights. -/

example : volume 0 = 1 := by rfl

example {d : ℕ} (rho : Operator d) : traceExpectation rho 0 = 0 := by
  simp [traceExpectation]

example {d : ℕ} (rho : Operator d) : SupportIncluded rho rho := by
  exact le_rfl

example : relativeEntropy (1 : Operator 1) 1 = 0 := by
  simp [relativeEntropy, QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported,
    cfc_one]

example {d : ℕ} (A : Operator d) :
    spectralFunction (fun _ => (0 : ℂ)) A = 0 := by
  simp [spectralFunction]

example {K : Type*} {S : MacroscopicSystem K} (n : ℕ) :
    wordOperator (S := S) n [] = 1 := by simp [wordOperator]

example (n : ℕ) : scaledLogMass n 0 = ⊥ := by simp [scaledLogMass]

example : extendedEta 0 = 0 := by simp [extendedEta]

example : extendedEta 1 = 0 := by simp [extendedEta]

example : extendedEta 2 = ⊥ := by norm_num [extendedEta]

example (mu : ℝ) (m : Fin 3 → ℝ) : kacConfiguration mu m 0 = mu := by rfl

example (V : Matrix.unitaryGroup Bool ℂ) (nu : Matrix Bool Bool ℂ) :
    kacChannel 1 V nu = nu := by simp [kacChannel]

example : pauli 0 = QAlgorithms.pauliX := by simp [pauli]

end QAlgorithms.Papers.Independent.Renew46.P24


