-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
-- name    : QAlgorithms_Papers_Independent_Frontier18_P07
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:51:58.754992+00:00
-- url     : https://prove2.me/theorems/77220897-fa8e-48de-8096-b92e28229958
-- title:
--   Definitions for Continuous ensembles and the chi-capacity of infinite-dimensional channels
-- statement:
--   The objects the formalized statements of *Continuous ensembles and the chi-capacity of infinite-dimensional channels* (arXiv:quant-ph/0408176) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `GeneralizedEnsemble`: Borel probability ensembles on trace-norm states; PDF p.2, Definition.
--   - `averageCoefficients`: Scalar coefficients of the average; PDF p.2. On probability ensembles of states the coefficients are integrable. No coefficientwise topology is used.
--   - `HasAverage`: Genuine coefficient barycenter relation, including scalar integrability; PDF p.2. The target is a normalized trace-class state.
--   - `HasFiniteSupport`: Finite conventional ensembles, as finite-support Borel laws; PDF p.2.
--   - `constrainedEnsembles`: Average constraints apply only to the average, not to individual signals; PDF p.6, the definition of P_A.
--   - `finiteEntropy`: Entropy of a positive finite-dimensional operator, including subnormalized compressions: Tr(A) log Tr(A) - Tr(A log A); PDF p.3, (1).
--   - `finiteRelativeEntropy`: Generalized relative entropy for positive finite-dimensional operators; PDF p.3, (2). Support inclusion is kernel inclusion in the reverse direction. The correction Tr(B-A) is essential for subnormalized compressions.
--   - `extendedEntropyNats`: Extended nonnegative entropy, by all finite coordinate compressions; PDF p.3, definition following Lemma 2. Cofinality of finite coordinate projections gives the same limit as any increasing exhaustive projections.
--   - `extendedRelativeEntropyNats`: Extended relative entropy in nats, including infinity on support failure; PDF p.3, definition following Lemma 2. No real-valued divergent sum is used.
--   - `relativeIntegral`: Integrated relative entropy to the fixed output reference Phi(sigma); PDF pp.4,12, (17). The competitor's own average is not substituted.
--   - `ensembleHolevo`: Generalized-ensemble Holevo functional, PDF p.4.
--   - `finiteEnsembleCapacity`: Original finite-ensemble definition of constrained capacity, PDF p.6, (5)-(6). Equality to the unrestricted-measure supremum is a theorem.
--   - `stateChi`: The single-state chi-function is the finite-ensemble supremum at exact average rho, PDF p.10, Corollary 2.
--   - `IsCapacityAttaining`: Optimal generalized ensemble, PDF p.8: admissibility and attainment.
--   - `IsOptimalAverage`: Optimal average, PDF p.8: a cluster point of the averages of an approximating sequence of finite ensembles. It is not a maximizer definition.
--   - `pureStates`: The set of normalized pure states, PDF pp.8-9; the accepted definition uses rank-one projectors and includes the norm-one condition.
--   - `scalarF`: Appendix B, PDF p.15: f(t)=t(1-ln t), with f(0)=0.
--   - `scalarInverse`: Inverse of f on [0,1], defined by the lower endpoint of its upper level set. Only arguments in [0,1] are used in the scalar theorem; that set is then nonempty and bounded below. PDF p.15.
--   - `scalarG`: Appendix B, PDF p.15: g(x)=x f^{-1}(ln(2)/x), for x>=1.
--   - `binaryEntropyBits`: Binary entropy in bits, with the zero endpoint convention, PDF p.15.
--   - `scalarH`: Appendix B, PDF pp.15-16: H(x)=h_2(g(x))+g(x)log_2 x.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, https://arxiv.org/abs/quant-ph/0408176v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

/-!
# Continuous ensembles and the ensembleHolevo-finiteEnsembleCapacity of infinite-dimensional channels

Holevo and Shirokov, arXiv:quant-ph/0408176v1. Countable orthonormal
coordinates include every separable complex Hilbert space, including finite
dimension. The accepted state space has trace-norm topology and its Borel
sigma algebra. Probability measures have Mathlib's weak topology.

Barycenters are represented by their scalar coefficients, with integrability
in the accepted `IsBarycenter` relation. This does not supply a Banach-valued
Bochner integral; that separate node is deferred. Extended extendedEntropyNats is defined
by the finite-compression prescription on PDF p.3, with natural logarithms.
The Appendix B scalar construction uses bits explicitly.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Borel probability ensembles on trace-norm states; PDF p.2, Definition. -/
abbrev GeneralizedEnsemble (I : Type) := ProbabilityMeasure (State I)

/-- The accepted Borel measurable space is definitionally the trace-norm Borel space. -/
instance stateBorelSpace (I : Type) : BorelSpace (State I) := ⟨rfl⟩

/-- Scalar coefficients of the average; PDF p.2. On probability ensembles of
states the coefficients are integrable. No coefficientwise topology is used. -/
def averageCoefficients {I : Type} (mu : GeneralizedEnsemble I) : Matrix I I ℂ :=
  fun i j => ∫ rho : State I, rho.coefficients i j ∂(mu : Measure (State I))

/-- Genuine coefficient barycenter relation, including scalar integrability;
PDF p.2. The target is a normalized trace-class state. -/
def HasAverage {I : Type} (mu : GeneralizedEnsemble I) (rho : State I) : Prop :=
  IsBarycenter (mu : Measure (State I)) State.coefficients rho.coefficients

/-- Finite conventional ensembles, as finite-support Borel laws; PDF p.2. -/
def HasFiniteSupport {I : Type} (mu : GeneralizedEnsemble I) : Prop :=
  (mu : Measure (State I)).support.Finite

/-- Average constraints apply only to the average, not to individual signals;
PDF p.6, the definition of P_A. -/
def constrainedEnsembles {I : Type} (A : Set (State I)) : Set (GeneralizedEnsemble I) :=
  {mu | ∃ rho ∈ A, HasAverage mu rho}

/- Coordinate compression (PDF p.3, Lemma 2) uses Mathlib's existing
`Matrix.submatrix A Subtype.val Subtype.val` on each finite coordinate set.
No local compression operation is declared. -/

/-- Entropy of a positive finite-dimensional operator, including subnormalized
compressions: Tr(A) log Tr(A) - Tr(A log A); PDF p.3, (1). -/
def finiteEntropy {F : Type} [Fintype F] [DecidableEq F]
    (A : Matrix F F ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (A.trace.re * Real.log A.trace.re - (A * cfc Real.log A).trace.re)

/-- Generalized relative entropy for positive finite-dimensional operators;
PDF p.3, (2). Support inclusion is kernel inclusion in the reverse direction.
The correction Tr(B-A) is essential for subnormalized compressions. -/
def finiteRelativeEntropy {F : Type} [Fintype F] [DecidableEq F]
    (A B : Matrix F F ℂ) : ℝ≥0∞ :=
  if LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin then
    ENNReal.ofReal ((A * cfc Real.log A - A * cfc Real.log B + B - A).trace.re)
  else ⊤

/-- Extended nonnegative entropy, by all finite coordinate compressions;
PDF p.3, definition following Lemma 2. Cofinality of finite coordinate
projections gives the same limit as any increasing exhaustive projections. -/
def extendedEntropyNats {I : Type} (A : Matrix I I ℂ) : ℝ≥0∞ :=
  ⨆ s : Finset I, finiteEntropy (A.submatrix (fun i : s => i.val) (fun i : s => i.val))

/-- Extended relative entropy in nats, including infinity on support failure;
PDF p.3, definition following Lemma 2. No real-valued divergent sum is used. -/
def extendedRelativeEntropyNats {I : Type} (A B : Matrix I I ℂ) : ℝ≥0∞ :=
  ⨆ s : Finset I, finiteRelativeEntropy (A.submatrix (fun i : s => i.val) (fun i : s => i.val))
    (B.submatrix (fun i : s => i.val) (fun i : s => i.val))

/-- Integrated relative entropy to the fixed output reference Phi(sigma);
PDF pp.4,12, (17). The competitor's own average is not substituted. -/
def relativeIntegral {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (mu : GeneralizedEnsemble I) (sigma : Matrix I I ℂ) : ℝ≥0∞ :=
  ∫⁻ rho : State I, extendedRelativeEntropyNats (Phi rho.coefficients) (Phi sigma)
    ∂(mu : Measure (State I))

/-- Generalized-ensemble Holevo functional, PDF p.4. -/
def ensembleHolevo {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (mu : GeneralizedEnsemble I) : ℝ≥0∞ :=
  relativeIntegral Phi mu (averageCoefficients mu)

/-- Original finite-ensemble definition of constrained capacity, PDF p.6,
(5)-(6). Equality to the unrestricted-measure supremum is a theorem. -/
def finiteEnsembleCapacity {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (A : Set (State I)) : ℝ≥0∞ :=
  ⨆ mu : {mu : GeneralizedEnsemble I // HasFiniteSupport mu ∧ mu ∈ constrainedEnsembles A},
    ensembleHolevo Phi mu.val

/-- The single-state chi-function is the finite-ensemble supremum at exact
average rho, PDF p.10, Corollary 2. -/
def stateChi {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (rho : State I) : ℝ≥0∞ :=
  finiteEnsembleCapacity Phi {rho}

/-- Optimal generalized ensemble, PDF p.8: admissibility and attainment. -/
def IsCapacityAttaining {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (A : Set (State I)) (mu : GeneralizedEnsemble I) : Prop :=
  mu ∈ constrainedEnsembles A ∧ ensembleHolevo Phi mu = finiteEnsembleCapacity Phi A

/-- Optimal average, PDF p.8: a cluster point of the averages of an
approximating sequence of finite ensembles. It is not a maximizer definition. -/
def IsOptimalAverage {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (A : Set (State I)) (rho : State I) : Prop :=
  rho ∈ A ∧ ∃ (mu : ℕ → GeneralizedEnsemble I) (averages : ℕ → State I),
    (∀ n, HasFiniteSupport (mu n) ∧ HasAverage (mu n) (averages n) ∧ averages n ∈ A) ∧
    Tendsto (fun n => ensembleHolevo Phi (mu n)) atTop (𝓝 (finiteEnsembleCapacity Phi A)) ∧
    ∃ k : ℕ → ℕ, StrictMono k ∧ Tendsto (fun n => averages (k n)) atTop (𝓝 rho)

/-- The set of normalized pure states, PDF pp.8-9; the accepted definition
uses rank-one projectors and includes the norm-one condition. -/
def pureStates (I : Type) : Set (State I) :=
  Set.range (fun rho : PureState I => rho.val)

/-- Appendix B, PDF p.15: f(t)=t(1-ln t), with f(0)=0. -/
def scalarF (t : ℝ) : ℝ := t * (1 - Real.log t)

/-- Inverse of f on [0,1], defined by the lower endpoint of its upper level
set. Only arguments in [0,1] are used in the scalar theorem; that set is
then nonempty and bounded below. PDF p.15. -/
def scalarInverse (y : ℝ) : ℝ :=
  sInf {t : ℝ | t ∈ Set.Icc 0 1 ∧ y ≤ scalarF t}

/-- Appendix B, PDF p.15: g(x)=x f^{-1}(ln(2)/x), for x>=1. -/
def scalarG (x : ℝ) : ℝ := x * scalarInverse (Real.log 2 / x)

/-- Binary entropy in bits, with the zero endpoint convention, PDF p.15. -/
def binaryEntropyBits (q : ℝ) : ℝ :=
  (-q * Real.log q - (1 - q) * Real.log (1 - q)) / Real.log 2

/-- Appendix B, PDF pp.15-16: H(x)=h_2(g(x))+g(x)log_2 x. -/
def scalarH (x : ℝ) : ℝ :=
  binaryEntropyBits (scalarG x) + scalarG x * (Real.log x / Real.log 2)

/-! Small sanity checks of complete local definitions; no paper theorem is proved. -/

example {I : Type} (mu : GeneralizedEnsemble I) :
    (mu : Measure (State I)) Set.univ = 1 := measure_univ

example {I : Type} (mu : GeneralizedEnsemble I) (rho : State I) (h : HasAverage mu rho) :
    averageCoefficients mu = rho.coefficients := by
  funext i j
  exact (h i j).2.symm

example {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (A : Set (State I)) (mu : GeneralizedEnsemble I) (h : IsCapacityAttaining Phi A mu) :
    ensembleHolevo Phi mu = finiteEnsembleCapacity Phi A := h.2

example {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (A : Set (State I)) (rho : State I) (h : IsOptimalAverage Phi A rho) :
    rho ∈ A := h.1

example {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) (rho : State I) :
    stateChi Phi rho = finiteEnsembleCapacity Phi {rho} := rfl

example {I : Type} (rho : PureState I) : rho.val ∈ pureStates I :=
  ⟨rho, rfl⟩

example {I : Type} (s : Finset I) (A : Matrix I I ℂ) (i j : s) :
    A.submatrix (fun i : s => i.val) (fun i : s => i.val) i j = A i.val j.val := rfl

example {F : Type} [Fintype F] [DecidableEq F] :
    finiteEntropy (0 : Matrix F F ℂ) = 0 := by
  simp [finiteEntropy]

example {F : Type} [Fintype F] [DecidableEq F] :
    finiteRelativeEntropy (0 : Matrix F F ℂ) 0 = 0 := by
  simp [finiteRelativeEntropy]

example {I : Type} : extendedEntropyNats (0 : Matrix I I ℂ) = 0 := by
  change (⨆ s : Finset I, finiteEntropy (0 : Matrix s s ℂ)) = 0
  simp [finiteEntropy]

example {I : Type} : constrainedEnsembles (∅ : Set (State I)) = ∅ := by
  ext mu
  simp [constrainedEnsembles]

example {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) :
    finiteEnsembleCapacity Phi (∅ : Set (State I)) = 0 := by
  simp [finiteEnsembleCapacity, constrainedEnsembles]

example {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) (mu : GeneralizedEnsemble I) :
    ensembleHolevo Phi mu = relativeIntegral Phi mu (averageCoefficients mu) := rfl

example : scalarF 0 = 0 := by simp [scalarF]

example : scalarF 1 = 1 := by simp [scalarF]

example : binaryEntropyBits 0 = 0 := by simp [binaryEntropyBits]

example : binaryEntropyBits 1 = 0 := by simp [binaryEntropyBits]

end QAlgorithms.Papers.Independent.Frontier18.P07


