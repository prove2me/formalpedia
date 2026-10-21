-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01
-- name    : QAlgorithms_Papers_Independent_Next46_P01
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T17:37:13.089847+00:00
-- url     : https://prove2.me/theorems/98692acf-f1e5-4ecd-bf38-f82e890a2ae4
-- title:
--   Definitions for Entropic Fluctuations in Statistical Mechanics II. Quantum Dynamical Systems
-- statement:
--   The objects the formalized statements of *Entropic Fluctuations in Statistical Mechanics II. Quantum Dynamical Systems* (arXiv:2409.15485) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `finitePower`: Complex spectral powers of a strictly positive matrix, PDF p.13. Every theorem use has positive-definite input; the logarithm is natural.
--   - `finiteDensityAt`: Schrödinger density at time t when tau_t(A)=exp(itH) A exp(-itH), PDF pp.9,13.
--   - `finiteAncillaFunctional`: The finite ancilla functional, with omega_{-t} and ordered factors, PDF p.13.
--   - `ancillaSigmaZ`: The eigenvalues +1,-1 are ordered as the ancilla labels +,-, PDF p.13.
--   - `finiteAncillaHamiltonian`: The actual coupled Hamiltonian, before taking a partial trace, PDF pp.13--14.
--   - `ancillaReadout`: The measurable ancilla density, including conjugation only in the lower-left coefficient, PDF p.14, Equation (2.16).
--   - `ClassicalFlowSystem`: The compact classical dynamical system with (Cl1), PDF p.21. Non-invariance is kept outside this structure so the p.28 obstruction has a nonvacuous ambient formulation. No cocycle law or entropy balance is assumed. The compact metric and Borel instances are explicit parameters, so Lean does not omit the source standing assumptions from consumers of this structure. This flow system differs from Dependency50.P05.ClassicalSystem, which is a diagonality predicate on a finite Choi matrix.
--   - `classicalEvolved`: nu_t(f)=nu(f composed with phi_t), PDF p.21.
--   - `ClassicalNonInvariant`: The source's non-invariance convention, PDF p.21.
--   - `classicalCocycle`: c^t=log(d omega_t/d omega) composed with phi_t, PDF p.21. RN derivatives are used only up to omega-a.e. equality; (Cl1) excludes their zero and infinite default values a.e. after the nonsingular flow.
--   - `classicalRelativeEntropy`: Nonpositive relative entropy of probability measures, PDF p.21. Minus KL retains minus infinity when the logarithm is not integrable. This is relative entropy, distinct from the finite Shannon entropy named classicalEntropy in Claimed50.P08 and Claimed50.P40.
--   - `extendedExpectation`: Extended signed expectation, PDF p.21. All uses below have finite negative part, so this never subtracts two infinities.
--   - `RegularClassicalSystem`: (Cl2) and (Cl3), PDF p.22. Continuous representatives are tied to the actual RN cocycle, not assumed additive. The derivative is in the sup norm on C(X).
--   - `classicalProduction`: sigma is computed from the norm derivative at zero, PDF p.22.
--   - `classicalLaw`: The law of c^t in an arbitrary initial probability state, PDF pp.21,23.
--   - `classicalFunctional`: Finite-time classical entropic functional, PDF p.23, Equation (2.35). Continuity and compactness make this integrable for all complex alpha and probability nu; it is not a scaled logarithm.
--   - `classicalRescaledLaw`: Speed-t classical laws P_t(B)=Q_t(t B), PDF pp.15,22. The source uses only positive t; division at nonpositive t is immaterial.
--   - `speedLogProbability`: Extended scaled logarithm of an event probability, PDF p.15, (2.20). For t>0, zero probability gives minus infinity. Nonpositive times are explicitly set to zero and are never used by the positive-time source asymptotics.
--   - `HasSpeedLDPOn`: Full/local speed-t LDP, PDF p.15, Definition 2.4, used on p.22. The source rate is globally lower semicontinuous and nonnegative, possibly infinite. Only the Borel test sets are restricted to the named domain. Infima are taken in ENNReal, so an empty set has infimum plus infinity; limits and inequalities are in EReal, retaining log(0)=-infinity.
--   - `ClassicalTRI`: Classical TRI, PDF pp.21--22. The map is an involutive homeomorphism and preserves the reference probability.
--   - `classicalCesaro`: Cesaro averages evaluated against a continuous real test, PDF p.23. Theorems restrict T to positive values.
--   - `IsClassicalNESS`: Weak cluster point of the positive-time Cesaro net, PDF p.23. Finite sets of continuous tests and epsilon balls give exactly the weak neighborhoods; arbitrary cutoffs encode cluster points as T tends to infinity. No convergence to a unique state or absolute continuity of the NESS is assumed.
--   - `StrongOperatorGroup`: A genuine strongly continuous group of bounded operators, PDF p.31. Completeness is an explicit parameter: consumers require a Hilbert space. There is no self-adjointness or operator-norm continuity assumption.
--   - `HasGroupGrowth`: Exponential operator-norm growth with fixed M,m, PDF p.31, Equation (4.1).
--   - `groupResolventCoefficient`: The scalar coefficient of the genuine resolvent (z-L)^-1, defined by the source's convergent Laplace formula on Im z>m, PDF pp.31,46. Here U_t=exp(-itL). Outside that half-plane this total definition is not used as a resolvent; analytic continuations are separate functions.
--   - `resonanceRemainder`: The actual remainder in Proposition 4.2, PDF p.32.
--   - `HasSolePole`: Sole singularity of exact order N in an open half-plane, PDF pp.31--32. Multiplying by (z-r)^N removes the pole; a nonzero value at r excludes removable singularities and every smaller pole order.
--   - `halfPlaneResidue`: Residue computed on a positively oriented circle strictly inside the half-plane of continuation, PDF p.45. Uses are guarded by mu+r.im>0 and HasSolePole; its integrand has no singularity on the circle.
--   - `HasUniformResolventTail`: The uniform L^(2-j) tail condition, PDF pp.31--32, Equations (4.2),(4.3). IntegrableOn prevents a nonintegrable Bochner integral from becoming zero. A real bound is quantified before the height y, rather than using an unguarded real supremum. The theorems use only j=0,1 and R>0.
--   - `HasTwoDecayingDerivatives`: Twice differentiable remainder with the two additional derivative decay bounds, PDF p.32. It does not require the original operator group to be C^2.
-- source:
--   Entropic Fluctuations in Statistical Mechanics II. Quantum Dynamical Systems, arXiv:2409.15485v2, https://arxiv.org/abs/2409.15485v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information

/-!
Statements from Benoist--Bruneau--Jaksic--Panati--Pillet, arXiv:2409.15485v2.
The finite ancilla, classical measure, and scalar resonance interfaces below are
paper-local. No finite-dimensional replacement of a general modular system is
made. Unstated nodes and their precise interface gaps are listed in HARD.md.
Compilation is deliberately pending under the batch compilation handoff.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P01

/-- Complex spectral powers of a strictly positive matrix, PDF p.13.
Every theorem use has positive-definite input; the logarithm is natural. -/
def finitePower {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (z : ℂ) : Matrix I I ℂ :=
  NormedSpace.exp (z • cfc Real.log A)

/-- Schrödinger density at time t when tau_t(A)=exp(itH) A exp(-itH), PDF pp.9,13. -/
def finiteDensityAt {I : Type*} [Fintype I] [DecidableEq I]
    (H nu : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) * nu *
    NormedSpace.exp ((Complex.I * (t : ℂ)) • H)

/-- The finite ancilla functional, with omega_{-t} and ordered factors, PDF p.13. -/
def finiteAncillaFunctional {I : Type*} [Fintype I] [DecidableEq I]
    (H omega nu : Matrix I I ℂ) (t : ℝ) (alpha : ℂ) : ℂ :=
  (nu * finitePower omega (-alpha / 2) *
    finitePower (finiteDensityAt H omega (-t)) alpha *
      finitePower omega (-alpha / 2)).trace

/-- The eigenvalues +1,-1 are ordered as the ancilla labels +,-, PDF p.13. -/
def ancillaSigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The actual coupled Hamiltonian, before taking a partial trace, PDF pp.13--14. -/
def finiteAncillaHamiltonian {I : Type*} [Fintype I] [DecidableEq I]
    (H omega : Matrix I I ℂ) (alpha : ℂ) : Matrix (I × Fin 2) (I × Fin 2) ℂ :=
  let K := Matrix.kronecker (cfc Real.log omega) ancillaSigmaZ
  NormedSpace.exp ((alpha / 2) • K) * Matrix.kronecker H 1 *
    NormedSpace.exp ((-alpha / 2) • K)

/-- The measurable ancilla density, including conjugation only in the lower-left
coefficient, PDF p.14, Equation (2.16). -/
def ancillaReadout (rho : Matrix (Fin 2) (Fin 2) ℂ) (F : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![rho 0 0, F * rho 0 1; conj F * rho 1 0, rho 1 1]

example {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    finitePower A 0 = 1 := by
  simp [finitePower, NormedSpace.exp_zero]

example {I : Type*} [Fintype I] [DecidableEq I] (H nu : Matrix I I ℂ) :
    finiteDensityAt H nu 0 = nu := by
  simp [finiteDensityAt, NormedSpace.exp_zero]

example {I : Type*} [Fintype I] [DecidableEq I] (H omega nu : Matrix I I ℂ)
    (t : ℝ) : finiteAncillaFunctional H omega nu t 0 = nu.trace := by
  simp [finiteAncillaFunctional, finitePower, NormedSpace.exp_zero]

example {I : Type*} [Fintype I] [DecidableEq I] (H omega : Matrix I I ℂ) :
    finiteAncillaHamiltonian H omega 0 = Matrix.kronecker H 1 := by
  simp [finiteAncillaHamiltonian, NormedSpace.exp_zero]

example (rho : Matrix (Fin 2) (Fin 2) ℂ) : ancillaReadout rho 1 = rho := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ancillaReadout]

section Classical

variable (X : Type*) [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- The compact classical dynamical system with (Cl1), PDF p.21.
Non-invariance is kept outside this structure so the p.28 obstruction has a
nonvacuous ambient formulation. No cocycle law or entropy balance is assumed.
The compact metric and Borel instances are explicit parameters, so Lean does
not omit the source standing assumptions from consumers of this structure.
This flow system differs from Dependency50.P05.ClassicalSystem, which is a
diagonality predicate on a finite Choi matrix. -/
structure ClassicalFlowSystem (X : Type*) [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] where
  flow : ℝ → X ≃ₜ X
  flow_zero : ∀ x, flow 0 x = x
  flow_add : ∀ t s x, flow (t + s) x = flow t (flow s x)
  continuous_flow : Continuous (fun p : ℝ × X => flow p.1 p.2)
  omega : ProbabilityMeasure X
  quasi_invariant : ∀ t : ℝ,
    (Measure.map (flow t) (omega : Measure X)) ≪ (omega : Measure X) ∧
      (omega : Measure X) ≪ Measure.map (flow t) (omega : Measure X)

variable {X}

/-- nu_t(f)=nu(f composed with phi_t), PDF p.21. -/
def classicalEvolved (D : ClassicalFlowSystem X) (nu : Measure X) (t : ℝ) : Measure X :=
  Measure.map (D.flow t) nu

/-- The source's non-invariance convention, PDF p.21. -/
def ClassicalNonInvariant (D : ClassicalFlowSystem X) : Prop :=
  ∃ t : ℝ, classicalEvolved D (D.omega : Measure X) t ≠ (D.omega : Measure X)

/-- c^t=log(d omega_t/d omega) composed with phi_t, PDF p.21.
RN derivatives are used only up to omega-a.e. equality; (Cl1) excludes their
zero and infinite default values a.e. after the nonsingular flow. -/
def classicalCocycle (D : ClassicalFlowSystem X) (t : ℝ) (x : X) : ℝ :=
  Real.log (((classicalEvolved D (D.omega : Measure X) t).rnDeriv
    (D.omega : Measure X) (D.flow t x)).toReal)

/-- Nonpositive relative entropy of probability measures, PDF p.21.
Minus KL retains minus infinity when the logarithm is not integrable.
This is relative entropy, distinct from the finite Shannon entropy named
classicalEntropy in Claimed50.P08 and Claimed50.P40. -/
def classicalRelativeEntropy (nu mu : Measure X) : EReal :=
  -(InformationTheory.klDiv nu mu : EReal)

/-- Extended signed expectation, PDF p.21. All uses below have finite negative
part, so this never subtracts two infinities. -/
def extendedExpectation (nu : Measure X) (f : X → ℝ) : EReal :=
  ((∫⁻ x, ENNReal.ofReal (f x) ∂nu) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (-f x) ∂nu) : EReal)

/-- (Cl2) and (Cl3), PDF p.22. Continuous representatives are tied to the actual
RN cocycle, not assumed additive. The derivative is in the sup norm on C(X). -/
structure RegularClassicalSystem (X : Type*) [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] extends ClassicalFlowSystem X where
  continuousCocycle : ℝ → C(X, ℝ)
  agrees : ∀ t : ℝ,
    (fun x => continuousCocycle t x) =ᵐ[(toClassicalFlowSystem.omega : Measure X)]
      classicalCocycle toClassicalFlowSystem t
  norm_differentiable : DifferentiableAt ℝ continuousCocycle 0

/-- sigma is computed from the norm derivative at zero, PDF p.22. -/
def classicalProduction (D : RegularClassicalSystem X) : C(X, ℝ) :=
  deriv D.continuousCocycle 0

/-- The law of c^t in an arbitrary initial probability state, PDF pp.21,23. -/
def classicalLaw (D : RegularClassicalSystem X) (nu : Measure X) (t : ℝ) : Measure ℝ :=
  Measure.map (D.continuousCocycle t) nu

/-- Finite-time classical entropic functional, PDF p.23, Equation (2.35).
Continuity and compactness make this integrable for all complex alpha and
probability nu; it is not a scaled logarithm. -/
def classicalFunctional (D : RegularClassicalSystem X) (nu : Measure X)
    (t : ℝ) (alpha : ℂ) : ℂ :=
  ∫ x, Complex.exp (-alpha * (D.continuousCocycle t x : ℂ)) ∂nu

/-- Speed-t classical laws P_t(B)=Q_t(t B), PDF pp.15,22.
The source uses only positive t; division at nonpositive t is immaterial. -/
def classicalRescaledLaw (D : RegularClassicalSystem X) (t : ℝ) : Measure ℝ :=
  Measure.map (fun s : ℝ => s / t) (classicalLaw D (D.omega : Measure X) t)

/-- Extended scaled logarithm of an event probability, PDF p.15, (2.20).
For t>0, zero probability gives minus infinity. Nonpositive times are explicitly
set to zero and are never used by the positive-time source asymptotics. -/
def speedLogProbability (P : ℝ → Measure ℝ) (B : Set ℝ) (t : ℝ) : EReal :=
  if 0 < t then ((t⁻¹ : ℝ) : EReal) * ENNReal.log (P t B) else 0

/-- Full/local speed-t LDP, PDF p.15, Definition 2.4, used on p.22.
The source rate is globally lower semicontinuous and nonnegative, possibly
infinite. Only the Borel test sets are restricted to the named domain.
Infima are taken in ENNReal, so an empty set has infimum plus infinity;
limits and inequalities are in EReal, retaining log(0)=-infinity. -/
def HasSpeedLDPOn (P : ℝ → Measure ℝ) (rate : ℝ → ℝ≥0∞)
    (domain : Set ℝ) : Prop :=
  (∀ t : ℝ, 0 < t → IsProbabilityMeasure (P t)) ∧
    LowerSemicontinuous rate ∧
    ∀ B : Set ℝ, MeasurableSet B → B ⊆ domain →
      -(((⨅ s ∈ interior B, rate s) : ℝ≥0∞) : EReal) ≤
        Filter.liminf (speedLogProbability P B) atTop ∧
      Filter.liminf (speedLogProbability P B) atTop ≤
        Filter.limsup (speedLogProbability P B) atTop ∧
      Filter.limsup (speedLogProbability P B) atTop ≤
        -(((⨅ s ∈ closure B, rate s) : ℝ≥0∞) : EReal)

example (P : ℝ → Measure ℝ) (B : Set ℝ) : speedLogProbability P B 0 = 0 := by
  simp [speedLogProbability]

example (P : ℝ → Measure ℝ) (B : Set ℝ) (h : P 1 B = 1) :
    speedLogProbability P B 1 = 0 := by
  simp [speedLogProbability, h]

example (rate : ℝ → ℝ≥0∞) : (⨅ s ∈ (∅ : Set ℝ), rate s) = ⊤ := by
  simp

/-- Classical TRI, PDF pp.21--22. The map is an involutive homeomorphism and
preserves the reference probability. -/
def ClassicalTRI (D : ClassicalFlowSystem X) (iota : X ≃ₜ X) : Prop :=
  (∀ x, iota (iota x) = x) ∧
    (∀ t x, iota (D.flow t x) = D.flow (-t) (iota x)) ∧
      Measure.map iota (D.omega : Measure X) = (D.omega : Measure X)

/-- Cesaro averages evaluated against a continuous real test, PDF p.23.
Theorems restrict T to positive values. -/
def classicalCesaro (D : ClassicalFlowSystem X) (f : C(X, ℝ)) (T : ℝ) : ℝ :=
  T⁻¹ * ∫ s in (0 : ℝ)..T, ∫ x, f (D.flow s x) ∂(D.omega : Measure X)

/-- Weak cluster point of the positive-time Cesaro net, PDF p.23.
Finite sets of continuous tests and epsilon balls give exactly the weak
neighborhoods; arbitrary cutoffs encode cluster points as T tends to infinity.
No convergence to a unique state or absolute continuity of the NESS is assumed. -/
def IsClassicalNESS (D : ClassicalFlowSystem X) (nu : ProbabilityMeasure X) : Prop :=
  ∀ (tests : Finset C(X, ℝ)) (epsilon : ℝ), 0 < epsilon →
    ∀ cutoff : ℝ, ∃ T : ℝ, cutoff < T ∧ 0 < T ∧
      ∀ f ∈ tests, |classicalCesaro D f T - ∫ x, f x ∂(nu : Measure X)| < epsilon

example (D : ClassicalFlowSystem X) (nu : Measure X) :
    classicalEvolved D nu 0 = nu := by
  have h : (fun x => D.flow 0 x) = id := funext D.flow_zero
  simp [classicalEvolved, h]

example (nu : Measure X) : extendedExpectation nu (fun _ => 0) = 0 := by
  simp [extendedExpectation]

example (D : RegularClassicalSystem X) (nu : Measure X) (t : ℝ) :
    classicalFunctional D nu t 0 = ∫ _x, (1 : ℂ) ∂nu := by
  simp [classicalFunctional]

end Classical

section Resonance

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A genuine strongly continuous group of bounded operators, PDF p.31.
Completeness is an explicit parameter: consumers require a Hilbert space.
There is no self-adjointness or operator-norm continuity assumption. -/
structure StrongOperatorGroup (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  op : ℝ → H →L[ℂ] H
  at_zero : op 0 = 1
  add_time : ∀ t s : ℝ, op (t + s) = op t * op s
  strong_continuity : ∀ psi : H, Continuous (fun t : ℝ => op t psi)

variable {H}

/-- Exponential operator-norm growth with fixed M,m, PDF p.31, Equation (4.1). -/
def HasGroupGrowth (U : StrongOperatorGroup H) (M m : ℝ) : Prop :=
  0 < M ∧ 0 < m ∧ ∀ t : ℝ, ‖U.op t‖ ≤ M * Real.exp (m * |t|)

/-- The scalar coefficient of the genuine resolvent (z-L)^-1, defined by the
source's convergent Laplace formula on Im z>m, PDF pp.31,46.
Here U_t=exp(-itL). Outside that half-plane this total definition is not used
as a resolvent; analytic continuations are separate functions. -/
def groupResolventCoefficient (U : StrongOperatorGroup H) (phi psi : H) (z : ℂ) : ℂ :=
  -Complex.I * ∫ t in Set.Ici (0 : ℝ),
    Complex.exp (Complex.I * z * (t : ℂ)) * inner ℂ phi (U.op t psi)

/-- The actual remainder in Proposition 4.2, PDF p.32. -/
def resonanceRemainder (U : StrongOperatorGroup H) (phi psi : H)
    (r : ℂ) (p : Polynomial ℂ) (t : ℝ) : ℂ :=
  inner ℂ phi (U.op t psi) - Complex.exp (-Complex.I * (t : ℂ) * r) * p.eval (t : ℂ)

/-- Sole singularity of exact order N in an open half-plane, PDF pp.31--32.
Multiplying by (z-r)^N removes the pole; a nonzero value at r excludes
removable singularities and every smaller pole order. -/
def HasSolePole (f : ℂ → ℂ) (mu : ℝ) (r : ℂ) (N : ℕ) : Prop :=
  1 ≤ N ∧ -mu < r.im ∧ ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g {z : ℂ | -mu < z.im} ∧ g r ≠ 0 ∧
      ∀ z : ℂ, -mu < z.im → z ≠ r → f z = g z / (z - r) ^ N

/-- Residue computed on a positively oriented circle strictly inside the
half-plane of continuation, PDF p.45. Uses are guarded by mu+r.im>0 and
HasSolePole; its integrand has no singularity on the circle. -/
def halfPlaneResidue (f : ℂ → ℂ) (mu : ℝ) (r : ℂ) : ℂ :=
  circleIntegral f r ((mu + r.im) / 2) / (2 * (Real.pi : ℂ) * Complex.I)

/-- The uniform L^(2-j) tail condition, PDF pp.31--32, Equations (4.2),(4.3).
IntegrableOn prevents a nonintegrable Bochner integral from becoming zero.
A real bound is quantified before the height y, rather than using an unguarded
real supremum. The theorems use only j=0,1 and R>0. -/
def HasUniformResolventTail (f : ℂ → ℂ) (mu R : ℝ) (j : ℕ) : Prop :=
  ∃ C : ℝ, ∀ y : ℝ, -mu < y →
    IntegrableOn (fun x : ℝ => ‖iteratedDeriv j f ((x : ℂ) + Complex.I * (y : ℂ))‖ ^ (2 - j))
      {x : ℝ | R < |x|} ∧
    (∫ x in {x : ℝ | R < |x|},
      ‖iteratedDeriv j f ((x : ℂ) + Complex.I * (y : ℂ))‖ ^ (2 - j)) ≤ C

/-- Twice differentiable remainder with the two additional derivative decay
bounds, PDF p.32. It does not require the original operator group to be C^2. -/
def HasTwoDecayingDerivatives (R : ℝ → ℂ) (gamma : ℝ) : Prop :=
  Differentiable ℝ R ∧ Differentiable ℝ (deriv R) ∧
    Asymptotics.IsBigO atTop (deriv R) (fun t : ℝ => Real.exp (-gamma * t)) ∧
    Asymptotics.IsBigO atTop (deriv (deriv R)) (fun t : ℝ => Real.exp (-gamma * t))

example (f : ℂ → ℂ) (mu : ℝ) (r : ℂ) : ¬ HasSolePole f mu r 0 := by
  simp [HasSolePole]

example (U : StrongOperatorGroup H) (phi psi : H) (r : ℂ) (p : Polynomial ℂ) :
    resonanceRemainder U phi psi r p 0 = inner ℂ phi psi - p.eval 0 := by
  simp [resonanceRemainder, U.at_zero]

end Resonance

end QAlgorithms.Papers.Independent.Next46.P01


