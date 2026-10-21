-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
-- name    : QAlgorithms_Papers_Independent_Claimed50_P15
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T09:38:06.936518+00:00
-- url     : https://prove2.me/theorems/28a80791-3db0-4e3d-84fc-9a4fce3c701e
-- title:
--   Definitions for Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics
-- statement:
--   The objects the formalized statements of *Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics* (arXiv:1109.3804) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `positiveMatrixRpow`: Positive-matrix real powers by the self-adjoint functional calculus, PDF pp.4,11. All theorem uses have positive-definite inputs; no inverse at zero is used.
--   - `evaluate`: Real trace evaluation of a positive functional on an observable, PDF p.10. The complex trace is real on the Hermitian/positive arguments used below.
--   - `IsProjectionTest`: Projection tests accept omega on outcome one, PDF p.11.
--   - `IsEffectTest`: Bounded effects, with genuine positive-operator contraction order, PDF p.12.
--   - `testingError`: The total testing error D(nu,omega,T), PDF p.11 (3.3).
--   - `optimalError`: Optimal projection/effect error as an extended-real infimum, PDF pp.11--12. The admissible set contains zero; positive inputs bound it below by zero.
--   - `positiveSupport`: Strictly positive spectral support of a Hermitian matrix, PDF pp.10,12. A zero eigenvalue is excluded, preserving the source's tie convention.
--   - `petzOverlap`: Petz overlap Tr(nu^s omega^(1-s)), equal to the modular quadratic form, PDF pp.11--12. The functionals are not required to have unit trace.
--   - `petzLogOverlap`: Extended natural logarithm of the Petz overlap, PDF p.11. In particular a zero overlap has value minus infinity, never real zero.
--   - `modularMatrix`: The finite relative modular operator in Hilbert--Schmidt matrix coordinates, Delta(A)=nu A omega^-1, PDF p.12. Inverses are used only for positive-definite omega.
--   - `modularQuadratic`: Hilbert--Schmidt quadratic form in Omega_omega=sqrt(omega), PDF p.12. Conjugation is on the first argument, as in the paper.
--   - `resolventOverlap`: Resolvent lower-bound quadratic form, PDF pp.12--13. This finite matrix expression is not an infinite-dimensional modular inverse.
--   - `extendedConvex`: Extension by positive infinity outside [a,b], PDF p.6.
--   - `legendre`: Fenchel--Legendre transform, PDF p.6 (2.1). Used only for a<b and continuous e on [a,b], hence a finite attained supremum.
--   - `convexSubgradient`: Supporting-line definition of the source subdifferential, PDF p.6. Outside the finite domain, the source assigns the empty subdifferential.
--   - `finiteSubgradient`: Subdifferential of an everywhere-finite convex function, PDF p.6.
--   - `rightSlope`: Right slope as the infimum of right secant slopes, PDF p.6. For continuous convex e this is D+e(s), including a possibly infinite endpoint.
--   - `leftSlope`: Left slope as the supremum of left secant slopes, PDF p.6. For continuous convex e this is D-e(s), including a possibly infinite endpoint.
--   - `hoeffdingTransform`: Hoeffding variational function, PDF p.7 (2.4). The half-open domain excludes division by zero; the supremum is extended real.
--   - `FiniteExperiment`: A finite nonzero measure space and a measurable real observable, PDF p.7. Its mass need not equal one.
--   - `LDFamily`: Arbitrary unbounded positive real index set, variable spaces and positive weights tending to infinity, PDF p.7.
--   - `indexFilter`: The limit along the source's real index subset, PDF p.7.
--   - `exponentialMoment`: Positive exponential moment as a nonnegative integral, PDF p.7. Divergent moments have value positive infinity.
--   - `scaledMoment`: Scaled extended logarithmic moment, PDF p.7 (LD).
--   - `HasLD`: Assumption LD itself, PDF pp.7--8. Convexity is a consequence, not an extra hypothesis; e is a real representative on the specified interval.
--   - `scaledEvent`: Logarithmic mass of an observable event, PDF pp.8--10. An empty event has value minus infinity.
--   - `upperTail`: Strict upper-tail event from (2.5),(2.7), PDF p.8.
--   - `lowerTail`: Strict lower-tail event from (2.6), PDF p.8.
--   - `FiniteTestingFamily`: Finite-system sequence with strictly positive functionals and diverging positive weights, PDF p.13; normalization is imposed separately where needed.
--   - `IsStateFamily`: The state hypothesis introduced only after Theorem 3.4, PDF p.14.
--   - `TestFamily`: A family of actual projection/effect tests, PDF pp.14--15.
--   - `scaledRenyi`: Scaled Petz logarithms with natural logs, PDF p.13.
--   - `extendedErrorLog`: Natural log on a nonnegative extended value, used on genuine testing errors. PDF p.13. An error equal to zero gives minus infinity.
--   - `symmetricRate`: Symmetric testing logarithms; the infimum precedes logarithm, PDF p.13.
--   - `typeIRate`: Type-I error exponent sequence, PDF pp.14--15.
--   - `typeIIRate`: Type-II error exponent sequence, PDF pp.14--15.
--   - `ExponentKind`: Three distinct exponent constructions: liminf, limsup and an existing limit, PDF pp.14--15. A genuine limit is included by an explicit Tendsto requirement.
--   - `testingExponent`: The lower, upper and existing-limit infima over exactly the admissible tests, PDF pp.14--15. Empty admissible sets have infimum positive infinity.
--   - `hoeffdingExponent`: The STRICT Hoeffding constraint, PDF pp.14--15.
--   - `steinExponent`: Fixed-epsilon Stein constraint at EVERY index, PDF p.15.
--   - `HasAF1`: AF1, PDF p.13: no normalization, no assumed lower testing bound. The extended endpoint slopes may be infinite.
--   - `HasAF2`: AF2, PDF p.15: a finite moment-limit extension past one, differentiable there.
--   - `distinctSpectrum`: Distinct eigenvalues, rather than a list counted with multiplicity, PDF pp.10,20. Degenerate entropy outcomes are measured with their full spectral projections.
--   - `propagator`: Schrodinger evolution exp(-itH), PDF p.19.
--   - `evolvedState`: Time-evolved state U_t omega U_t*, PDF p.19.
--   - `evolvedObservable`: Heisenberg evolution U_t* A U_t, PDF p.19.
--   - `finiteRelativeEntropyNats`: The paper's nonpositive relative entropy, in nats, for faithful finite matrices, PDF p.11 (3.1). Arbitrary positive trace is allowed.
--   - `entropyObservable`: The entropy observable is -log omega, PDF p.19.
--   - `meanProduction`: Time-averaged entropy production (S_t-S)/t, PDF p.19 (4.1). The source theorem below restricts t to positive values.
--   - `finiteEntropic`: Finite-time real entropic functional, PDF pp.19--20. The faithful hypotheses guarantee strictly positive overlaps for every real s.
--   - `finiteModularLaw`: The spectral law of MINUS log Delta_nu|omega in Omega_omega, PDF p.12. Its mass is Tr omega, not necessarily one.
--   - `finiteFCS`: Two-measurement FCS, PDF p.20. The measured entropy change is (alpha_prime-alpha)/t = (log lam-log mu)/t; no density/Jacobian is introduced.
--   - `IsFiniteTRI`: Finite-system time reversal: one orthonormal basis makes both H and omega real, PDF p.21. The unitary changes the original orthonormal coordinates.
--   - `FiniteSystem`: A genuine finite dynamical system, PDF pp.19,24.
--   - `WeakMeasureLimit`: Weak convergence of finite Borel measures tested against every bounded continuous complex function, PDF p.24. All uses have finite measures.
--   - `tdFCS`: The thermodynamic FCS, constructed as the unique probability weak limit when it exists, PDF p.24. Zero is only an off-domain fallback, never used under TD.
--   - `tdEntropic`: Thermodynamic entropic functional computed from the scalar limit, PDF p.24. Under TD this defining set is a nonempty singleton; no unbounded real infimum occurs.
--   - `HasTD`: TD, including the open symmetric interval containing [0,1], PDF p.24.
--   - `ltEntropic`: Large-time entropic functional computed after the thermodynamic limit, PDF p.25. Under LT this real-infimum set is a nonempty singleton.
--   - `HasLT`: LT adds finite long-time limits and differentiability on I, PDF p.25.
--   - `tdMeanProduction`: Inner thermodynamic mean-production limit, PDF p.26. The existence of this limit is conclusion content in the law below.
--   - `tdRelativeEntropy`: Inner thermodynamic relative-entropy limit, PDF p.26. Used only at fixed positive t under LT, where its set is a singleton.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, https://arxiv.org/abs/1109.3804v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_SpectralFilter

/-!
Statements from Jakšić--Ogata--Pillet--Seiringer, arXiv:1109.3804v2.
All new definitions are local to this paper. The real spectral powers, Petz
log-overlap, extended-error log, and signed relative entropy are distinct from
the frozen library concepts with previously colliding short names; exact
comparisons are recorded in ASSESSMENT.json. General W*-algebraic results and
concrete infinite-system models requiring additional interfaces are deferred
explicitly in the unit's HARD.md and GAPS.json. Compilation is pending.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Positive-matrix real powers by the self-adjoint functional calculus, PDF pp.4,11.
All theorem uses have positive-definite inputs; no inverse at zero is used. -/
def positiveMatrixRpow {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (s : ℝ) : Matrix I I ℂ :=
  cfc (fun x : ℝ => x ^ s) A

/-- Real trace evaluation of a positive functional on an observable, PDF p.10.
The complex trace is real on the Hermitian/positive arguments used below. -/
def evaluate {I : Type*} [Fintype I] [DecidableEq I]
    (rho A : Matrix I I ℂ) : ℝ := (rho * A).trace.re

/-- Projection tests accept omega on outcome one, PDF p.11. -/
def IsProjectionTest {I : Type*} [Fintype I] [DecidableEq I]
    (T : Matrix I I ℂ) : Prop := T.IsHermitian ∧ T * T = T

/-- Bounded effects, with genuine positive-operator contraction order, PDF p.12. -/
abbrev IsEffectTest {I : Type*} [Fintype I] [DecidableEq I]
    (T : Matrix I I ℂ) : Prop := QAlgorithms.IsEffect T

/-- The total testing error D(nu,omega,T), PDF p.11 (3.3). -/
def testingError {I : Type*} [Fintype I] [DecidableEq I]
    (nu omega T : Matrix I I ℂ) : ℝ := evaluate nu T + evaluate omega (1 - T)

/-- Optimal projection/effect error as an extended-real infimum, PDF pp.11--12.
The admissible set contains zero; positive inputs bound it below by zero. -/
def optimalError {I : Type*} [Fintype I] [DecidableEq I]
    (effect : Bool) (nu omega : Matrix I I ℂ) : EReal :=
  sInf {v | ∃ T : Matrix I I ℂ,
    (if effect then IsEffectTest T else IsProjectionTest T) ∧
      v = (testingError nu omega T : EReal)}

/-- Strictly positive spectral support of a Hermitian matrix, PDF pp.10,12.
A zero eigenvalue is excluded, preserving the source's tie convention. -/
def positiveSupport {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) : Matrix I I ℂ :=
  cfc (fun x : ℝ => if 0 < x then 1 else 0) A

/-- Petz overlap Tr(nu^s omega^(1-s)), equal to the modular quadratic form,
PDF pp.11--12. The functionals are not required to have unit trace. -/
def petzOverlap {I : Type*} [Fintype I] [DecidableEq I]
    (nu omega : Matrix I I ℂ) (s : ℝ) : ℝ :=
  (positiveMatrixRpow nu s * positiveMatrixRpow omega (1 - s)).trace.re

/-- Extended natural logarithm of the Petz overlap, PDF p.11.
In particular a zero overlap has value minus infinity, never real zero. -/
def petzLogOverlap {I : Type*} [Fintype I] [DecidableEq I]
    (nu omega : Matrix I I ℂ) (s : ℝ) : EReal :=
  ENNReal.log (ENNReal.ofReal (petzOverlap nu omega s))

/-- The finite relative modular operator in Hilbert--Schmidt matrix coordinates,
Delta(A)=nu A omega^-1, PDF p.12. Inverses are used only for positive-definite omega. -/
def modularMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (nu omega : Matrix I I ℂ) : Matrix (I × I) (I × I) ℂ :=
  fun p q => nu p.1 q.1 * (omega⁻¹) q.2 p.2

/-- Hilbert--Schmidt quadratic form in Omega_omega=sqrt(omega), PDF p.12.
Conjugation is on the first argument, as in the paper. -/
def modularQuadratic {I : Type*} [Fintype I] [DecidableEq I]
    (omega : Matrix I I ℂ) (K : Matrix (I × I) (I × I) ℂ) : ℝ :=
  let v : I × I → ℂ := fun p => (cfc Real.sqrt omega) p.1 p.2
  (∑ p, star (v p) * (K.mulVec v) p).re

/-- Resolvent lower-bound quadratic form, PDF pp.12--13.
This finite matrix expression is not an infinite-dimensional modular inverse. -/
def resolventOverlap {I : Type*} [Fintype I] [DecidableEq I]
    (nu omega : Matrix I I ℂ) : ℝ :=
  let D := modularMatrix nu omega
  modularQuadratic omega (D * (1 + D)⁻¹)

/-- Extension by positive infinity outside [a,b], PDF p.6. -/
def extendedConvex (a b : ℝ) (e : ℝ → ℝ) (s : ℝ) : EReal :=
  if s ∈ Set.Icc a b then (e s : EReal) else ⊤

/-- Fenchel--Legendre transform, PDF p.6 (2.1).
Used only for a<b and continuous e on [a,b], hence a finite attained supremum. -/
def legendre (a b : ℝ) (e : ℝ → ℝ) (theta : ℝ) : ℝ :=
  sSup ((fun s : ℝ => theta * s - e s) '' Set.Icc a b)

/-- Supporting-line definition of the source subdifferential, PDF p.6.
Outside the finite domain, the source assigns the empty subdifferential. -/
def convexSubgradient (a b : ℝ) (e : ℝ → ℝ) (s theta : ℝ) : Prop :=
  s ∈ Set.Icc a b ∧ ∀ t ∈ Set.Icc a b, e s + theta * (t - s) ≤ e t

/-- Subdifferential of an everywhere-finite convex function, PDF p.6. -/
def finiteSubgradient (f : ℝ → ℝ) (theta s : ℝ) : Prop :=
  ∀ eta : ℝ, f theta + s * (eta - theta) ≤ f eta

/-- Right slope as the infimum of right secant slopes, PDF p.6.
For continuous convex e this is D+e(s), including a possibly infinite endpoint. -/
def rightSlope (b : ℝ) (e : ℝ → ℝ) (s : ℝ) : EReal :=
  sInf {v | ∃ t : ℝ, s < t ∧ t ≤ b ∧ v = (((e t - e s) / (t - s) : ℝ) : EReal)}

/-- Left slope as the supremum of left secant slopes, PDF p.6.
For continuous convex e this is D-e(s), including a possibly infinite endpoint. -/
def leftSlope (a : ℝ) (e : ℝ → ℝ) (s : ℝ) : EReal :=
  sSup {v | ∃ t : ℝ, a ≤ t ∧ t < s ∧ v = (((e s - e t) / (s - t) : ℝ) : EReal)}

/-- Hoeffding variational function, PDF p.7 (2.4).
The half-open domain excludes division by zero; the supremum is extended real. -/
def hoeffdingTransform (e : ℝ → ℝ) (r : ℝ) : EReal :=
  -sSup {v | ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧
    v = (((-s * r - e s) / (1 - s) : ℝ) : EReal)}

/-- A finite nonzero measure space and a measurable real observable, PDF p.7.
Its mass need not equal one. -/
structure FiniteExperiment where
  Space : Type
  measurableSpace : MeasurableSpace Space
  measure : @Measure Space measurableSpace
  finite_mass : measure Set.univ < ⊤
  nonzero_mass : measure Set.univ ≠ 0
  observable : Space → ℝ
  measurable_observable : @Measurable Space ℝ measurableSpace inferInstance observable

/-- Arbitrary unbounded positive real index set, variable spaces and positive
weights tending to infinity, PDF p.7. -/
structure LDFamily where
  index : Set ℝ
  index_positive : ∀ t ∈ index, 0 < t
  index_unbounded : ∀ R : ℝ, ∃ t ∈ index, R ≤ t
  experiment : index → FiniteExperiment
  weight : index → ℝ
  weight_positive : ∀ t, 0 < weight t
  weight_tendsto : Tendsto weight (Filter.comap Subtype.val Filter.atTop) Filter.atTop

/-- The limit along the source's real index subset, PDF p.7. -/
def indexFilter (F : LDFamily) : Filter F.index := Filter.comap Subtype.val Filter.atTop

/-- Positive exponential moment as a nonnegative integral, PDF p.7.
Divergent moments have value positive infinity. -/
def exponentialMoment (E : FiniteExperiment) (s : ℝ) : ℝ≥0∞ :=
  letI := E.measurableSpace
  ∫⁻ x, ENNReal.ofReal (Real.exp (s * E.observable x)) ∂E.measure

/-- Scaled extended logarithmic moment, PDF p.7 (LD). -/
def scaledMoment (F : LDFamily) (s : ℝ) (t : F.index) : EReal :=
  (((F.weight t)⁻¹ : ℝ) : EReal) * ENNReal.log (exponentialMoment (F.experiment t) s)

/-- Assumption LD itself, PDF pp.7--8. Convexity is a consequence, not an
extra hypothesis; e is a real representative on the specified interval. -/
def HasLD (F : LDFamily) (a b : ℝ) (e : ℝ → ℝ) : Prop :=
  ContinuousOn e (Set.Icc a b) ∧
    ∀ s ∈ Set.Icc a b, Tendsto (scaledMoment F s) (indexFilter F) (nhds (e s : EReal))

/-- Logarithmic mass of an observable event, PDF pp.8--10.
An empty event has value minus infinity. -/
def scaledEvent (F : LDFamily) (event : ∀ t : F.index, Set (F.experiment t).Space)
    (t : F.index) : EReal :=
  (((F.weight t)⁻¹ : ℝ) : EReal) * ENNReal.log ((F.experiment t).measure (event t))

/-- Strict upper-tail event from (2.5),(2.7), PDF p.8. -/
def upperTail (F : LDFamily) (theta : ℝ) (t : F.index) : Set (F.experiment t).Space :=
  {x | theta * F.weight t < (F.experiment t).observable x}

/-- Strict lower-tail event from (2.6), PDF p.8. -/
def lowerTail (F : LDFamily) (theta : ℝ) (t : F.index) : Set (F.experiment t).Space :=
  {x | (F.experiment t).observable x < theta * F.weight t}

/-- Finite-system sequence with strictly positive functionals and diverging
positive weights, PDF p.13; normalization is imposed separately where needed. -/
structure FiniteTestingFamily where
  dim : ℕ → ℕ
  dim_positive : ∀ n, 0 < dim n
  nu : ∀ n, Matrix (Fin (dim n)) (Fin (dim n)) ℂ
  omega : ∀ n, Matrix (Fin (dim n)) (Fin (dim n)) ℂ
  nu_positive : ∀ n, (nu n).PosDef
  omega_positive : ∀ n, (omega n).PosDef
  weight : ℕ → ℝ
  weight_positive : ∀ n, 0 < weight n
  weight_tendsto : Tendsto weight atTop atTop

/-- The state hypothesis introduced only after Theorem 3.4, PDF p.14. -/
def IsStateFamily (F : FiniteTestingFamily) : Prop :=
  (∀ n, (F.nu n).trace = 1) ∧ (∀ n, (F.omega n).trace = 1)

/-- A family of actual projection/effect tests, PDF pp.14--15. -/
def TestFamily (F : FiniteTestingFamily) (effect : Bool) :=
  ∀ n, {T : Matrix (Fin (F.dim n)) (Fin (F.dim n)) ℂ //
    if effect then IsEffectTest T else IsProjectionTest T}

/-- Scaled Petz logarithms with natural logs, PDF p.13. -/
def scaledRenyi (F : FiniteTestingFamily) (s : ℝ) (n : ℕ) : EReal :=
  (((F.weight n)⁻¹ : ℝ) : EReal) * petzLogOverlap (F.nu n) (F.omega n) s

/-- Natural log on a nonnegative extended value, used on genuine testing errors.
PDF p.13. An error equal to zero gives minus infinity. -/
def extendedErrorLog (x : EReal) : EReal :=
  if x = ⊤ then ⊤ else if x ≤ 0 then ⊥ else (Real.log x.toReal : EReal)

/-- Symmetric testing logarithms; the infimum precedes logarithm, PDF p.13. -/
def symmetricRate (F : FiniteTestingFamily) (effect : Bool) (n : ℕ) : EReal :=
  (((F.weight n)⁻¹ : ℝ) : EReal) * extendedErrorLog (optimalError effect (F.nu n) (F.omega n))

/-- Type-I error exponent sequence, PDF pp.14--15. -/
def typeIRate (F : FiniteTestingFamily) {effect : Bool} (T : TestFamily F effect)
    (n : ℕ) : EReal :=
  (((F.weight n)⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (evaluate (F.omega n) (1 - (T n).val)))

/-- Type-II error exponent sequence, PDF pp.14--15. -/
def typeIIRate (F : FiniteTestingFamily) {effect : Bool} (T : TestFamily F effect)
    (n : ℕ) : EReal :=
  (((F.weight n)⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (evaluate (F.nu n) (T n).val))

/-- Three distinct exponent constructions: liminf, limsup and an existing limit,
PDF pp.14--15. A genuine limit is included by an explicit Tendsto requirement. -/
inductive ExponentKind where
  | lower
  | upper
  | limit

/-- The lower, upper and existing-limit infima over exactly the admissible tests,
PDF pp.14--15. Empty admissible sets have infimum positive infinity. -/
def testingExponent (F : FiniteTestingFamily) (effect : Bool) (kind : ExponentKind)
    (admissible : TestFamily F effect → Prop) : EReal :=
  sInf {v | ∃ T : TestFamily F effect, admissible T ∧
    match kind with
    | .lower => v = Filter.liminf (typeIRate F T) atTop
    | .upper => v = Filter.limsup (typeIRate F T) atTop
    | .limit => Tendsto (typeIRate F T) atTop (nhds v)}

/-- The STRICT Hoeffding constraint, PDF pp.14--15. -/
def hoeffdingExponent (F : FiniteTestingFamily) (effect : Bool)
    (kind : ExponentKind) (r : ℝ) : EReal :=
  testingExponent F effect kind (fun T => Filter.limsup (typeIIRate F T) atTop < (-r : ℝ))

/-- Fixed-epsilon Stein constraint at EVERY index, PDF p.15. -/
def steinExponent (F : FiniteTestingFamily) (effect : Bool)
    (kind : ExponentKind) (epsilon : ℝ) : EReal :=
  testingExponent F effect kind (fun T => ∀ n, evaluate (F.nu n) (T n).val ≤ epsilon)

/-- AF1, PDF p.13: no normalization, no assumed lower testing bound.
The extended endpoint slopes may be infinite. -/
def HasAF1 (F : FiniteTestingFamily) (e : ℝ → ℝ) : Prop :=
  (∀ s ∈ Set.Icc (0 : ℝ) 1, Tendsto (scaledRenyi F s) atTop (nhds (e s : EReal))) ∧
  ContinuousOn e (Set.Icc (0 : ℝ) 1) ∧ DifferentiableOn ℝ e (Set.Ioo (0 : ℝ) 1) ∧
  rightSlope 1 e 0 < leftSlope 0 e 1

/-- AF2, PDF p.15: a finite moment-limit extension past one, differentiable there. -/
def HasAF2 (F : FiniteTestingFamily) (e : ℝ → ℝ) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧
    (∀ s ∈ Set.Ico (0 : ℝ) (1 + delta),
      Tendsto (scaledRenyi F s) atTop (nhds (e s : EReal))) ∧ DifferentiableAt ℝ e 1

/-- Distinct eigenvalues, rather than a list counted with multiplicity, PDF pp.10,20.
Degenerate entropy outcomes are measured with their full spectral projections. -/
def distinctSpectrum {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) : Finset ℝ :=
  (Finset.univ : Finset (Fin (Fintype.card I))).image (QAlgorithms.ascEigenvalues A)

/-- Schrodinger evolution exp(-itH), PDF p.19. -/
def propagator {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((-(t : ℂ) * Complex.I) • H)

/-- Time-evolved state U_t omega U_t*, PDF p.19. -/
def evolvedState {I : Type*} [Fintype I] [DecidableEq I]
    (H omega : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  propagator H t * omega * (propagator H t)ᴴ

/-- Heisenberg evolution U_t* A U_t, PDF p.19. -/
def evolvedObservable {I : Type*} [Fintype I] [DecidableEq I]
    (H A : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  (propagator H t)ᴴ * A * propagator H t

/-- The paper's nonpositive relative entropy, in nats, for faithful finite matrices,
PDF p.11 (3.1). Arbitrary positive trace is allowed. -/
def finiteRelativeEntropyNats {I : Type*} [Fintype I] [DecidableEq I]
    (nu omega : Matrix I I ℂ) : ℝ :=
  evaluate nu (cfc Real.log omega - cfc Real.log nu)

/-- The entropy observable is -log omega, PDF p.19. -/
def entropyObservable {I : Type*} [Fintype I] [DecidableEq I]
    (omega : Matrix I I ℂ) : Matrix I I ℂ := -cfc Real.log omega

/-- Time-averaged entropy production (S_t-S)/t, PDF p.19 (4.1).
The source theorem below restricts t to positive values. -/
def meanProduction {I : Type*} [Fintype I] [DecidableEq I]
    (H omega : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  ((t⁻¹ : ℝ) : ℂ) • (evolvedObservable H (entropyObservable omega) t - entropyObservable omega)

/-- Finite-time real entropic functional, PDF pp.19--20.
The faithful hypotheses guarantee strictly positive overlaps for every real s. -/
def finiteEntropic {I : Type*} [Fintype I] [DecidableEq I]
    (H omega : Matrix I I ℂ) (t s : ℝ) : ℝ :=
  Real.log (petzOverlap (evolvedState H omega t) omega s)

/-- The spectral law of MINUS log Delta_nu|omega in Omega_omega,
PDF p.12. Its mass is Tr omega, not necessarily one. -/
def finiteModularLaw {I : Type*} [Fintype I] [DecidableEq I]
    (nu omega : Matrix I I ℂ) : Measure ℝ :=
  ∑ lam ∈ distinctSpectrum nu, ∑ mu ∈ distinctSpectrum omega,
    ENNReal.ofReal (mu * (QAlgorithms.spectralProjector nu lam *
      QAlgorithms.spectralProjector omega mu).trace.re) •
        Measure.dirac (Real.log mu - Real.log lam)

/-- Two-measurement FCS, PDF p.20. The measured entropy change is
(alpha_prime-alpha)/t = (log lam-log mu)/t; no density/Jacobian is introduced. -/
def finiteFCS {I : Type*} [Fintype I] [DecidableEq I]
    (H omega : Matrix I I ℂ) (t : ℝ) : Measure ℝ :=
  ∑ lam ∈ distinctSpectrum omega, ∑ mu ∈ distinctSpectrum omega,
    ENNReal.ofReal ((propagator H t * omega * QAlgorithms.spectralProjector omega lam *
      (propagator H t)ᴴ * QAlgorithms.spectralProjector omega mu).trace.re) •
        Measure.dirac ((Real.log lam - Real.log mu) / t)

/-- Finite-system time reversal: one orthonormal basis makes both H and omega
real, PDF p.21. The unitary changes the original orthonormal coordinates. -/
def IsFiniteTRI {I : Type*} [Fintype I] [DecidableEq I]
    (H omega : Matrix I I ℂ) : Prop :=
  ∃ U : Matrix.unitaryGroup I ℂ, ∀ i j,
    (((U : Matrix I I ℂ)ᴴ * H * (U : Matrix I I ℂ)) i j).im = 0 ∧
    (((U : Matrix I I ℂ)ᴴ * omega * (U : Matrix I I ℂ)) i j).im = 0

/-- A genuine finite dynamical system, PDF pp.19,24. -/
structure FiniteSystem where
  dim : ℕ
  dim_positive : 0 < dim
  H : Matrix (Fin dim) (Fin dim) ℂ
  H_hermitian : H.IsHermitian
  omega : Matrix (Fin dim) (Fin dim) ℂ
  omega_positive : omega.PosDef
  omega_normalized : omega.trace = 1

/-- Weak convergence of finite Borel measures tested against every bounded
continuous complex function, PDF p.24. All uses have finite measures. -/
def WeakMeasureLimit {T : Type*} (mu : T → Measure ℝ) (l : Filter T)
    (nu : Measure ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℂ, Tendsto (fun t => ∫ x : ℝ, f x ∂mu t) l
    (nhds (∫ x : ℝ, f x ∂nu))

/-- The thermodynamic FCS, constructed as the unique probability weak limit
when it exists, PDF p.24. Zero is only an off-domain fallback, never used under TD. -/
def tdFCS (Q : ℕ → FiniteSystem) (t : ℝ) : Measure ℝ :=
  if h : ∃ P : Measure ℝ, IsProbabilityMeasure P ∧
      WeakMeasureLimit (fun m => finiteFCS (Q m).H (Q m).omega t) atTop P then
    h.choose else 0

/-- Thermodynamic entropic functional computed from the scalar limit, PDF p.24.
Under TD this defining set is a nonempty singleton; no unbounded real infimum occurs. -/
def tdEntropic (Q : ℕ → FiniteSystem) (t s : ℝ) : ℝ :=
  sInf {v : ℝ | Tendsto (fun m => finiteEntropic (Q m).H (Q m).omega t s) atTop (nhds v)}

/-- TD, including the open symmetric interval containing [0,1], PDF p.24. -/
def HasTD (Q : ℕ → FiniteSystem) (I : Set ℝ) : Prop :=
  IsOpen I ∧ Set.OrdConnected I ∧ Set.Icc (0 : ℝ) 1 ⊆ I ∧
  (∀ s ∈ I, 1 - s ∈ I) ∧ ∀ t : ℝ, 0 < t → ∀ s ∈ I,
    ∃ v : ℝ, Tendsto (fun m => finiteEntropic (Q m).H (Q m).omega t s) atTop (nhds v)

/-- Large-time entropic functional computed after the thermodynamic limit,
PDF p.25. Under LT this real-infimum set is a nonempty singleton. -/
def ltEntropic (Q : ℕ → FiniteSystem) (s : ℝ) : ℝ :=
  sInf {v : ℝ | Tendsto (fun t : ℝ => tdEntropic Q t s / t) atTop (nhds v)}

/-- LT adds finite long-time limits and differentiability on I, PDF p.25. -/
def HasLT (Q : ℕ → FiniteSystem) (I : Set ℝ) : Prop :=
  HasTD Q I ∧ (∀ s ∈ I, ∃ v : ℝ,
    Tendsto (fun t : ℝ => tdEntropic Q t s / t) atTop (nhds v)) ∧
      DifferentiableOn ℝ (ltEntropic Q) I

/-- Inner thermodynamic mean-production limit, PDF p.26.
The existence of this limit is conclusion content in the law below. -/
def tdMeanProduction (Q : ℕ → FiniteSystem) (t : ℝ) : ℝ :=
  sInf {v : ℝ | Tendsto (fun m => evaluate (Q m).omega
    (meanProduction (Q m).H (Q m).omega t)) atTop (nhds v)}

/-- Inner thermodynamic relative-entropy limit, PDF p.26.
Used only at fixed positive t under LT, where its set is a singleton. -/
def tdRelativeEntropy (Q : ℕ → FiniteSystem) (t : ℝ) : ℝ :=
  sInf {v : ℝ | Tendsto (fun m => finiteRelativeEntropyNats
    (evolvedState (Q m).H (Q m).omega t) (Q m).omega) atTop (nhds v)}

/-! Sanity tests pin the conventions without proving any source theorem. -/

example {I : Type*} [Fintype I] [DecidableEq I] :
    IsProjectionTest (0 : Matrix I I ℂ) := by
  exact ⟨Matrix.isHermitian_zero, by simp⟩

example {I : Type*} [Fintype I] [DecidableEq I] (nu omega : Matrix I I ℂ) :
    testingError nu omega 0 = omega.trace.re := by
  simp [testingError, evaluate]

example (a b s : ℝ) (e : ℝ → ℝ) (h : s ∉ Set.Icc a b) :
    extendedConvex a b e s = ⊤ := by simp [extendedConvex, h]

example : ENNReal.log 0 = ⊥ ∧ ENNReal.log ⊤ = ⊤ := by simp

example : extendedErrorLog 0 = ⊥ := by simp [extendedErrorLog]

example {F : FiniteTestingFamily} {effect : Bool} {T : TestFamily F effect}
    {epsilon : ℝ} (h : ∀ n, evaluate (F.nu n) (T n).val ≤ epsilon) (n : ℕ) :
    evaluate (F.nu n) (T n).val ≤ epsilon := h n

example {I : Type*} [Fintype I] [DecidableEq I] (omega : Matrix I I ℂ) :
    evolvedState (0 : Matrix I I ℂ) omega 0 = omega := by
  simp [evolvedState, propagator]

example {I : Type*} [Fintype I] [DecidableEq I] (omega : Matrix I I ℂ) :
    finiteRelativeEntropyNats omega omega = 0 := by
  simp [finiteRelativeEntropyNats, evaluate]

example (mu : Measure ℝ) : WeakMeasureLimit (fun _ : ℕ => mu) atTop mu := by
  intro f
  exact tendsto_const_nhds

end QAlgorithms.Papers.Independent.Claimed50.P15


