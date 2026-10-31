-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34
-- name    : QAlgorithms_Papers_Independent_Intake100_P34
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T17:59:18.314614+00:00
-- url     : https://prove2.me/theorems/c5606c28-e226-490f-a456-ee388874ff15
-- title:
--   Definitions for Entropic fluctuations of quantum dynamical semigroups
-- statement:
--   The objects the formalized statements of *Entropic fluctuations of quantum dynamical semigroups* (arXiv:1305.4409) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `EntropyCoordinates`: PDF p.6: real reservoir coordinates with their usual finite dimensional topology.
--   - `CVec`: PDF p.7: complexified reservoir coordinates.
--   - `weightedAdjoint`: PDF p.5: the adjoint for tr(rho X*Y); only used at faithful rho.
--   - `expect`: PDF p.3: evaluation of the state on an observable.
--   - `IsImproving`: PDF p.3: strictly positive image of every nonzero positive input.
--   - `DaviesIrreducible`: PDF p.4: Davies irreducibility, including the dimension-one zero-map case.
--   - `qdsEvolution`: PDF p.4: exp(tL) is the actual finite-dimensional operator exponential.
--   - `IsCPSemigroup`: PDF p.4: CP semigroup, with no normalization requirement.
--   - `IsUnitalSemigroup`: PDF p.4: unitality in the Heisenberg picture.
--   - `IsQDS`: PDF p.4: a quantum dynamical semigroup is CP and unital.
--   - `StationaryDensity`: PDF p.4: a stationary density satisfies L*(rho)=0.
--   - `RelaxesExponentially`: PDF p.4: a common decay exponent, with prefactors allowed to depend on the initial state.
--   - `abscissa`: PDF p.5: spectral abscissa on a nonzero finite matrix algebra.
--   - `IsPerron`: PDF pp.5,25: algebraically simple, strictly dominant real eigenvalue.
--   - `hamiltonianPart`: PDF p.5, (5): Hamiltonian part with the source's positive i.
--   - `lindblad`: PDF p.5, (5): the specified unital Lindblad expression.
--   - `DetailedBalance`: PDF p.5: detailed balance includes faithfulness, QDS, stationarity and a symmetric CP part.
--   - `IsReversal`: PDF p.6: an involutive antilinear unital star automorphism.
--   - `TimeReversible`: PDF p.6, Definition 2.4(b): time reversal of a pair.
--   - `matrixLog`: PDF p.21: log rho, by finite-dimensional self-adjoint functional calculus.
--   - `densityComplexPower`: PDF p.21: complex powers of a faithful density, exp(z log rho).
--   - `rGroup`: PDF p.21: both sandwich factors have positive exponent.
--   - `densityModularAction`: PDF p.21: the densityModularAction action has opposite exponents.
--   - `logEigenvalues`: PDF p.22: real log-density eigenvalues, repeated eigenvalues removed.
--   - `logProjection`: PDF p.22: spectral projection of log rho, built from rho by functional calculus.
--   - `frequencies`: PDF p.22: all differences of log-density eigenvalues.
--   - `frequencyComponent`: PDF p.22: the constructed frequency component, not a family assumed to decompose Phi.
--   - `deformation`: PDF p.22, (41): the deformation defined first by similarity.
--   - `dissipation`: PDF p.5: dissipation is sesquilinear, with both required stars.
--   - `qdsGibbsDensity`: PDF p.6: Gibbs density for a positive inverse temperature.
--   - `DBData`: PDF pp.5–6, (DB): specified reservoir decomposition and chosen DB Lindblad witnesses. No ER, TR, thermal condition, or fluctuation conclusion is a field.
--   - `reservoirGenerator`: PDF p.6: the reservoirGenerator generator is the specified sum.
--   - `ER`: PDF p.6, (ER): positivity improving at every strictly positive time.
--   - `TR`: PDF p.6, (TR): the same reversal for every reservoir.
--   - `Thermal`: PDF p.6, (KMS_beta): a common self-adjoint Hamiltonian and positive temperatures.
--   - `entropyTilt`: PDF p.7, (6): the source's right-multiplication tilt.
--   - `countingParameterEmbedding`: PDF p.7: embedding of real counting parameters.
--   - `entropySpectralCGF`: PDF p.7: the real dominant spectral value, not a complex spectral-abscissa extension.
--   - `traceTransform`: PDF p.7: finite-time trace transform.
--   - `finiteCGF`: PDF p.7: finite-time real logarithm for real parameters.
--   - `noJumpK`: PDF p.20: the no-jump matrix K, with the positive iT term.
--   - `noJump`: PDF p.20: no-jump superoperator, distinct from the deformed Davies generator.
--   - `Jump`: PDF p.20: a reservoir and one of its log-density frequency differences.
--   - `jumpAt`: PDF p.20: the interaction-picture CP jump.
--   - `orderedSimplex`: PDF p.20: ordered jump times, including the zero-dimensional singleton when N=0.
--   - `Trajectory`: PDF p.21: all jump counts, label sequences and time coordinates. The measure below restricts times to the ordered simplex.
--   - `pathWeight`: PDF p.21, (40): Phi_N ∘ ... ∘ Phi_1 applied to 1; fold order is chronological.
--   - `trajectoryMeasure`: PDF p.21: the actual path measure, summing every N and all finite labels, with Lebesgue ordered-simplex densities. The N=0 term is exactly the source's empty-path mass.
--   - `pathRate`: PDF p.21: evaluate entropy rates, defined only at positive counting times in results.
--   - `efcs`: PDF pp.7,21: EFCS is a measurable pushforward of the constructed trajectory measure. At t=0 choose delta_0; its transform is one but does not otherwise determine a unique law.
--   - `reservoirPairing`: PDF p.7: Euclidean scalar product of reservoir coordinates.
--   - `countingCoordinateDerivative`: PDF pp.8–9: first countingCoordinateDerivative derivative at an arbitrary real point.
--   - `coordinateHessianAtZero`: PDF p.9: Hessian at zero. Analyticity is a conclusion, not a derivative hypothesis.
--   - `entropyMean`: PDF p.8: minus the gradient of e at zero.
--   - `rateFunction`: PDF p.8: the extended-real Fenchel transform. The supremum can be +infinity.
--   - `centeredGaussianLaw`: PDF p.9: centered Gaussian, including singular covariance, transported to coordinate space.
--   - `lawMean`: PDF p.9: finite-time evaluate of a coordinate law.
--   - `fluctuations`: PDF p.9: centered, square-root-time fluctuation map.
--   - `HasCLT`: PDF p.9: CLT on Gaussian continuity sets, retaining the printed finite-time centering.
--   - `scaledLog`: PDF p.8: log zero is -infinity; no conversion of log probability to a finite real.
--   - `rightDerivative`: PDF pp.9–10: extended right derivative, preserving the possible +infinite value at the boundary.
--   - `reservoirEntropyProduction`: PDF p.9, (14): entropy production from the actual dual reservoir evolutions.
--   - `entropyFlux`: PDF p.10: entropy flux out of reservoir j.
--   - `steadyDensity`: PDF p.10: the constructed unique stationary density; the default is used only outside ER.
--   - `centeredCurrent`: PDF p.10: centered entropy current.
--   - `adjointCurrent`: PDF p.10: the rho_+-adjoint image, not a positive part.
--   - `energyFlux`: PDF p.11: energy flux out of the reservoir into the system.
--   - `energyMean`: PDF p.11: steady energy flux.
--   - `energyLaw`: PDF p.11: energetic FCS is the pushforward s ↦ -s/beta.
--   - `energyCGF`: PDF p.11: corrected positive-Laplace energy CGF, forced by its displayed transform identity.
--   - `ComplexLimit`: PDF p.26: local holomorphic continuation and the eventually defined logarithm branch. The branch is normalized at the real base point and is not principal Complex.log.
--   - `length`: PDF p.8: Euclidean length in the real reservoir-coordinate space.
--   - `currentCorrelation`: PDF p.10: the first correlation integrand in the second-entropySpectralCGF formula.
--   - `currentCorrection`: PDF p.10: the additional reservoir-generator integrand.
--   - `energyCorrelation`: PDF pp.11–13: ordered equilibrium energy correlation.
--   - `ResponseFamily`: PDF p.12: the thermal componentwise response family, with no time-reversal field. Data exist only on the stated open neighborhood. The extension by zero in regularity and response definitions has no effect near zero. RE is a property of the actual generators.
--   - `equilibrium`: PDF p.12: the equilibrium data at the actual zero force.
--   - `responseFlux`: PDF p.12: actual steady flux, extended outside the domain solely to take ambient derivatives.
--   - `kinetic`: PDF p.12: kinetic coefficients are derivatives of the actual steady flux.
--   - `responseCGF`: PDF pp.12–13: positive-Laplace energy CGF with beta=beta0-zeta.
--   - `negativeResponseCGF`: PDF p.13: the distinct negative-Laplace convention, whose first energy derivative has a minus.
--   - `greenKubo`: PDF p.13: corrected ordered Green–Kubo expression for the physical force beta0-beta.
--   - `energies`: PDF p.16: distinct real energy eigenvalues.
--   - `energyDifferenceSet`: PDF p.16: all Bohr differences, with duplicates removed.
--   - `energyProjection`: PDF p.16: the energy spectral projection is constructed from H.
--   - `bohrComponent`: PDF p.16, (31): the lowering component, with mu-nu=w and P_nu Q P_mu.
--   - `DaviesData`: PDF pp.15–16: finite Davies spectral data; these are not an assumed microscopic limit.
--   - `daviesT`: PDF p.16: the Hamiltonian correction constructed from s and lowering components.
--   - `daviesPhi`: PDF p.16: the CP part constructed from the positive h matrices.
--   - `daviesGenerator`: PDF p.16: the constructed finite Davies reservoir generator.
--   - `commonCommutant`: PDF p.17: matrices commuting with the system Hamiltonian and a specified coupling set.
--   - `allCouplings`: PDF p.17: the full family of small-system couplings.
--   - `allBohrComponents`: PDF p.17: the full family V of constructed Bohr components.
--   - `daviesEntropyProduction`: PDF p.17: entropy production from the constructed finite Davies dynamics.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, https://arxiv.org/abs/1305.4409v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

/-!
Statements from Jakšić–Pillet–Westrich, arXiv:1305.4409v2.
Accepted primitives are imported directly; paper-specific definitions retain the
Heisenberg convention and the unnormalized trace.
Source corrections and deferred microscopic interfaces are documented in the unit artifacts.
Compilation is pending the separate mechanical stage.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder
open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P34

-- Exact accepted definitions, checked at their recorded source bodies.
open QAlgorithms (IsDensityMatrix)
open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)
open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)
open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P69 (Faithful)
open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)
open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate finiteRelativeEntropyNats entropyObservable)
open QAlgorithms.Papers.Independent.Claimed50.P43 (chaotic)

/-- PDF p.3: complex linear superoperators. -/
local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

/-- PDF p.6: real reservoir coordinates with their usual finite dimensional topology. -/
abbrev EntropyCoordinates (M : ℕ) := Fin M → ℝ

/-- PDF p.7: complexified reservoir coordinates. -/
abbrev CVec (M : ℕ) := Fin M → ℂ

/-- PDF p.5: the adjoint for tr(rho X*Y); only used at faithful rho. -/
def weightedAdjoint {d : ℕ} (rho : Mat d) (F : GeneratorMap d) : GeneratorMap d :=
  (LinearMap.mulRight ℂ rho⁻¹).comp ((hsAdjoint F).comp (LinearMap.mulRight ℂ rho))

/-- PDF p.3: evaluation of the state on an observable. -/
def expect {d : ℕ} (rho X : Mat d) : ℂ := (rho * X).trace

/-- PDF p.3: strictly positive image of every nonzero positive input. -/
def IsImproving {d : ℕ} (F : GeneratorMap d) : Prop :=
  ∀ X, X.PosSemidef → X ≠ 0 → (F X).PosDef

/-- PDF p.4: Davies irreducibility, including the dimension-one zero-map case. -/
def DaviesIrreducible {d : ℕ} (F : GeneratorMap d) : Prop :=
  IsPositiveMap F ∧ ∀ P : Mat d, P * P = P → Pᴴ = P →
    ∀ c : ℝ, 0 < c → ((c : ℂ) • P - F P).PosSemidef → P = 0 ∨ P = 1

/-- PDF p.4: exp(tL) is the actual finite-dimensional operator exponential. -/
def qdsEvolution {d : ℕ} (L : GeneratorMap d) (t : ℝ) : GeneratorMap d :=
  (QAlgorithms.Papers.Independent.Dependency50.P16.semigroupEvolution L t).toLinearMap

/-- PDF p.4: CP semigroup, with no normalization requirement. -/
def IsCPSemigroup {d : ℕ} (L : GeneratorMap d) : Prop :=
  ∀ t : ℝ, 0 < t → QAlgorithms.Entanglement.IsCompletelyPositive (qdsEvolution L t)

/-- PDF p.4: unitality in the Heisenberg picture. -/
def IsUnitalSemigroup {d : ℕ} (L : GeneratorMap d) : Prop :=
  ∀ t : ℝ, 0 < t → qdsEvolution L t 1 = 1

/-- PDF p.4: a quantum dynamical semigroup is CP and unital. -/
def IsQDS {d : ℕ} (L : GeneratorMap d) : Prop := IsCPSemigroup L ∧ IsUnitalSemigroup L

/-- PDF p.4: a stationary density satisfies L*(rho)=0. -/
def StationaryDensity {d : ℕ} (L : GeneratorMap d) (rho : Mat d) : Prop := hsAdjoint L rho = 0

/-- PDF p.4: a common decay exponent, with prefactors allowed to depend on the initial state. -/
def RelaxesExponentially {d : ℕ} (L : GeneratorMap d) (rhoPlus : Mat d) : Prop :=
  Faithful rhoPlus ∧ StationaryDensity L rhoPlus ∧
    ∃ gamma : ℝ, 0 < gamma ∧ ∀ rho, IsDensityMatrix rho →
      ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, ∀ t ≥ T,
        ‖hsAdjoint (qdsEvolution L t) rho - rhoPlus‖ ≤ C * Real.exp (-gamma * t)

/-- PDF p.5: spectral abscissa on a nonzero finite matrix algebra. -/
def abscissa {d : ℕ} (L : GeneratorMap d) : ℝ :=
  sSup {r : ℝ | ∃ z : ℂ, L.charpoly.IsRoot z ∧ r = z.re}

/-- PDF pp.5,25: algebraically simple, strictly dominant real eigenvalue. -/
def IsPerron {d : ℕ} (L : GeneratorMap d) (ell : ℝ) : Prop :=
  L.charpoly.IsRoot (ell : ℂ) ∧ Polynomial.rootMultiplicity (ell : ℂ) L.charpoly = 1 ∧
    ∀ z : ℂ, L.charpoly.IsRoot z → z ≠ (ell : ℂ) → z.re < ell

/-- PDF p.5, (5): Hamiltonian part with the source's positive i. -/
def hamiltonianPart {d : ℕ} (T : Mat d) : GeneratorMap d :=
  Complex.I • (LinearMap.mulLeft ℂ T - LinearMap.mulRight ℂ T)

/-- PDF p.5, (5): the specified unital Lindblad expression. -/
def lindblad {d : ℕ} (T : Mat d) (Phi : GeneratorMap d) : GeneratorMap d :=
  hamiltonianPart T - (1 / 2 : ℂ) •
    (LinearMap.mulLeft ℂ (Phi 1) + LinearMap.mulRight ℂ (Phi 1)) + Phi

/-- PDF p.5: detailed balance includes faithfulness, QDS, stationarity and a symmetric CP part. -/
def DetailedBalance {d : ℕ} (rho : Mat d) (L : GeneratorMap d) : Prop :=
  Faithful rho ∧ IsQDS L ∧ StationaryDensity L rho ∧
    ∃ T : Mat d, T.IsHermitian ∧ ∃ Phi : GeneratorMap d,
      QAlgorithms.Entanglement.IsCompletelyPositive Phi ∧
      L = lindblad T Phi ∧ weightedAdjoint rho Phi = Phi

/-- PDF p.6: an involutive antilinear unital star automorphism. -/
def IsReversal {d : ℕ} (Theta : Mat d → Mat d) : Prop :=
  (∀ X Y, Theta (X + Y) = Theta X + Theta Y) ∧
  (∀ c : ℂ, ∀ X, Theta (c • X) = conj c • Theta X) ∧
  (∀ X Y, Theta (X * Y) = Theta X * Theta Y) ∧
  Theta 1 = 1 ∧ (∀ X, Theta (Xᴴ) = (Theta X)ᴴ) ∧ ∀ X, Theta (Theta X) = X

/-- PDF p.6, Definition 2.4(b): time reversal of a pair. -/
def TimeReversible {d : ℕ} (rho : Mat d) (L : GeneratorMap d) (Theta : Mat d → Mat d) : Prop :=
  IsReversal Theta ∧ Theta rho = rho ∧
    ∀ X, weightedAdjoint rho L (Theta X) = Theta (L X)

/-- PDF p.21: log rho, by finite-dimensional self-adjoint functional calculus. -/
def matrixLog {d : ℕ} (rho : Mat d) : Mat d := cfc Real.log rho

/-- PDF p.21: complex powers of a faithful density, exp(z log rho). -/
def densityComplexPower {d : ℕ} (rho : Mat d) (z : ℂ) : Mat d :=
  NormedSpace.exp (z • matrixLog rho)

/-- PDF p.21: both sandwich factors have positive exponent. -/
def rGroup {d : ℕ} (rho : Mat d) (z : ℂ) : GeneratorMap d :=
  sandwich (densityComplexPower rho z) (densityComplexPower rho z)

/-- PDF p.21: the densityModularAction action has opposite exponents. -/
def densityModularAction {d : ℕ} (rho : Mat d) (z : ℂ) : GeneratorMap d :=
  sandwich (densityComplexPower rho z) (densityComplexPower rho (-z))

/-- PDF p.22: real log-density eigenvalues, repeated eigenvalues removed. -/
def logEigenvalues {d : ℕ} (rho : Mat d) : Finset ℝ :=
  rho.charpoly.roots.toFinset.image (fun z => Real.log z.re)

/-- PDF p.22: spectral projection of log rho, built from rho by functional calculus. -/
def logProjection {d : ℕ} (rho : Mat d) (a : ℝ) : Mat d :=
  cfc (fun r : ℝ => if Real.log r = a then 1 else 0) rho

/-- PDF p.22: all differences of log-density eigenvalues. -/
def frequencies {d : ℕ} (rho : Mat d) : Finset ℝ :=
  ((logEigenvalues rho).product (logEigenvalues rho)).image (fun p => p.1 - p.2)

/-- PDF p.22: the constructed frequency component, not a family assumed to decompose Phi. -/
def frequencyComponent {d : ℕ} (rho : Mat d) (Phi : GeneratorMap d) (w : ℝ) : GeneratorMap d :=
  ∑ a ∈ logEigenvalues rho, ∑ b ∈ logEigenvalues rho,
    ∑ c ∈ logEigenvalues rho, ∑ e ∈ logEigenvalues rho,
      if a - b = w ∧ c - e = w then
        (sandwich (logProjection rho b) (logProjection rho e)).comp
          (Phi.comp (sandwich (logProjection rho a) (logProjection rho c)))
      else 0

/-- PDF p.22, (41): the deformation defined first by similarity. -/
def deformation {d : ℕ} (rho : Mat d) (L : GeneratorMap d) (z : ℂ) : GeneratorMap d :=
  (rGroup rho (z / 2)).comp (L.comp (rGroup rho (-z / 2)))

/-- PDF p.5: dissipation is sesquilinear, with both required stars. -/
def dissipation {d : ℕ} (L : GeneratorMap d) (A B : Mat d) : Mat d :=
  L (Aᴴ * B) - L (Aᴴ) * B - Aᴴ * L B

/-- PDF p.6: Gibbs density for a positive inverse temperature. -/
def qdsGibbsDensity {d : ℕ} (H : Mat d) (beta : ℝ) : Mat d :=
  let E := NormedSpace.exp ((-beta : ℂ) • H)
  E.trace⁻¹ • E

/-- Sanity: at time zero the actual exponential is the identity superoperator. -/
example {d : ℕ} (L : GeneratorMap d) : qdsEvolution L 0 = 1 := by
  change (NormedSpace.exp ((0 : ℂ) • LinearMap.toContinuousLinearMap L)).toLinearMap = 1
  have hzero : (0 : ℂ) • LinearMap.toContinuousLinearMap L =
      (0 : Mat d →L[ℂ] Mat d) := by
    apply ContinuousLinearMap.ext
    intro X
    apply Matrix.ext
    intro i j
    change (0 : ℂ) * (L X) i j = 0
    exact zero_mul _
  calc
    (NormedSpace.exp ((0 : ℂ) • LinearMap.toContinuousLinearMap L)).toLinearMap =
        (NormedSpace.exp (0 : Mat d →L[ℂ] Mat d)).toLinearMap :=
      congrArg (fun A : Mat d →L[ℂ] Mat d => (NormedSpace.exp A).toLinearMap) hzero
    _ = (1 : Mat d →L[ℂ] Mat d).toLinearMap :=
      congrArg (fun A : Mat d →L[ℂ] Mat d => A.toLinearMap) NormedSpace.exp_zero
    _ = 1 := rfl

/-- Sanity: the Hamiltonian term vanishes for the zero Hamiltonian. -/
example {d : ℕ} : hamiltonianPart (0 : Mat d) = 0 := by
  simp [hamiltonianPart]

/-- Sanity: the dissipation of a zero generator is zero, with no state assumptions. -/
example {d : ℕ} (A B : Mat d) : dissipation (0 : GeneratorMap d) A B = 0 := by
  simp [dissipation]

/-- Sanity: zero complex power is the identity, including the one-level case. -/
example {d : ℕ} (rho : Mat d) : densityComplexPower rho 0 = 1 := by
  simp [densityComplexPower]

/-- PDF pp.5–6, (DB): specified reservoir decomposition and chosen DB Lindblad witnesses.
No ER, TR, thermal condition, or fluctuation conclusion is a field. -/
structure DBData (d M : ℕ) where
  dimension_pos : 0 < d
  rho : Fin M → Mat d
  generator : Fin M → GeneratorMap d
  faithful : ∀ j, Faithful (rho j)
  qds : ∀ j, IsQDS (generator j)
  stationary : ∀ j, StationaryDensity (generator j) (rho j)
  T : Fin M → Mat d
  T_hermitian : ∀ j, (T j).IsHermitian
  Phi : Fin M → GeneratorMap d
  Phi_cp : ∀ j, QAlgorithms.Entanglement.IsCompletelyPositive (Phi j)
  decomposition : ∀ j, generator j = lindblad (T j) (Phi j)
  Phi_symmetric : ∀ j, weightedAdjoint (rho j) (Phi j) = Phi j

/-- PDF p.6: the reservoirGenerator generator is the specified sum. -/
def reservoirGenerator {d M : ℕ} (D : DBData d M) : GeneratorMap d := ∑ j, D.generator j

/-- PDF p.6, (ER): positivity improving at every strictly positive time. -/
def ER {d M : ℕ} (D : DBData d M) : Prop := ∀ t : ℝ, 0 < t → IsImproving (qdsEvolution (reservoirGenerator D) t)

/-- PDF p.6, (TR): the same reversal for every reservoir. -/
def TR {d M : ℕ} (D : DBData d M) : Prop :=
  ∃ Theta : Mat d → Mat d, IsReversal Theta ∧ ∀ j, TimeReversible (D.rho j) (D.generator j) Theta

/-- PDF p.6, (KMS_beta): a common self-adjoint Hamiltonian and positive temperatures. -/
def Thermal {d M : ℕ} (D : DBData d M) (H : Mat d) (beta : EntropyCoordinates M) : Prop :=
  H.IsHermitian ∧ (∀ j, 0 < beta j) ∧ ∀ j, D.rho j = qdsGibbsDensity H (beta j)

/-- PDF p.7, (6): the source's right-multiplication tilt. -/
def entropyTilt {d M : ℕ} (D : DBData d M) (a : CVec M) : GeneratorMap d :=
  ∑ j, (LinearMap.mulRight ℂ (densityComplexPower (D.rho j) (a j))).comp
    ((D.generator j).comp (LinearMap.mulRight ℂ (densityComplexPower (D.rho j) (-a j))))

/-- PDF p.7: embedding of real counting parameters. -/
def countingParameterEmbedding {M : ℕ} (a : EntropyCoordinates M) : CVec M := fun j => (a j : ℂ)

/-- PDF p.7: the real dominant spectral value, not a complex spectral-abscissa extension. -/
def entropySpectralCGF {d M : ℕ} (D : DBData d M) (a : EntropyCoordinates M) : ℝ := abscissa (entropyTilt D (countingParameterEmbedding a))

/-- PDF p.7: finite-time trace transform. -/
def traceTransform {d M : ℕ} (D : DBData d M) (rho : Mat d) (t : ℝ) (a : CVec M) : ℂ :=
  expect rho (qdsEvolution (entropyTilt D a) t 1)

/-- PDF p.7: finite-time real logarithm for real parameters. -/
def finiteCGF {d M : ℕ} (D : DBData d M) (rho : Mat d) (t : ℝ) (a : EntropyCoordinates M) : ℝ :=
  Real.log (traceTransform D rho t (countingParameterEmbedding a)).re

/-- PDF p.20: the no-jump matrix K, with the positive iT term. -/
def noJumpK {d M : ℕ} (D : DBData d M) : Mat d :=
  ∑ j, ((1 / 2 : ℂ) • D.Phi j 1 + Complex.I • D.T j)

/-- PDF p.20: no-jump superoperator, distinct from the deformed Davies generator. -/
def noJump {d M : ℕ} (D : DBData d M) : GeneratorMap d :=
  -LinearMap.mulLeft ℂ ((noJumpK D)ᴴ) - LinearMap.mulRight ℂ (noJumpK D)

/-- PDF p.20: a reservoir and one of its log-density frequency differences. -/
abbrev Jump {d M : ℕ} (D : DBData d M) := Σ j : Fin M, ↥(frequencies (D.rho j))

/-- PDF p.20: the interaction-picture CP jump. -/
def jumpAt {d M : ℕ} (D : DBData d M) (q : Jump D) (s : ℝ) : GeneratorMap d :=
  (qdsEvolution (noJump D) (-s)).comp
    ((frequencyComponent (D.rho q.1) (D.Phi q.1) q.2.val).comp (qdsEvolution (noJump D) s))

/-- PDF p.20: ordered jump times, including the zero-dimensional singleton when N=0. -/
def orderedSimplex (N : ℕ) (t : ℝ) : Set (Fin N → ℝ) :=
  {s | (∀ k, 0 ≤ s k ∧ s k ≤ t) ∧ Monotone s}

/-- PDF p.21: all jump counts, label sequences and time coordinates.
The measure below restricts times to the ordered simplex. -/
abbrev Trajectory {d M : ℕ} (D : DBData d M) :=
  Σ N : ℕ, (Fin N → Jump D) × (Fin N → ℝ)

/-- PDF p.21, (40): Phi_N ∘ ... ∘ Phi_1 applied to 1; fold order is chronological. -/
def pathWeight {d M N : ℕ} (D : DBData d M) (rho : Mat d) (t : ℝ)
    (q : Fin N → Jump D) (s : Fin N → ℝ) : ℝ :=
  evaluate (hsAdjoint (qdsEvolution (noJump D) t) rho)
    ((List.finRange N).foldl (fun X k => jumpAt D (q k) (s k) X) 1)

/-- PDF p.21: the actual path measure, summing every N and all finite labels, with Lebesgue
ordered-simplex densities. The N=0 term is exactly the source's empty-path mass. -/
def trajectoryMeasure {d M : ℕ} (D : DBData d M) (rho : Mat d) (t : ℝ) :
    Measure (Trajectory D) :=
  Measure.sum (fun N : ℕ => ∑ q : Fin N → Jump D,
    Measure.map (fun s : Fin N → ℝ => (⟨N, (q, s)⟩ : Trajectory D))
      ((volume.restrict (orderedSimplex N t)).withDensity
        (fun s => ENNReal.ofReal (pathWeight D rho t q s))))

/-- PDF p.21: evaluate entropy rates, defined only at positive counting times in results. -/
def pathRate {d M : ℕ} (D : DBData d M) (t : ℝ) (xi : Trajectory D) : EntropyCoordinates M :=
  fun j => (∑ k : Fin xi.1, if (xi.2.1 k).1 = j then (xi.2.1 k).2.val else 0) / t

/-- PDF pp.7,21: EFCS is a measurable pushforward of the constructed trajectory measure.
At t=0 choose delta_0; its transform is one but does not otherwise determine a unique law. -/
def efcs {d M : ℕ} (D : DBData d M) (rho : Mat d) (t : ℝ) : Measure (EntropyCoordinates M) :=
  if t = 0 then Measure.dirac 0 else Measure.map (pathRate D t) (trajectoryMeasure D rho t)

/-- PDF p.7: Euclidean scalar product of reservoir coordinates. -/
def reservoirPairing {M : ℕ} (a b : EntropyCoordinates M) : ℝ := ∑ j, a j * b j

/-- PDF pp.8–9: first countingCoordinateDerivative derivative at an arbitrary real point. -/
def countingCoordinateDerivative {M : ℕ} (f : EntropyCoordinates M → ℝ) (j : Fin M) (a : EntropyCoordinates M) : ℝ :=
  deriv (fun x : ℝ => f (Function.update a j x)) (a j)

/-- PDF p.9: Hessian at zero. Analyticity is a conclusion, not a derivative hypothesis. -/
def coordinateHessianAtZero {M : ℕ} (f : EntropyCoordinates M → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun j k => countingCoordinateDerivative (countingCoordinateDerivative f j) k 0

/-- PDF p.8: minus the gradient of e at zero. -/
def entropyMean {d M : ℕ} (D : DBData d M) : EntropyCoordinates M := fun j => -countingCoordinateDerivative (entropySpectralCGF D) j 0

/-- PDF p.8: the extended-real Fenchel transform. The supremum can be +infinity. -/
def rateFunction {d M : ℕ} (D : DBData d M) (s : EntropyCoordinates M) : EReal :=
  ⨆ a : EntropyCoordinates M, ((-reservoirPairing a s - entropySpectralCGF D a : ℝ) : EReal)

/-- PDF p.9: centered Gaussian, including singular covariance, transported to coordinate space. -/
def centeredGaussianLaw {M : ℕ} (C : Matrix (Fin M) (Fin M) ℝ) : Measure (EntropyCoordinates M) :=
  Measure.map (fun x : EuclideanSpace ℝ (Fin M) => fun j => x j)
    (ProbabilityTheory.multivariateGaussian 0 C)

/-- PDF p.9: finite-time evaluate of a coordinate law. -/
def lawMean {M : ℕ} (P : Measure (EntropyCoordinates M)) : EntropyCoordinates M := fun j => ∫ s, s j ∂P

/-- PDF p.9: centered, square-root-time fluctuation map. -/
def fluctuations {M : ℕ} (P : Measure (EntropyCoordinates M)) (t : ℝ) (s : EntropyCoordinates M) : EntropyCoordinates M :=
  Real.sqrt t • (s - lawMean P)

/-- PDF p.9: CLT on Gaussian continuity sets, retaining the printed finite-time centering. -/
def HasCLT {M : ℕ} (P : ℝ → Measure (EntropyCoordinates M)) (C : Matrix (Fin M) (Fin M) ℝ) : Prop :=
  C.PosSemidef ∧ ∀ G : Set (EntropyCoordinates M), MeasurableSet G → centeredGaussianLaw C (frontier G) = 0 →
    Tendsto (fun t : ℝ => (P t ((fluctuations (P t) t) ⁻¹' G)).toReal)
      atTop (nhds ((centeredGaussianLaw C G).toReal))

/-- PDF p.8: log zero is -infinity; no conversion of log probability to a finite real. -/
def scaledLog {M : ℕ} (P : ℝ → Measure (EntropyCoordinates M)) (G : Set (EntropyCoordinates M)) (t : ℝ) : EReal :=
  ((1 / t : ℝ) : EReal) * (P t G).log

/-- PDF pp.9–10: extended right derivative, preserving the possible +infinite value at the boundary. -/
def rightDerivative (f : ℝ → ℝ) : EReal :=
  Filter.liminf (fun t : ℝ => (((f t - f 0) / t : ℝ) : EReal))
    (nhdsWithin 0 (Set.Ioi 0))

/-- PDF p.9, (14): entropy production from the actual dual reservoir evolutions. -/
def reservoirEntropyProduction {d M : ℕ} (D : DBData d M) (rho : Mat d) : EReal :=
  ∑ j, rightDerivative (fun t => finiteRelativeEntropyNats (hsAdjoint (qdsEvolution (D.generator j) t) rho) (D.rho j))

/-- PDF p.10: entropy flux out of reservoir j. -/
def entropyFlux {d M : ℕ} (D : DBData d M) (j : Fin M) : Mat d :=
  D.generator j (entropyObservable (D.rho j))

/-- PDF p.10: the constructed unique stationary density; the default is used only outside ER. -/
def steadyDensity {d : ℕ} (L : GeneratorMap d) : Mat d :=
  if h : ∃ rho : Mat d, IsDensityMatrix rho ∧ StationaryDensity L rho ∧
      ∀ sigma : Mat d, IsDensityMatrix sigma → StationaryDensity L sigma → sigma = rho then h.choose
  else chaotic d

/-- PDF p.10: centered entropy current. -/
def centeredCurrent {d M : ℕ} (D : DBData d M) (j : Fin M) : Mat d :=
  entropyFlux D j - expect (steadyDensity (reservoirGenerator D)) (entropyFlux D j) • 1

/-- PDF p.10: the rho_+-adjoint image, not a positive part. -/
def adjointCurrent {d M : ℕ} (D : DBData d M) (j : Fin M) : Mat d :=
  weightedAdjoint (steadyDensity (reservoirGenerator D)) (D.generator j) (entropyObservable (D.rho j))

/-- PDF p.11: energy flux out of the reservoir into the system. -/
def energyFlux {d M : ℕ} (D : DBData d M) (H : Mat d) (j : Fin M) : Mat d := D.generator j H

/-- PDF p.11: steady energy flux. -/
def energyMean {d M : ℕ} (D : DBData d M) (H : Mat d) : EntropyCoordinates M :=
  fun j => evaluate (steadyDensity (reservoirGenerator D)) (energyFlux D H j)

/-- PDF p.11: energetic FCS is the pushforward s ↦ -s/beta. -/
def energyLaw {d M : ℕ} (D : DBData d M) (beta : EntropyCoordinates M) (rho : Mat d) (t : ℝ) : Measure (EntropyCoordinates M) :=
  Measure.map (fun s : EntropyCoordinates M => fun j => -s j / beta j) (efcs D rho t)

/-- PDF p.11: corrected positive-Laplace energy CGF, forced by its displayed transform identity. -/
def energyCGF {d M : ℕ} (D : DBData d M) (beta : EntropyCoordinates M) (a : EntropyCoordinates M) : ℝ :=
  entropySpectralCGF D (fun j => a j / beta j)

/-- PDF p.26: local holomorphic continuation and the eventually defined logarithm branch.
The branch is normalized at the real base point and is not principal Complex.log. -/
def ComplexLimit {d M : ℕ} (D : DBData d M) (rho : Mat d) : Prop :=
  ∀ a0 : EntropyCoordinates M, ∃ r : ℝ, 0 < r ∧ ∃ E : CVec M → ℂ,
    AnalyticOnNhd ℂ E (Metric.ball (countingParameterEmbedding a0) r) ∧
    (∀ a : EntropyCoordinates M, countingParameterEmbedding a ∈ Metric.ball (countingParameterEmbedding a0) r → E (countingParameterEmbedding a) = (entropySpectralCGF D a : ℂ)) ∧
    (∀ z ∈ Metric.ball (countingParameterEmbedding a0) r,
      (entropyTilt D z).charpoly.IsRoot (E z) ∧ Polynomial.rootMultiplicity (E z) (entropyTilt D z).charpoly = 1) ∧
    ∃ T : ℝ, 0 < T ∧ ∃ B : ℝ → CVec M → ℂ,
      (∀ t ≥ T, AnalyticOnNhd ℂ (B t) (Metric.ball (countingParameterEmbedding a0) r) ∧
        (∀ z ∈ Metric.ball (countingParameterEmbedding a0) r, Complex.exp (B t z) = traceTransform D rho t z) ∧
        B t (countingParameterEmbedding a0) = (finiteCGF D rho t a0 : ℂ)) ∧
      ∀ z ∈ Metric.ball (countingParameterEmbedding a0) r,
        Tendsto (fun t : ℝ => B t z / (t : ℂ)) atTop (nhds (E z))

/-- Sanity: the counting law at t=0 is exactly the chosen delta_0. -/
example {d M : ℕ} (D : DBData d M) (rho : Mat d) : efcs D rho 0 = Measure.dirac 0 := by
  simp [efcs]

/-- Sanity: zero jumps produce zero entropy rate at every time by reservoirGenerator division. -/
example {d M : ℕ} (D : DBData d M) (t : ℝ) (q : Fin 0 → Jump D) (s : Fin 0 → ℝ) :
    pathRate D t ⟨0, (q, s)⟩ = 0 := by
  ext j
  simp [pathRate]

/-- PDF p.8: Euclidean length in the real reservoir-coordinate space. -/
def length {M : ℕ} (s : EntropyCoordinates M) : ℝ := Real.sqrt (∑ j, (s j) ^ 2)

/-- PDF p.10: the first correlation integrand in the second-entropySpectralCGF formula. -/
def currentCorrelation {d M : ℕ} (D : DBData d M) (j k : Fin M) (t : ℝ) : ℂ :=
  expect (steadyDensity (reservoirGenerator D))
    (qdsEvolution (reservoirGenerator D) t (centeredCurrent D j) * adjointCurrent D k +
      qdsEvolution (reservoirGenerator D) t (centeredCurrent D k) * adjointCurrent D j)

/-- PDF p.10: the additional reservoir-generator integrand. -/
def currentCorrection {d M : ℕ} (D : DBData d M) (j k : Fin M) (t : ℝ) : ℂ :=
  expect (steadyDensity (reservoirGenerator D))
    (D.generator k (qdsEvolution (reservoirGenerator D) t (centeredCurrent D j) * entropyObservable (D.rho k)) +
      D.generator j (qdsEvolution (reservoirGenerator D) t (centeredCurrent D k) * entropyObservable (D.rho j)))

/-- PDF pp.11–13: ordered equilibrium energy correlation. -/
def energyCorrelation {d M : ℕ} (D : DBData d M) (H : Mat d) (j k : Fin M) (t : ℝ) : ℝ :=
  evaluate (steadyDensity (reservoirGenerator D)) (qdsEvolution (reservoirGenerator D) t (energyFlux D H j) * energyFlux D H k)

/-- PDF p.12: the thermal componentwise response family, with no time-reversal field.
Data exist only on the stated open neighborhood. The extension by zero in regularity and
response definitions has no effect near zero. RE is a property of the actual generators. -/
structure ResponseFamily (d M : ℕ) where
  U : Set (EntropyCoordinates M)
  U_open : IsOpen U
  zero_mem : (0 : EntropyCoordinates M) ∈ U
  beta0 : ℝ
  beta0_pos : 0 < beta0
  H : Mat d
  H_hermitian : H.IsHermitian
  data : U → DBData d M
  thermal : ∀ z : U, Thermal (data z) H (fun j => beta0 - z.val j)
  componentwise : ∀ z w : U, ∀ j, z.val j = w.val j → (data z).generator j = (data w).generator j
  er : ∀ z : U, ER (data z)
  regular : ∃ V : Set (EntropyCoordinates M), IsOpen V ∧ (0 : EntropyCoordinates M) ∈ V ∧ V ⊆ U ∧
    ContDiffOn ℝ 1 (fun z : EntropyCoordinates M =>
      if hz : z ∈ U then LinearMap.toContinuousLinearMap (reservoirGenerator (data ⟨z, hz⟩)) else 0) V

/-- PDF p.12: the equilibrium data at the actual zero force. -/
def equilibrium {d M : ℕ} (F : ResponseFamily d M) : DBData d M := F.data ⟨0, F.zero_mem⟩

/-- PDF p.12: actual steady flux, extended outside the domain solely to take ambient derivatives. -/
def responseFlux {d M : ℕ} (F : ResponseFamily d M) (z : EntropyCoordinates M) : EntropyCoordinates M :=
  if hz : z ∈ F.U then energyMean (F.data ⟨z, hz⟩) F.H else 0

/-- PDF p.12: kinetic coefficients are derivatives of the actual steady flux. -/
def kinetic {d M : ℕ} (F : ResponseFamily d M) : Matrix (Fin M) (Fin M) ℝ :=
  fun j k => countingCoordinateDerivative (fun z => responseFlux F z j) k 0

/-- PDF pp.12–13: positive-Laplace energy CGF with beta=beta0-zeta. -/
def responseCGF {d M : ℕ} (F : ResponseFamily d M) (z a : EntropyCoordinates M) : ℝ :=
  if hz : z ∈ F.U then energyCGF (F.data ⟨z, hz⟩) (fun j => F.beta0 - z j) a else 0

/-- PDF p.13: the distinct negative-Laplace convention, whose first energy derivative has a minus. -/
def negativeResponseCGF {d M : ℕ} (F : ResponseFamily d M) (z a : EntropyCoordinates M) : ℝ :=
  responseCGF F z (-a)

/-- PDF p.13: corrected ordered Green–Kubo expression for the physical force beta0-beta. -/
def greenKubo {d M : ℕ} (F : ResponseFamily d M) (j k : Fin M) : ℝ :=
  -(∫ t in Set.Ioi (0 : ℝ), energyCorrelation (equilibrium F) F.H j k t) +
    (if j = k then (1 / 2 : ℝ) * evaluate (qdsGibbsDensity F.H F.beta0)
      (dissipation ((equilibrium F).generator j) F.H F.H) else 0)

/-- PDF p.16: distinct real energy eigenvalues. -/
def energies {d : ℕ} (H : Mat d) : Finset ℝ := H.charpoly.roots.toFinset.image Complex.re

/-- PDF p.16: all Bohr differences, with duplicates removed. -/
def energyDifferenceSet {d : ℕ} (H : Mat d) : Finset ℝ :=
  ((energies H).product (energies H)).image (fun p => p.1 - p.2)

/-- PDF p.16: the energy spectral projection is constructed from H. -/
def energyProjection {d : ℕ} (H : Mat d) (a : ℝ) : Mat d :=
  cfc (fun r : ℝ => if r = a then 1 else 0) H

/-- PDF p.16, (31): the lowering component, with mu-nu=w and P_nu Q P_mu. -/
def bohrComponent {d : ℕ} (H Q : Mat d) (w : ℝ) : Mat d :=
  ∑ mu ∈ energies H, ∑ nu ∈ energies H,
    if mu - nu = w then energyProjection H nu * Q * energyProjection H mu else 0

/-- PDF pp.15–16: finite Davies spectral data; these are not an assumed microscopic limit. -/
structure DaviesData (d M : ℕ) where
  dimension_pos : 0 < d
  H : Mat d
  H_hermitian : H.IsHermitian
  n : Fin M → ℕ
  Q : ∀ j, Fin (n j) → Mat d
  Q_hermitian : ∀ j k, (Q j k).IsHermitian
  beta : EntropyCoordinates M
  beta_pos : ∀ j, 0 < beta j
  h : ∀ j, ℝ → Matrix (Fin (n j)) (Fin (n j)) ℂ
  h_positive : ∀ j w, w ∈ energyDifferenceSet H → (h j w).PosSemidef
  h_KMS : ∀ j w, w ∈ energyDifferenceSet H → ∀ k l,
    h j (-w) k l = (Real.exp (-beta j * w) : ℂ) * h j w l k
  s : ∀ j, ℝ → Matrix (Fin (n j)) (Fin (n j)) ℂ
  s_hermitian : ∀ j w, w ∈ energyDifferenceSet H → (s j w).IsHermitian

/-- PDF p.16: the Hamiltonian correction constructed from s and lowering components. -/
def daviesT {d M : ℕ} (D : DaviesData d M) (j : Fin M) : Mat d :=
  ∑ k : Fin (D.n j), ∑ l : Fin (D.n j), ∑ w ∈ energyDifferenceSet D.H,
    D.s j w k l • ((bohrComponent D.H (D.Q j k) w)ᴴ * bohrComponent D.H (D.Q j l) w)

/-- PDF p.16: the CP part constructed from the positive h matrices. -/
def daviesPhi {d M : ℕ} (D : DaviesData d M) (j : Fin M) : GeneratorMap d :=
  ∑ k : Fin (D.n j), ∑ l : Fin (D.n j), ∑ w ∈ energyDifferenceSet D.H,
    D.h j w k l • sandwich ((bohrComponent D.H (D.Q j k) w)ᴴ) (bohrComponent D.H (D.Q j l) w)

/-- PDF p.16: the constructed finite Davies reservoir generator. -/
def daviesGenerator {d M : ℕ} (D : DaviesData d M) (j : Fin M) : GeneratorMap d :=
  lindblad (daviesT D j) (daviesPhi D j)

/-- PDF p.17: matrices commuting with the system Hamiltonian and a specified coupling set. -/
def commonCommutant {d : ℕ} (H : Mat d) (Q : Set (Mat d)) : Set (Mat d) :=
  {B | H * B = B * H ∧ ∀ A ∈ Q, A * B = B * A}

/-- PDF p.17: the full family of small-system couplings. -/
def allCouplings {d M : ℕ} (D : DaviesData d M) : Set (Mat d) :=
  {A | ∃ j, ∃ k, A = D.Q j k}

/-- PDF p.17: the full family V of constructed Bohr components. -/
def allBohrComponents {d M : ℕ} (D : DaviesData d M) : Set (Mat d) :=
  {A | ∃ j, ∃ k, ∃ w ∈ energyDifferenceSet D.H, A = bohrComponent D.H (D.Q j k) w}

/-- PDF p.17: entropy production from the constructed finite Davies dynamics. -/
def daviesEntropyProduction {d M : ℕ} (D : DaviesData d M) (rho : Mat d) : EReal :=
  ∑ j, rightDerivative (fun t => finiteRelativeEntropyNats
    (hsAdjoint (qdsEvolution (daviesGenerator D j) t) rho) (qdsGibbsDensity D.H (D.beta j)))

/-- Sanity: the zero coupling has every Bohr component zero, with either frequency sign. -/
example {d : ℕ} (H : Mat d) (w : ℝ) : bohrComponent H (0 : Mat d) w = 0 := by
  simp [bohrComponent]

end QAlgorithms.Papers.Independent.Intake100.P34


