-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26
-- name    : QAlgorithms_Papers_Independent_Gap48_P26
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T22:52:11.296402+00:00
-- url     : https://prove2.me/theorems/abc5e65a-a711-40ac-9e88-dd16fac90b09
-- title:
--   Definitions for Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture
-- statement:
--   The objects the formalized statements of *Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture* (arXiv:1312.6225) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `entropyBits`: PDF pp.2,6: extended spectral entropy in bits; no infinite-entropy real default.
--   - `weightedPhotonExpectation`: PDF pp.2,6: weighted photon expectation on arbitrary number-coordinate arrays, including blocks. Frozen Next46.P27.energy takes a bounded single-mode operator and has no coordinate weight; this is its distinct block-array interface.
--   - `totalPhotons`: PDF p.6, (16): total photons, rather than a separate budget in each mode.
--   - `minimumFiniteEnergy`: PDF pp.2,6: finite-energy pure-input entropy infimum. Attainment is a theorem.
--   - `vacuumOne`: PDF pp.2,6: one oscillator vacuum.
--   - `PhaseInsensitive`: PDF pp.1,2,6, (14): full phase-covariant/contravariant CPTP channel. This is the defining Weyl action on every density, not an entropy assumption.
--   - `coherentKernel`: PDF pp.2,6: normalized coherent projector, with the accepted exact coefficients.
--   - `thermalKernel`: PDF p.6, (18): Gibbs thermal state of finite nonnegative mean E.
--   - `constrainedHolevoBits`: PDF p.6, (15)-(16): optimized Holevo information in bits over all generalized ensembles with an average energy constraint. Neither the individual signals nor entanglement across the block are restricted. Values may be extended. Frozen Claimed50.P13.chiCapacity instead uses finite ensembles, a closed-form observable, and nats, so the generalized-law photon-budget interface here is distinct.
--   - `regularizedClassicalBits`: PDF pp.2,6: regularized per-use capacity, equivalently the supremum of positive block Holevo rates. Its equality to a single-use quantity is not built in. Frozen Information100.P62.classicalCapacity is finite-dimensional zero-error capacity without an energy argument, and cannot represent this quantity.
--   - `circularLaw`: PDF p.6: circular complex Gaussian law; E=0 is its Dirac vacuum version.
--   - `CoherentEncoding`: PDF p.6: push-forward encoding is the exact coherent projector at each label.
--   - `AffineGaussianUnitary`: PDF pp.4,7: affine Gaussian unitaries, including squeezing, phase rotation and displacement. Frozen Frontier30.P14.GaussianUnitary is centered and excludes displacements; its predicate cannot replace this affine Weyl condition.
--   - `normalFormChannel`: PDF p.7: the constructed normal form U o Phi o V, on full coefficient arrays.
--   - `GaussianPlaneLaw`: PDF pp.4,7: a real Gaussian displacement law; singular covariance is allowed. The Fourier convention uses Re(z), Im(z), so this also includes Dirac laws.
--   - `GaussianEncoding`: PDF pp.4,7: a Gaussian encoding consists of Gaussian displacements of one pure Gaussian seed. The optimization itself is over all ensembles.
--   - `AttainsCapacity`: PDF p.7: unrestricted feasible capacity-attaining ensemble.
--   - `IsPartialIsometry`: PDF p.3, (6), source correction: V V* V=V, allowing unequal kernel dimensions.
--   - `PreservesSupport`: Identity of the initial projection on the source support. This prevents a partial isometry from deleting positive spectral mass. PDF p.3, corrected (6).
--   - `squeezingColumn`: PDF pp.4,7, (13),(32): positive squeezing column U_kappa |p,0>. The accepted exact amplifier coefficient is also its Stinespring coefficient. No vector normalization or channel realization is assumed as a premise.
--   - `squeezedThermal`: PDF pp.4,7: the full two-mode output U_kappa (thermal_N tensor vacuum) U*. Each column is a full infinite Fock vector; no photon truncation is imposed.
--   - `squeezedCovariance`: PDF p.7, (32): covariance in vacuum-I, interleaved mode/quadrature order.
--   - `displacementCovariance`: PDF p.7, (35): classical correlated-displacement covariance, with its 2N factor.
--   - `correlatedDisplacement`: PDF p.7: product local displacements driven by one shared classical label. The positive correlation gives the c sigma_z block of (32).
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, https://arxiv.org/abs/1312.6225v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P45

/-!
arXiv:1312.6225v1. Full Fock spaces, nuclear trace-class densities, and bits.
Pinned accepted paper modules provide definitions under the independent-paper
workflow override. NumberString, vacuum, bounded operator coefficients, and the
unrestricted continuous-ensemble EoF are imported directly. Thermal entropy in
bits is imported directly from frozen Dependency50.P30. Distinct weighted block energy,
generalized-ensemble bit capacities, and affine Gaussian unitaries keep explicit
names because the similarly named frozen objects have different domains.
Local definitions have complete bodies. Equations (6)-(9)
use connecting partial isometries, as required on infinite Fock space and independently
specified in arXiv:1312.2251v1, Section 6. See SOURCE_CORRECTIONS.md.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P26

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Next46.P32 (NumberString vacuum)
open QAlgorithms.Papers.Independent.Next46.P45 (entanglementOfFormation)
open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State rankOne IsDensity IsBarycenter IsTraceClassChannel)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation traceClassTensorPower weylCharacteristic boundedUnitaryConjugation
   conjugateKernel partialRight GaussianDensity)

namespace B
export QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet operatorOfMatrix coherentCoefficient coherentMeasure husimiQ)
end B

namespace Ens
export QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasAverage ensembleHolevo extendedEntropyNats)
end Ens

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2,6: extended spectral entropy in bits; no infinite-entropy real default. -/
def entropyBits {I : Type} (X : Matrix I I ℂ) : ℝ≥0∞ :=
  Ens.extendedEntropyNats X / ENNReal.ofReal (Real.log 2)

/-- PDF pp.2,6: weighted photon expectation on arbitrary number-coordinate
arrays, including blocks. Frozen Next46.P27.energy takes a bounded single-mode
operator and has no coordinate weight; this is its distinct block-array interface. -/
def weightedPhotonExpectation {I : Type} (weight : I → ℕ) (X : Matrix I I ℂ) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal ((weight i : ℝ) * (X i i).re)

/-- PDF p.6, (16): total photons, rather than a separate budget in each mode. -/
def totalPhotons {m : ℕ} (a : NumberString m) : ℕ := ∑ j, a j

/-- PDF pp.2,6: finite-energy pure-input entropy infimum. Attainment is a theorem. -/
def minimumFiniteEnergy {I : Type} (weight : I → ℕ) (Phi : Operation I I) : ℝ≥0∞ :=
  ⨅ u : {u : Hilbert I // ‖u‖ = 1 ∧ weightedPhotonExpectation weight (rankOne u) < ⊤},
    entropyBits (Phi (rankOne u.val))

/-- PDF pp.2,6: one oscillator vacuum. -/
def vacuumOne : Matrix ℕ ℕ ℂ := fun a b => if a = 0 ∧ b = 0 then 1 else 0

/-- PDF pp.1,2,6, (14): full phase-covariant/contravariant CPTP channel.
This is the defining Weyl action on every density, not an entropy assumption. -/
def PhaseInsensitive (Phi : Operation ℕ ℕ) (tau y : ℝ) : Prop :=
  IsTraceClassChannel Phi ∧ |tau - 1| ≤ y ∧
    ∀ (rho : State ℕ) (z : ℂ),
      weylCharacteristic (Phi rho.coefficients) z =
        weylCharacteristic rho.coefficients
          (if 0 ≤ tau then (Real.sqrt tau : ℂ) * z
           else -(Real.sqrt |tau| : ℂ) * star z) *
        Complex.exp ((-y * Complex.normSq z / 2 : ℝ) : ℂ)

/-- PDF pp.2,6: normalized coherent projector, with the accepted exact coefficients. -/
def coherentKernel (alpha : ℂ) : Matrix ℕ ℕ ℂ :=
  fun a b => B.coherentCoefficient alpha a * star (B.coherentCoefficient alpha b)

/-- PDF p.6, (18): Gibbs thermal state of finite nonnegative mean E. -/
def thermalKernel (E : ℝ) : Matrix ℕ ℕ ℂ :=
  fun a b => if a = b then ((E / (E + 1)) ^ a / (E + 1) : ℝ) else 0

/-- PDF p.6, (15)-(16): optimized Holevo information in bits over all generalized
ensembles with an average energy constraint. Neither the individual signals nor
entanglement across the block are restricted. Values may be extended. Frozen
Claimed50.P13.chiCapacity instead uses finite ensembles, a closed-form observable,
and nats, so the generalized-law photon-budget interface here is distinct. -/
def constrainedHolevoBits {I : Type} (weight : I → ℕ) (Phi : Operation I I) (budget : ℝ) : ℝ≥0∞ :=
  ⨆ mu : {mu : Ens.GeneralizedEnsemble I // ∃ rho : State I,
      Ens.HasAverage mu rho ∧ weightedPhotonExpectation weight rho.coefficients ≤ ENNReal.ofReal budget},
    Ens.ensembleHolevo Phi mu.val / ENNReal.ofReal (Real.log 2)

/-- PDF pp.2,6: regularized per-use capacity, equivalently the supremum of
positive block Holevo rates. Its equality to a single-use quantity is not built in.
Frozen Information100.P62.classicalCapacity is finite-dimensional zero-error
capacity without an energy argument, and cannot represent this quantity. -/
def regularizedClassicalBits (Phi : Operation ℕ ℕ) (E : ℝ) : ℝ≥0∞ :=
  ⨆ m : {m : ℕ // 0 < m},
    constrainedHolevoBits totalPhotons (traceClassTensorPower Phi m.val) (m.val * E) /
      (m.val : ℝ≥0∞)

/-- PDF p.6: circular complex Gaussian law; E=0 is its Dirac vacuum version. -/
def circularLaw (E : ℝ) : Measure ℂ :=
  if E = 0 then Measure.dirac 0 else
    volume.withDensity (fun z => ENNReal.ofReal
      (Real.exp (-Complex.normSq z / E) / (Real.pi * E)))

/-- PDF p.6: push-forward encoding is the exact coherent projector at each label. -/
def CoherentEncoding (E : ℝ) (mu : Ens.GeneralizedEnsemble ℕ) : Prop :=
  ∃ f : ℂ → State ℕ, Measurable f ∧
    (∀ z, (f z).coefficients = coherentKernel z) ∧
    (mu : Measure (State ℕ)) = (circularLaw E).map f

/-- PDF pp.4,7: affine Gaussian unitaries, including squeezing, phase rotation
and displacement. Frozen Frontier30.P14.GaussianUnitary is centered and excludes
displacements; its predicate cannot replace this affine Weyl condition. -/
def AffineGaussianUnitary (U : Hilbert ℕ ≃ₗᵢ[ℂ] Hilbert ℕ) : Prop :=
  ∃ alpha beta delta : ℂ, Complex.normSq alpha - Complex.normSq beta = 1 ∧
    ∀ z : ℂ,
      boundedUnitaryConjugation U.symm
          (QAlgorithms.Papers.Independent.Dependency50.P39.displacementMatrix z) =
        Complex.exp (z * star delta - star z * delta) •
          QAlgorithms.Papers.Independent.Dependency50.P39.displacementMatrix
            (z * star alpha - star z * beta)

/-- PDF p.7: the constructed normal form U o Phi o V, on full coefficient arrays. -/
def normalFormChannel (Phi : Operation ℕ ℕ)
    (U V : Hilbert ℕ ≃ₗᵢ[ℂ] Hilbert ℕ) : Operation ℕ ℕ :=
  fun X => boundedUnitaryConjugation U (Phi (boundedUnitaryConjugation V X))

/-- PDF pp.4,7: a real Gaussian displacement law; singular covariance is allowed.
The Fourier convention uses Re(z), Im(z), so this also includes Dirac laws. -/
def GaussianPlaneLaw (nu : Measure ℂ) : Prop :=
  IsProbabilityMeasure nu ∧ ∃ (mean : Fin 2 → ℝ) (cov : Matrix (Fin 2) (Fin 2) ℝ),
    cov.PosSemidef ∧ ∀ t : Fin 2 → ℝ,
      (∫ z : ℂ, Complex.exp (Complex.I * ((t 0 * z.re + t 1 * z.im : ℝ) : ℂ)) ∂nu) =
        Complex.exp (((-(∑ i, ∑ j, t i * cov i j * t j) / 2 : ℝ) : ℂ) +
          Complex.I * ((∑ i, t i * mean i : ℝ) : ℂ))

/-- PDF pp.4,7: a Gaussian encoding consists of Gaussian displacements of one
pure Gaussian seed. The optimization itself is over all ensembles. -/
def GaussianEncoding (mu : Ens.GeneralizedEnsemble ℕ) : Prop :=
  ∃ (seed : State ℕ) (u : Hilbert ℕ) (nu : Measure ℂ) (f : ℂ → State ℕ),
    ‖u‖ = 1 ∧ seed.coefficients = rankOne u ∧ GaussianDensity seed.coefficients ∧
    GaussianPlaneLaw nu ∧ Measurable f ∧
    (∀ z, (f z).coefficients = conjugateKernel
      (QAlgorithms.Papers.Independent.Dependency50.P39.displacementMatrix z) seed.coefficients) ∧
    (mu : Measure (State ℕ)) = nu.map f

/-- PDF p.7: unrestricted feasible capacity-attaining ensemble. -/
def AttainsCapacity (Phi : Operation ℕ ℕ) (E : ℝ)
    (mu : Ens.GeneralizedEnsemble ℕ) : Prop :=
  (∃ rho : State ℕ, Ens.HasAverage mu rho ∧
    weightedPhotonExpectation id rho.coefficients ≤ ENNReal.ofReal E) ∧
  Ens.ensembleHolevo Phi mu / ENNReal.ofReal (Real.log 2) = constrainedHolevoBits id Phi E

example : thermalEntropyBits 0 = 0 := by simp [thermalEntropyBits]

example : thermalKernel 0 0 0 = 1 := by simp [thermalKernel]

example (X : Matrix (NumberString 0) (NumberString 0) ℂ) :
    traceClassTensorPower (fun Y : Matrix ℕ ℕ ℂ => Y) 0 X = X := rfl

example : circularLaw 0 = Measure.dirac 0 := by simp [circularLaw]

/-- PDF p.3, (6), source correction: V V* V=V, allowing unequal kernel dimensions. -/
def IsPartialIsometry (V : B.FockOperator) : Prop :=
  (V.comp (ContinuousLinearMap.adjoint V)).comp V = V

/-- Identity of the initial projection on the source support. This prevents a
partial isometry from deleting positive spectral mass. PDF p.3, corrected (6). -/
def PreservesSupport (V : B.FockOperator) (X : Matrix ℕ ℕ ℂ) : Prop :=
  ((ContinuousLinearMap.adjoint V).comp V).comp (B.operatorOfMatrix X) = B.operatorOfMatrix X

example : IsPartialIsometry (1 : B.FockOperator) := by
  simp [IsPartialIsometry, ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id]

/-- PDF pp.4,7, (13),(32): positive squeezing column U_kappa |p,0>.
The accepted exact amplifier coefficient is also its Stinespring coefficient.
No vector normalization or channel realization is assumed as a premise. -/
def squeezingColumn (kappa : ℝ) (p : ℕ) (a : NumberString 2) : ℂ :=
  QAlgorithms.Papers.Independent.Dependency50.P39.amplifierMatrix
    (Real.sqrt kappa) (a 1) (a 0) p

/-- PDF pp.4,7: the full two-mode output U_kappa (thermal_N tensor vacuum) U*.
Each column is a full infinite Fock vector; no photon truncation is imposed. -/
def squeezedThermal (kappa N : ℝ) : Matrix (NumberString 2) (NumberString 2) ℂ :=
  fun a b => ∑' p : ℕ, ((N / (N + 1)) ^ p / (N + 1) : ℝ) *
    squeezingColumn kappa p a * star (squeezingColumn kappa p b)

/-- PDF p.7, (32): covariance in vacuum-I, interleaved mode/quadrature order. -/
def squeezedCovariance (kappa N : ℝ) :
    QAlgorithms.Papers.Independent.Claimed50.P19.Cov 2 :=
  let c := 2 * (N + 1) * Real.sqrt (kappa * (kappa - 1))
  QAlgorithms.Papers.Independent.Claimed50.P19.standardFormCovariance
    (2 * (N + 1) * kappa - 1) (2 * (N + 1) * kappa - (2 * N + 1)) c (-c)

/-- PDF p.7, (35): classical correlated-displacement covariance, with its 2N factor. -/
def displacementCovariance (kappa N : ℝ) :
    QAlgorithms.Papers.Independent.Claimed50.P19.Cov 2 :=
  (2 * N) • QAlgorithms.Papers.Independent.Claimed50.P19.standardFormCovariance
    kappa (kappa - 1) (Real.sqrt (kappa * (kappa - 1)))
    (-Real.sqrt (kappa * (kappa - 1)))

/-- PDF p.7: product local displacements driven by one shared classical label.
The positive correlation gives the c sigma_z block of (32). -/
def correlatedDisplacement (kappa : ℝ) (z : ℂ) :
    Matrix (NumberString 2) (NumberString 2) ℂ :=
  QAlgorithms.Papers.Independent.Claimed50.P19.productWeyl
    ![(Real.sqrt kappa : ℂ) * z, (Real.sqrt (kappa - 1) : ℂ) * star z]

example : displacementCovariance 1 0 = 0 := by simp [displacementCovariance]

example : squeezingColumn 1 0 (fun _ => 0) = 1 := by
  simp [squeezingColumn, QAlgorithms.Papers.Independent.Dependency50.P39.amplifierMatrix]

end QAlgorithms.Papers.Independent.Gap48.P26


