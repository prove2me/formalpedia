-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64
-- name    : QAlgorithms_Papers_Independent_Intake100_P64
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:14:28.498244+00:00
-- url     : https://prove2.me/theorems/d2df1b58-a089-456c-a93e-fcbad3b0bd09
-- title:
--   Definitions for Quantum linear Boltzmann equation
-- statement:
--   The objects the formalized statements of *Quantum linear Boltzmann equation* (arXiv:0904.3911) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Momentum`: PDF p.6: physical three-dimensional Euclidean momentum space.
--   - `MomentumKernel`: PDF p.7: chosen scalar kernel representative, not an L2 equivalence class.
--   - `momentumDot`: PDF p.6: physical Euclidean scalar product.
--   - `GasTracerParameters`: PDF p.6: positive gas/tracer masses, hbar, and number density.
--   - `reducedMass`: PDF p.6: reduced mass.
--   - `parallel`: PDF p.6: parallel projection, zero at null transfer.
--   - `perpendicular`: PDF p.6: perpendicular projection.
--   - `relativeMomentum`: PDF p.6, (2.4): relative momentum.
--   - `MomentumLaw`: PDF p.6: nonnegative measurable Lebesgue probability density.
--   - `CollisionData`: PDF pp.6–7: formal scalar collision data. Only elastic on-shell values are sampled; an inverse-scattering realization is not asserted. Restrictions such as reciprocity and the optical theorem are separate hypotheses.
--   - `crossSection`: PDF p.7: differential cross-section.
--   - `TransverseFrames`: PDF p.6: orthonormal coordinates for the actual transverse plane. At Q=0 only the arbitrary chart is unused, since the coefficient is zero.
--   - `prefactor`: PDF p.6: prefactor with explicit Lebesgue-null Q=0 convention.
--   - `gasArgument`: PDF p.6, (2.3): the gas-density argument.
--   - `transverseRelative`: PDF p.6: the transverse mean relative momentum.
--   - `collisionCoefficient`: PDF p.6, (2.3): complex coefficient with both square roots retained.
--   - `rateIntegrand`: PDF p.7, (2.10): rate integrand for a jump from P to P+Q.
--   - `transferRate`: PDF p.7: M_in(P;Q)=transferRate(P-Q,Q).
--   - `quantumGain`: PDF p.7, (2.8): complex gain, with the shift in both arguments.
--   - `outgoingIntensity`: PDF p.7: outgoing intensity before Q integration.
--   - `collisionLossRate`: PDF pp.6–7: loss defined from the original Lindblad coefficients.
--   - `lindbladIntegrand`: PDF p.6, (2.2): original double-integral kernel integrand.
--   - `collisionKernel`: PDF pp.6–7: formal weak/scalar collision expression, not a closed generator.
--   - `KernelDomain`: PDF p.7: finite scalar domain for the integral rearrangement.
--   - `classicalGenerator`: PDF pp.7,10–11: classical gain-minus-loss collision expression.
--   - `maxwell`: PDF p.6, (2.6): normalized three-dimensional Maxwell density.
--   - `maxwellPlane`: PDF p.44, (8.2): transverse Maxwell density.
--   - `energyTransfer`: PDF p.16, (4.11): energy gained by the tracer.
--   - `maxwellStructure`: PDF p.45, (8.8): Maxwell structure factor. Its Q=0 value is only a null-set convention for the Lebesgue collision integral.
--   - `bornAmplitude`: PDF p.8, (2.15): Born Fourier amplitude, with negative Fourier sign.
--   - `bornMatrixAmplitude`: PDF p.8: independent two-momentum spelling of the Born integral.
--   - `bornMultiplier`: PDF p.8, (2.17): nonnegative Born multiplier, with nested square roots.
--   - `bornKernel`: PDF p.8, (2.18): the single-Q Born collision expression.
--   - `forwardAverage`: PDF p.30, (6.1): actual forward-amplitude integral.
--   - `energyShift`: PDF p.6, (2.5): gas-induced energy shift.
--   - `opticalPotential`: PDF p.31, (6.8): complex optical potential.
--   - `boostedCoefficient`: PDF p.15: coefficient evaluated with mu_V(p)=mu(p-mV).
--   - `boostedEnergyShift`: PDF p.15: energy shift evaluated with the translated gas density.
--   - `boostedCollisionKernel`: PDF p.15, (4.4): collision expression with the translated gas coefficient.
--   - `averagedCrossSection`: PDF p.45, (8.6): the averaged cross-section retains transverse P dependence.
--   - `structureGenerator`: PDF pp.45,48, (8.7),(8.23): collision expression for a given medium S. No Maxwell shape is imposed on S in the generic-medium stationarity theorem.
--   - `structureCoefficient`: PDF p.46, (8.10): structure-factor coefficient, retaining complex amplitudes.
--   - `structureQuantumKernel`: PDF p.46: explicit double integral in structure-factor form.
--   - `thermalSpeed`: PDF p.19, (4.28): most probable thermal gas speed.
--   - `brownianFriction`: PDF pp.19–20, (4.33): constant-cross-section Brownian friction.
--   - `BrownianMomentSolution`: PDF pp.19–20: exact moment equations defining the resulting approximate Brownian model, not the finite-mass QLBE. Right derivatives at zero suffice.
--   - `momentumDiffusion`: PDF p.28, (5.16): momentum diffusion coefficient.
--   - `positionDiffusion`: PDF p.28, (5.17): quantum position diffusion coefficient.
--   - `quantumExponent`: PDF pp.43–44: direct quantum momentum-coherence exponent.
--   - `dispersionExponent`: PDF pp.43–44: dispersion-induced exponent, kept separate from the incorrectly printed full convolution formula.
--   - `ConservativeQDS`: PDF p.17: a given conservative QDS on the full trace class of an arbitrary complete complex Hilbert space. The source's finite-volume setting is represented through its given trace-class invariant state, not a finite matrix. The state maps are tied to the linear CP maps, not independent dynamics.
--   - `boltzmannRelativeEntropy`: PDF p.17, (4.17): k_B times accepted extended nats Umegaki entropy.
--   - `sphereDirection`: PDF p.31, (6.4): unit direction used for ordinary solid-angle integration.
--   - `totalCrossSection`: PDF p.31: total cross-section using dOmega=sin(theta)dtheta dphi. The p=0 value is a null-relative-momentum convention in the flux integral.
--   - `fluxLoss`: PDF pp.30–31, (6.3)–(6.4): loss as relative flux times total cross-section.
--   - `OpticalDomain`: PDF p.31: the cited optical theorem, together with the actual common finite-integral domain. Optical equality is imposed on scattering data, not on the desired loss-rate conclusion.
--   - `fullKernel`: PDF p.6, (2.1): full formal momentum-kernel generator.
--   - `noJumpFactor`: PDF p.31: no-jump wave multiplier for the optical potential, with kinetic energy.
--   - `noJumpWave`: PDF p.31: actual wave-function representative of the conditioned pure state.
--   - `noJumpKernel`: PDF p.31: conditioned no-jump kernel, with conjugation on the right.
--   - `refractiveIndex`: PDF p.32, (6.13): physical square-root branch, continuous from n=1 at zero gas density. The gas density n varies while the beam and gas law are fixed.
--   - `refractiveSlope`: PDF p.32, (6.14)–(6.16): the first-order coefficient per unit gas density.
--   - `radialForwardIntegrand`: PDF p.33, (6.17): radial thermal convolution for nonzero beam velocity.
--   - `planeFriction`: PDF pp.27–28, (5.11): exact plane-integral friction functional.
--   - `angularFriction`: PDF pp.25,28,57, (5.2),(5.13),(A.32): common angular functional.
--   - `kummer`: PDF pp.19,22: standard entire 1F1(a;b;z), used only for b>0. The value at zero is written separately so no sin(x)/x or erf(x)/x default is used at zero velocity. For b>0 the series is absolutely convergent.
--   - `speedPower`: PDF p.22: relative-speed power, assigned zero on the single null point where a negative power would be singular. This does not change its integral.
--   - `powerCollisionRate`: PDF p.22: thermal collision rate for the differential law c|v-V|^a.
--   - `effectiveCrossSection`: PDF p.22, (4.45): effective cross-section; only P!=0 is used.
--   - `errorFunction`: PDF p.22, (4.49): the standard real error function, via its Gaussian integral.
--   - `londonCoefficient`: PDF p.37, (7.20): semiclassical London total-cross-section coefficient; this is a model input, not a claim about every singular -C6/r^6 potential.
--   - `londonRate`: PDF pp.37–38: London collision frequency, an actual thermal convolution.
--   - `londonBaseRate`: PDF p.38, (7.23): zero-speed collision frequency.
--   - `frozenCharacteristic`: PDF pp.35–37: normalized characteristic function of the frozen-label transfer law (7.9). The 1/Gamma normalization missing below (7.19) is explicit.
--   - `frozenPositionGenerator`: PDF pp.35,37: position kernel of the specified frozen-label model.
-- source:
--   Quantum linear Boltzmann equation, arXiv:0904.3911v3, https://arxiv.org/abs/0904.3911v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

/-!
Vacchini–Hornberger, arXiv:0904.3911v3. Formal continuum identities use explicit
scalar integrability. Kernels are chosen representatives, never evaluations of
L2 equivalence classes. The trace-class paper imports are pinned accepted foundations
for the conditional H-theorem; the remaining imports supply the accepted plane
and rising factorial. No general Boltzmann QDS is constructed here.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

/-- PDF p.6: physical three-dimensional Euclidean momentum space. -/
abbrev Momentum := EuclideanSpace ℝ (Fin 3)

-- PDF p.6: specialize the accepted Euclidean plane to real scalars.
local notation "TransversePlane" => QAlgorithms.Papers.Independent.Renew46.P04.Plane ℝ

-- The accepted rising factorial has exactly the same finite-product body.
open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

/-- PDF p.7: chosen scalar kernel representative, not an L2 equivalence class. -/
abbrev MomentumKernel := Momentum → Momentum → ℂ

/-- PDF p.6: physical Euclidean scalar product. -/
def momentumDot (x y : Momentum) : ℝ := ∑ i, x i * y i

/-- PDF p.6: positive gas/tracer masses, hbar, and number density. -/
structure GasTracerParameters where
  m : ℝ
  M : ℝ
  hbar : ℝ
  density : ℝ
  m_pos : 0 < m
  M_pos : 0 < M
  hbar_pos : 0 < hbar
  density_pos : 0 < density

/-- PDF p.6: reduced mass. -/
def reducedMass (a : GasTracerParameters) : ℝ := a.m * a.M / (a.m + a.M)

/-- PDF p.6: parallel projection, zero at null transfer. -/
def parallel (P Q : Momentum) : Momentum := (momentumDot P Q / ‖Q‖ ^ 2) • Q

/-- PDF p.6: perpendicular projection. -/
def perpendicular (P Q : Momentum) : Momentum := P - parallel P Q

/-- PDF p.6, (2.4): relative momentum. -/
def relativeMomentum (a : GasTracerParameters) (p P : Momentum) : Momentum :=
  (reducedMass a / a.m) • p - (reducedMass a / a.M) • P

/-- PDF p.6: nonnegative measurable Lebesgue probability density. -/
structure MomentumLaw where
  value : Momentum → ℝ
  measurable : Measurable value
  nonnegative : ∀ p, 0 ≤ value p
  integrable : Integrable value
  normalized : ∫ p, value p = 1

/-- PDF pp.6–7: formal scalar collision data. Only elastic on-shell values
are sampled; an inverse-scattering realization is not asserted. Restrictions
such as reciprocity and the optical theorem are separate hypotheses. -/
structure CollisionData where
  parameters : GasTracerParameters
  gas : MomentumLaw
  amplitude : Momentum → Momentum → ℂ
  amplitude_measurable : Measurable (Function.uncurry amplitude)

/-- PDF p.7: differential cross-section. -/
def crossSection (d : CollisionData) (pf pi : Momentum) : ℝ :=
  Complex.normSq (d.amplitude pf pi)

/-- PDF p.6: orthonormal coordinates for the actual transverse plane.
At Q=0 only the arbitrary chart is unused, since the coefficient is zero. -/
structure TransverseFrames where
  map : Momentum → TransversePlane →ₗᵢ[ℝ] Momentum
  orthogonal : ∀ Q k, momentumDot (map Q k) Q = 0
  onto : ∀ Q, Q ≠ 0 → ∀ p, momentumDot p Q = 0 → ∃ k, map Q k = p

/-- PDF p.6: prefactor with explicit Lebesgue-null Q=0 convention. -/
def prefactor (a : GasTracerParameters) (Q : Momentum) : ℝ :=
  if Q = 0 then 0 else a.density * a.m / (reducedMass a ^ 2 * ‖Q‖)

/-- PDF p.6, (2.3): the gas-density argument. -/
def gasArgument (a : GasTracerParameters) (p P Q : Momentum) : Momentum :=
  perpendicular p Q + (a.m / (2 * reducedMass a)) • Q +
    (a.m / a.M) • parallel P Q

/-- PDF p.6: the transverse mean relative momentum. -/
def transverseRelative (a : GasTracerParameters) (p P Q : Momentum) : Momentum :=
  relativeMomentum a (perpendicular p Q) (perpendicular P Q)

/-- PDF p.6, (2.3): complex coefficient with both square roots retained. -/
def collisionCoefficient (d : CollisionData) (p P Q : Momentum) : ℂ :=
  if Q = 0 then 0 else
    (Real.sqrt (prefactor d.parameters Q) : ℂ) *
      d.amplitude
        (transverseRelative d.parameters p P Q - (1 / 2 : ℝ) • Q)
        (transverseRelative d.parameters p P Q + (1 / 2 : ℝ) • Q) *
      (Real.sqrt (d.gas.value (gasArgument d.parameters p P Q)) : ℂ)

/-- PDF p.7, (2.10): rate integrand for a jump from P to P+Q. -/
def rateIntegrand (d : CollisionData) (F : TransverseFrames)
    (P Q : Momentum) (k : TransversePlane) : ℝ :=
  prefactor d.parameters Q * d.gas.value (gasArgument d.parameters (F.map Q k) P Q) *
    crossSection d
      (transverseRelative d.parameters (F.map Q k) P Q - (1 / 2 : ℝ) • Q)
      (transverseRelative d.parameters (F.map Q k) P Q + (1 / 2 : ℝ) • Q)

/-- PDF p.7: M_in(P;Q)=transferRate(P-Q,Q). -/
def transferRate (d : CollisionData) (F : TransverseFrames) (P Q : Momentum) : ℝ :=
  ∫ k, rateIntegrand d F P Q k

/-- PDF p.7, (2.8): complex gain, with the shift in both arguments. -/
def quantumGain (d : CollisionData) (F : TransverseFrames)
    (P Pprime Q : Momentum) : ℂ :=
  ∫ k, collisionCoefficient d (F.map Q k) (P - Q) Q *
    star (collisionCoefficient d (F.map Q k) (Pprime - Q) Q)

/-- PDF p.7: outgoing intensity before Q integration. -/
def outgoingIntensity (d : CollisionData) (F : TransverseFrames)
    (P Q : Momentum) : ℝ :=
  ∫ k, Complex.normSq (collisionCoefficient d (F.map Q k) P Q)

/-- PDF pp.6–7: loss defined from the original Lindblad coefficients. -/
def collisionLossRate (d : CollisionData) (F : TransverseFrames) (P : Momentum) : ℝ :=
  ∫ Q, outgoingIntensity d F P Q

/-- PDF p.6, (2.2): original double-integral kernel integrand. -/
def lindbladIntegrand (d : CollisionData) (F : TransverseFrames)
    (r : MomentumKernel) (P Pprime Q : Momentum) (k : TransversePlane) : ℂ :=
  collisionCoefficient d (F.map Q k) (P - Q) Q * r (P - Q) (Pprime - Q) *
      star (collisionCoefficient d (F.map Q k) (Pprime - Q) Q) -
    (((Complex.normSq (collisionCoefficient d (F.map Q k) P Q) +
      Complex.normSq (collisionCoefficient d (F.map Q k) Pprime Q)) / 2 : ℝ) : ℂ) * r P Pprime

/-- PDF pp.6–7: formal weak/scalar collision expression, not a closed generator. -/
def collisionKernel (d : CollisionData) (F : TransverseFrames)
    (r : MomentumKernel) (P Pprime : Momentum) : ℂ :=
  ∫ Q, ∫ k, lindbladIntegrand d F r P Pprime Q k

/-- PDF p.7: finite scalar domain for the integral rearrangement. -/
def KernelDomain (d : CollisionData) (F : TransverseFrames)
    (r : MomentumKernel) (P Pprime : Momentum) : Prop :=
  (∀ᵐ Q : Momentum, Integrable (fun k : TransversePlane =>
    collisionCoefficient d (F.map Q k) (P - Q) Q *
      star (collisionCoefficient d (F.map Q k) (Pprime - Q) Q))) ∧
  (∀ᵐ Q : Momentum, Integrable (fun k : TransversePlane =>
    Complex.normSq (collisionCoefficient d (F.map Q k) P Q))) ∧
  (∀ᵐ Q : Momentum, Integrable (fun k : TransversePlane =>
    Complex.normSq (collisionCoefficient d (F.map Q k) Pprime Q))) ∧
  Integrable (fun Q => quantumGain d F P Pprime Q * r (P - Q) (Pprime - Q)) ∧
  Integrable (outgoingIntensity d F P) ∧ Integrable (outgoingIntensity d F Pprime)

/-- PDF pp.7,10–11: classical gain-minus-loss collision expression. -/
def classicalGenerator (d : CollisionData) (F : TransverseFrames)
    (nu : Momentum → ℝ) (P : Momentum) : ℝ :=
  (∫ Q, transferRate d F (P - Q) Q * nu (P - Q)) - collisionLossRate d F P * nu P

/-- PDF p.6, (2.6): normalized three-dimensional Maxwell density. -/
def maxwell (mass beta : ℝ) (p : Momentum) : ℝ :=
  Real.rpow (beta / (2 * Real.pi * mass)) (3 / 2 : ℝ) *
    Real.exp (-beta * ‖p‖ ^ 2 / (2 * mass))

/-- PDF p.44, (8.2): transverse Maxwell density. -/
def maxwellPlane (mass beta : ℝ) (p : Momentum) : ℝ :=
  beta / (2 * Real.pi * mass) * Real.exp (-beta * ‖p‖ ^ 2 / (2 * mass))

/-- PDF p.16, (4.11): energy gained by the tracer. -/
def energyTransfer (a : GasTracerParameters) (Q P : Momentum) : ℝ :=
  ‖Q‖ ^ 2 / (2 * a.M) + momentumDot Q P / a.M

/-- PDF p.45, (8.8): Maxwell structure factor. Its Q=0 value is only a
null-set convention for the Lebesgue collision integral. -/
def maxwellStructure (a : GasTracerParameters) (beta : ℝ) (Q : Momentum) (E : ℝ) : ℝ :=
  if Q = 0 then 0 else Real.sqrt (beta * a.m / (2 * Real.pi)) / ‖Q‖ *
    Real.exp (-beta * (‖Q‖ ^ 2 + 2 * a.m * E) ^ 2 / (8 * a.m * ‖Q‖ ^ 2))

/-- PDF p.8, (2.15): Born Fourier amplitude, with negative Fourier sign. -/
def bornAmplitude (a : GasTracerParameters) (V : Momentum → ℝ) (Q : Momentum) : ℂ :=
  (-(reducedMass a) / (2 * Real.pi * a.hbar ^ 2) : ℝ) *
    ∫ x, (V x : ℂ) * Complex.exp (-Complex.I * (momentumDot Q x / a.hbar : ℝ))

/-- PDF p.8: independent two-momentum spelling of the Born integral. -/
def bornMatrixAmplitude (a : GasTracerParameters) (V : Momentum → ℝ) (pf pi : Momentum) : ℂ :=
  (-(reducedMass a) / (2 * Real.pi * a.hbar ^ 2) : ℝ) *
    ∫ x, (V x : ℂ) *
      Complex.exp (-Complex.I * ((momentumDot pf x - momentumDot pi x) / a.hbar : ℝ))

/-- PDF p.8, (2.17): nonnegative Born multiplier, with nested square roots. -/
def bornMultiplier (a : GasTracerParameters) (beta : ℝ) (V : Momentum → ℝ)
    (P Q : Momentum) : ℝ :=
  if Q = 0 then 0 else
    Real.sqrt (Real.sqrt (beta * a.m / (2 * Real.pi)) * a.density *
      Complex.normSq (bornAmplitude a V Q) / (reducedMass a ^ 2 * ‖Q‖)) *
      Real.exp (-beta * ((1 + a.m / a.M) * ‖Q‖ ^ 2 +
        (2 * a.m / a.M) * momentumDot P Q) ^ 2 / (16 * a.m * ‖Q‖ ^ 2))

/-- PDF p.8, (2.18): the single-Q Born collision expression. -/
def bornKernel (a : GasTracerParameters) (beta : ℝ) (V : Momentum → ℝ)
    (r : MomentumKernel) (P Pprime : Momentum) : ℂ :=
  ∫ Q, (bornMultiplier a beta V (P - Q) Q : ℂ) * r (P - Q) (Pprime - Q) *
    (bornMultiplier a beta V (Pprime - Q) Q : ℂ) -
      (((bornMultiplier a beta V P Q ^ 2 + bornMultiplier a beta V Pprime Q ^ 2) / 2 : ℝ) : ℂ) * r P Pprime

/-- PDF p.30, (6.1): actual forward-amplitude integral. -/
def forwardAverage (d : CollisionData) (P : Momentum) : ℂ :=
  ∫ p, (d.gas.value p : ℂ) *
    d.amplitude (relativeMomentum d.parameters p P) (relativeMomentum d.parameters p P)

/-- PDF p.6, (2.5): gas-induced energy shift. -/
def energyShift (d : CollisionData) (P : Momentum) : ℝ :=
  -2 * Real.pi * d.parameters.hbar ^ 2 * d.parameters.density /
    reducedMass d.parameters * (forwardAverage d P).re

/-- PDF p.31, (6.8): complex optical potential. -/
def opticalPotential (d : CollisionData) (P : Momentum) : ℂ :=
  (-2 * Real.pi * d.parameters.hbar ^ 2 * d.parameters.density /
    reducedMass d.parameters : ℝ) * forwardAverage d P

/-- PDF p.15: coefficient evaluated with mu_V(p)=mu(p-mV). -/
def boostedCoefficient (d : CollisionData) (v p P Q : Momentum) : ℂ :=
  if Q = 0 then 0 else (Real.sqrt (prefactor d.parameters Q) : ℂ) *
    d.amplitude
      (transverseRelative d.parameters p P Q - (1 / 2 : ℝ) • Q)
      (transverseRelative d.parameters p P Q + (1 / 2 : ℝ) • Q) *
    (Real.sqrt (d.gas.value (gasArgument d.parameters p P Q - d.parameters.m • v)) : ℂ)

/-- PDF p.15: energy shift evaluated with the translated gas density. -/
def boostedEnergyShift (d : CollisionData) (v P : Momentum) : ℝ :=
  -2 * Real.pi * d.parameters.hbar ^ 2 * d.parameters.density /
    reducedMass d.parameters * (∫ p,
      (d.gas.value (p - d.parameters.m • v) : ℂ) *
        d.amplitude (relativeMomentum d.parameters p P) (relativeMomentum d.parameters p P)).re

/-- PDF p.15, (4.4): collision expression with the translated gas coefficient. -/
def boostedCollisionKernel (d : CollisionData) (F : TransverseFrames) (v : Momentum)
    (r : MomentumKernel) (P Pprime : Momentum) : ℂ :=
  ∫ Q, ∫ k, boostedCoefficient d v (F.map Q k) (P - Q) Q *
    r (P - Q) (Pprime - Q) * star (boostedCoefficient d v (F.map Q k) (Pprime - Q) Q) -
      (((Complex.normSq (boostedCoefficient d v (F.map Q k) P Q) +
        Complex.normSq (boostedCoefficient d v (F.map Q k) Pprime Q)) / 2 : ℝ) : ℂ) * r P Pprime

example (a : GasTracerParameters) : prefactor a 0 = 0 := by simp [prefactor]

example (d : CollisionData) (p P : Momentum) : collisionCoefficient d p P 0 = 0 := by
  simp [collisionCoefficient]

example (a : GasTracerParameters) (beta E : ℝ) : maxwellStructure a beta 0 E = 0 := by
  simp [maxwellStructure]

example (a : GasTracerParameters) (V : Momentum → ℝ) (P : Momentum) (beta : ℝ) :
    bornMultiplier a beta V P 0 = 0 := by simp [bornMultiplier]

example (a : GasTracerParameters) (Q : Momentum) : bornAmplitude a (fun _ => 0) Q = 0 := by
  simp [bornAmplitude]

/-- PDF p.45, (8.6): the averaged cross-section retains transverse P dependence. -/
def averagedCrossSection (d : CollisionData) (F : TransverseFrames)
    (beta : ℝ) (P Q : Momentum) : ℝ :=
  ∫ k, maxwellPlane d.parameters.m beta (F.map Q k) * crossSection d
    (transverseRelative d.parameters (F.map Q k) P Q - (1 / 2 : ℝ) • Q)
    (transverseRelative d.parameters (F.map Q k) P Q + (1 / 2 : ℝ) • Q)

/-- PDF pp.45,48, (8.7),(8.23): collision expression for a given medium S.
No Maxwell shape is imposed on S in the generic-medium stationarity theorem. -/
def structureGenerator (d : CollisionData) (F : TransverseFrames) (beta : ℝ)
    (S : Momentum → Momentum → ℝ) (nu : Momentum → ℝ) (P : Momentum) : ℝ :=
  d.parameters.density / reducedMass d.parameters ^ 2 *
    ∫ Q, averagedCrossSection d F beta P Q *
      (S Q (P - Q) * nu (P - Q) - S Q P * nu P)

/-- PDF p.46, (8.10): structure-factor coefficient, retaining complex amplitudes. -/
def structureCoefficient (d : CollisionData) (beta : ℝ) (p P Q : Momentum) : ℂ :=
  (Real.sqrt (d.parameters.density / reducedMass d.parameters ^ 2 *
    maxwellPlane d.parameters.m beta (perpendicular p Q)) : ℂ) *
    d.amplitude
      (transverseRelative d.parameters p P Q - (1 / 2 : ℝ) • Q)
      (transverseRelative d.parameters p P Q + (1 / 2 : ℝ) • Q) *
    (Real.sqrt (maxwellStructure d.parameters beta Q (energyTransfer d.parameters Q P)) : ℂ)

/-- PDF p.46: explicit double integral in structure-factor form. -/
def structureQuantumKernel (d : CollisionData) (F : TransverseFrames) (beta : ℝ)
    (r : MomentumKernel) (P Pprime : Momentum) : ℂ :=
  ∫ Q, ∫ k, structureCoefficient d beta (F.map Q k) (P - Q) Q *
    r (P - Q) (Pprime - Q) * star (structureCoefficient d beta (F.map Q k) (Pprime - Q) Q) -
    (((Complex.normSq (structureCoefficient d beta (F.map Q k) P Q) +
      Complex.normSq (structureCoefficient d beta (F.map Q k) Pprime Q)) / 2 : ℝ) : ℂ) * r P Pprime

example (d : CollisionData) (beta : ℝ) (p P : Momentum) :
    structureCoefficient d beta p P 0 = 0 := by simp [structureCoefficient, maxwellStructure]

/-- PDF p.19, (4.28): most probable thermal gas speed. -/
def thermalSpeed (a : GasTracerParameters) (beta : ℝ) : ℝ := Real.sqrt (2 / (beta * a.m))

/-- PDF pp.19–20, (4.33): constant-cross-section Brownian friction. -/
def brownianFriction (a : GasTracerParameters) (beta sigmaTotal : ℝ) : ℝ :=
  8 / (3 * Real.sqrt Real.pi) * (a.m / a.M) * a.density * thermalSpeed a beta * sigmaTotal

/-- PDF pp.19–20: exact moment equations defining the resulting approximate
Brownian model, not the finite-mass QLBE. Right derivatives at zero suffice. -/
def BrownianMomentSolution (eta beta : ℝ) (p : ℝ → Momentum) (e : ℝ → ℝ) : Prop :=
  ContinuousOn p (Set.Ici 0) ∧ ContinuousOn e (Set.Ici 0) ∧
  (∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt p (-eta • p t) (Set.Ici 0) t) ∧
  (∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt e (-2 * eta * (e t - 3 / (2 * beta))) (Set.Ici 0) t)

/-- PDF p.28, (5.16): momentum diffusion coefficient. -/
def momentumDiffusion (M beta eta : ℝ) : ℝ := eta * M / beta

/-- PDF p.28, (5.17): quantum position diffusion coefficient. -/
def positionDiffusion (M beta hbar eta : ℝ) : ℝ := eta * beta * hbar ^ 2 / (16 * M)

example (M beta hbar : ℝ) : positionDiffusion M beta hbar 0 = 0 := by
  simp [positionDiffusion]

/-- PDF pp.43–44: direct quantum momentum-coherence exponent. -/
def quantumExponent (M beta eta t : ℝ) (delta : Momentum) : ℝ :=
  beta * ‖delta‖ ^ 2 / (16 * M) * eta * t

/-- PDF pp.43–44: dispersion-induced exponent, kept separate from the
incorrectly printed full convolution formula. -/
def dispersionExponent (M beta hbar eta t : ℝ) (delta : Momentum) : ℝ :=
  ‖delta‖ ^ 2 * eta * t ^ 3 / (12 * M * beta * hbar ^ 2)

example (M beta eta t : ℝ) : quantumExponent M beta eta t 0 = 0 := by
  simp [quantumExponent]

open QAlgorithms.Papers.Independent.Dependency50.P13
  (TraceClass State relativeEntropy traceNormTopology)
open QAlgorithms.Papers.Independent.Next46.P09 (IsTraceLinear IsTraceCP)

/-- PDF p.17: a given conservative QDS on the full trace class of an
arbitrary complete complex Hilbert space. The source's finite-volume setting
is represented through its given trace-class invariant state, not a finite matrix.
The state maps are tied to the linear CP maps, not independent dynamics. -/
structure ConservativeQDS {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {I : Type*} (b : HilbertBasis I ℂ H) where
  maps : NNReal → TraceClass H → TraceClass H
  linear : ∀ t, IsTraceLinear (maps t)
  cp : ∀ t, IsTraceCP (maps t)
  stateMap : NNReal → State b → State b
  compatible : ∀ t rho, (stateMap t rho).val = maps t rho.val
  initial : ∀ rho, maps 0 rho = rho
  semigroup : ∀ s t rho, maps (s + t) rho = maps s (maps t rho)
  tracePreserving : ∀ t rho,
    QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b (maps t rho).val =
      QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b rho.val
  continuous :
    letI : TopologicalSpace (TraceClass H) := traceNormTopology
    ∀ rho, Continuous (fun t : NNReal => maps t rho)

/-- PDF p.17, (4.17): k_B times accepted extended nats Umegaki entropy. -/
def boltzmannRelativeEntropy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {I : Type*} {b : HilbertBasis I ℂ H}
    (kB : ℝ) (rho sigma : State b) : ℝ≥0∞ :=
  ENNReal.ofReal kB * relativeEntropy rho.val sigma.val

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {I : Type*} {b : HilbertBasis I ℂ H} (T : ConservativeQDS b) (rho : TraceClass H) :
    T.maps 0 rho = rho := T.initial rho

/-- PDF p.31, (6.4): unit direction used for ordinary solid-angle integration. -/
def sphereDirection (theta phi : ℝ) : Momentum :=
  WithLp.toLp 2 ![Real.sin theta * Real.cos phi, Real.sin theta * Real.sin phi, Real.cos theta]

/-- PDF p.31: total cross-section using dOmega=sin(theta)dtheta dphi.
The p=0 value is a null-relative-momentum convention in the flux integral. -/
def totalCrossSection (d : CollisionData) (p : Momentum) : ℝ :=
  if p = 0 then 0 else
    ∫ theta in Set.Icc (0 : ℝ) Real.pi, Real.sin theta *
      ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        crossSection d (‖p‖ • sphereDirection theta phi) p

/-- PDF pp.30–31, (6.3)–(6.4): loss as relative flux times total cross-section. -/
def fluxLoss (d : CollisionData) (P : Momentum) : ℝ :=
  d.parameters.density / reducedMass d.parameters * ∫ p,
    d.gas.value p * ‖relativeMomentum d.parameters p P‖ * totalCrossSection d (relativeMomentum d.parameters p P)

/-- PDF p.31: the cited optical theorem, together with the actual common
finite-integral domain. Optical equality is imposed on scattering data, not on
the desired loss-rate conclusion. -/
def OpticalDomain (d : CollisionData) (F : TransverseFrames) (P : Momentum) : Prop :=
  (∀ p, p ≠ 0 → totalCrossSection d p =
    4 * Real.pi * d.parameters.hbar / ‖p‖ * (d.amplitude p p).im) ∧
  (∀ p, p ≠ 0 →
    (∀ᵐ theta ∂volume.restrict (Set.Icc (0 : ℝ) Real.pi),
      IntegrableOn (fun phi => crossSection d (‖p‖ • sphereDirection theta phi) p)
        (Set.Icc 0 (2 * Real.pi))) ∧
    IntegrableOn (fun theta => Real.sin theta * ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
      crossSection d (‖p‖ • sphereDirection theta phi) p) (Set.Icc 0 Real.pi)) ∧
  (∀ᵐ Q : Momentum, Integrable (rateIntegrand d F P Q)) ∧
  Integrable (outgoingIntensity d F P) ∧
  Integrable (fun p => (d.gas.value p : ℂ) *
    d.amplitude (relativeMomentum d.parameters p P) (relativeMomentum d.parameters p P)) ∧
  Integrable (fun p => d.gas.value p * ‖relativeMomentum d.parameters p P‖ *
    totalCrossSection d (relativeMomentum d.parameters p P))

example (d : CollisionData) : totalCrossSection d 0 = 0 := by simp [totalCrossSection]

/-- PDF p.6, (2.1): full formal momentum-kernel generator. -/
def fullKernel (d : CollisionData) (F : TransverseFrames) (r : MomentumKernel)
    (P Pprime : Momentum) : ℂ :=
  (-Complex.I / d.parameters.hbar) *
    ((‖P‖ ^ 2 / (2 * d.parameters.M) + energyShift d P -
      (‖Pprime‖ ^ 2 / (2 * d.parameters.M) + energyShift d Pprime) : ℝ) : ℂ) *
        r P Pprime + collisionKernel d F r P Pprime

/-- PDF p.31: no-jump wave multiplier for the optical potential, with kinetic energy. -/
def noJumpFactor (d : CollisionData) (t : ℝ) (P : Momentum) : ℂ :=
  Complex.exp (-Complex.I * (t / d.parameters.hbar : ℝ) *
    (((‖P‖ ^ 2 / (2 * d.parameters.M) : ℝ) : ℂ) + opticalPotential d P))

/-- PDF p.31: actual wave-function representative of the conditioned pure state. -/
def noJumpWave (d : CollisionData) (psi : Momentum → ℂ) (t : ℝ) (P : Momentum) : ℂ :=
  noJumpFactor d t P * psi P

/-- PDF p.31: conditioned no-jump kernel, with conjugation on the right. -/
def noJumpKernel (d : CollisionData) (t : ℝ) (r : MomentumKernel) (P Pprime : Momentum) : ℂ :=
  noJumpFactor d t P * r P Pprime * star (noJumpFactor d t Pprime)

/-- PDF p.32, (6.13): physical square-root branch, continuous from n=1 at
zero gas density. The gas density n varies while the beam and gas law are fixed. -/
def refractiveIndex (d : CollisionData) (K : Momentum) (n : ℝ) : ℂ :=
  Complex.sqrt (1 + (4 * Real.pi * n * d.parameters.M /
    (‖K‖ ^ 2 * reducedMass d.parameters) : ℝ) *
      forwardAverage d (d.parameters.hbar • K))

/-- PDF p.32, (6.14)–(6.16): the first-order coefficient per unit gas density. -/
def refractiveSlope (d : CollisionData) (K : Momentum) : ℂ :=
  (2 * Real.pi * d.parameters.M / (‖K‖ ^ 2 * reducedMass d.parameters) : ℝ) *
    forwardAverage d (d.parameters.hbar • K)

/-- PDF p.33, (6.17): radial thermal convolution for nonzero beam velocity. -/
def radialForwardIntegrand (a : GasTracerParameters) (beta speed : ℝ) (g : ℝ → ℂ) (v : ℝ) : ℂ :=
  (v / (thermalSpeed a beta * speed) *
    Real.sinh (2 * v * speed / thermalSpeed a beta ^ 2) *
    Real.exp (-(v ^ 2 + speed ^ 2) / thermalSpeed a beta ^ 2) : ℝ) *
      g (reducedMass a * v ^ 2 / 2)

/-- PDF pp.27–28, (5.11): exact plane-integral friction functional. -/
def planeFriction (d : CollisionData) (F : TransverseFrames) (beta : ℝ) : ℝ :=
  beta * d.parameters.density / (6 * d.parameters.M * d.parameters.m) *
    ∫ Q, ‖Q‖ * ∫ k, maxwell d.parameters.m beta (F.map Q k + (1 / 2 : ℝ) • Q) *
      crossSection d (F.map Q k - (1 / 2 : ℝ) • Q) (F.map Q k + (1 / 2 : ℝ) • Q)

/-- PDF pp.25,28,57, (5.2),(5.13),(A.32): common angular functional. -/
def angularFriction (a : GasTracerParameters) (beta : ℝ) (sigma : ℝ → ℝ → ℝ) : ℝ :=
  16 / 3 * Real.sqrt Real.pi * (a.m / a.M) * a.density * thermalSpeed a beta *
    ∫ u in Set.Ioi (0 : ℝ), u ^ 5 * Real.exp (-u ^ 2) *
      ∫ theta in Set.Icc (0 : ℝ) Real.pi,
        Real.sin theta * (1 - Real.cos theta) * sigma theta (u * Real.sqrt (2 * a.m / beta))

/-- PDF pp.19,22: standard entire 1F1(a;b;z), used only for b>0.
The value at zero is written separately so no sin(x)/x or erf(x)/x default
is used at zero velocity. For b>0 the series is absolutely convergent. -/
def kummer (a b z : ℝ) : ℝ :=
  if z = 0 then 1 else ∑' n : ℕ, rising a n / rising b n * z ^ n / (n.factorial : ℝ)

/-- PDF p.22: relative-speed power, assigned zero on the single null point
where a negative power would be singular. This does not change its integral. -/
def speedPower (a : GasTracerParameters) (exponent : ℝ) (P p : Momentum) : ℝ :=
  let v := (1 / a.m) • p - (1 / a.M) • P
  if v = 0 then 0 else Real.rpow ‖v‖ (exponent + 1)

/-- PDF p.22: thermal collision rate for the differential law c|v-V|^a. -/
def powerCollisionRate (a : GasTracerParameters) (beta c exponent : ℝ) (P : Momentum) : ℝ :=
  a.density * (4 * Real.pi * c) * ∫ p, maxwell a.m beta p * speedPower a exponent P p

/-- PDF p.22, (4.45): effective cross-section; only P!=0 is used. -/
def effectiveCrossSection (a : GasTracerParameters) (beta c exponent : ℝ) (P : Momentum) : ℝ :=
  powerCollisionRate a beta c exponent P / (a.density * ‖P‖ / a.M)

example (a b : ℝ) : kummer a b 0 = 1 := by simp [kummer]

example (a : ℝ) : rising a 0 = 1 := by simp [rising]

/-- PDF p.22, (4.49): the standard real error function, via its Gaussian integral. -/
def errorFunction (x : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * ∫ y in (0 : ℝ)..x, Real.exp (-(y ^ 2))

example : errorFunction 0 = 0 := by simp [errorFunction]

/-- PDF p.37, (7.20): semiclassical London total-cross-section coefficient;
this is a model input, not a claim about every singular -C6/r^6 potential. -/
def londonCoefficient (a : GasTracerParameters) (C6 : ℝ) : ℝ :=
  Real.pi ^ 2 / (Real.sin (Real.pi / 5) * Real.Gamma (2 / 5)) *
    Real.rpow (3 * Real.pi * C6 / (8 * a.hbar)) (2 / 5 : ℝ)

/-- PDF pp.37–38: London collision frequency, an actual thermal convolution. -/
def londonRate (a : GasTracerParameters) (beta C6 : ℝ) (P : Momentum) : ℝ :=
  powerCollisionRate a beta (londonCoefficient a C6 / (4 * Real.pi)) (-2 / 5) P

/-- PDF p.38, (7.23): zero-speed collision frequency. -/
def londonBaseRate (a : GasTracerParameters) (beta C6 : ℝ) : ℝ :=
  a.density * 4 * Real.pi * Real.Gamma (9 / 10) / (5 * Real.sin (Real.pi / 5)) *
    Real.rpow (3 * Real.pi * C6 / (2 * a.hbar)) (2 / 5 : ℝ) *
    Real.rpow (thermalSpeed a beta) (3 / 5 : ℝ)

/-- PDF pp.35–37: normalized characteristic function of the frozen-label
transfer law (7.9). The 1/Gamma normalization missing below (7.19) is explicit. -/
def frozenCharacteristic (d : CollisionData) (F : TransverseFrames)
    (P0 S : Momentum) : ℂ :=
  ∫ Q, (transferRate d F P0 Q / collisionLossRate d F P0 : ℝ) *
    Complex.exp (Complex.I * (momentumDot Q S / d.parameters.hbar : ℝ))

/-- PDF pp.35,37: position kernel of the specified frozen-label model. -/
def frozenPositionGenerator (d : CollisionData) (F : TransverseFrames)
    (P0 : Momentum) (r : MomentumKernel) (X Xprime : Momentum) : ℂ :=
  ∫ Q, (transferRate d F P0 Q : ℂ) *
    (Complex.exp (Complex.I * (momentumDot Q (X - Xprime) / d.parameters.hbar : ℝ)) - 1) * r X Xprime

end QAlgorithms.Papers.Independent.Intake100.P64


