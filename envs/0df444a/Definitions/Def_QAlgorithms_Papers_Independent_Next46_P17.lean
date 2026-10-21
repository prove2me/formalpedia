-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17
-- name    : QAlgorithms_Papers_Independent_Next46_P17
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T13:17:46.758664+00:00
-- url     : https://prove2.me/theorems/45608581-f261-4fd0-9fe8-535ed06a691b
-- title:
--   Definitions for The entropy power inequality for quantum systems
-- statement:
--   The objects the formalized statements of *The entropy power inequality for quantum systems* (arXiv:1205.3409) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `divergenceCurve`: PDF pp.9–10, (69): the relative entropy to a moving state, in nats. `toReal` is used only under local finiteness in `FisherRegular` below.
--   - `FisherRegular`: PDF pp.5,9, the actual finite twice-differentiability domain of (69). The first derivative exists throughout a neighborhood; its derivative exists at `base`. No symmetric Dini derivative or default derivative is substituted.
--   - `fisher`: PDF p.10, (69): genuine divergence-based Fisher information when `FisherRegular rho base` holds. State normalization is required by each theorem.
--   - `singleBeamCoefficient`: PDF p.7, (44): number-basis coefficient of the one-pair beam splitter. This is the binomial expansion of (a*x+b*y)^p (b*x-a*y)^q on normalized number vectors, a=sqrt(lambda), b=sqrt(1-lambda). The second port has the printed minus sign. This definition includes every finite photon sector.
--   - `beamCoefficient`: PDF p.7, (44): the source's n independent pairs of beam splitters.
--   - `beamSplitter`: PDF p.7, (45): conjugate by the full number-basis unitary and trace the second n modes. Each row of U has finite support by photon conservation; the remaining trace series converges on trace-class inputs. In particular this acts on correlated densities, and not only on product or Gaussian inputs.
--   - `bosonicEntropyPower`: PDF pp.2,12, (89): entropy power, including infinite entropy. For positive n and finite S this is exp(S/n); infinite S gives infinity.
--   - `InterleavedPhaseVector`: PDF pp.5–6, (25)–(28): full 2n-dimensional real phase space.
--   - `weylCoefficient`: PDF p.5, (25): D(xi)=exp(i xi.J.R). The accepted displacement coefficients are exp(z*a_dagger-conj(z)*a); hence z_j=-(xi_Q+i*xi_P)/sqrt(2). This sign is fixed by [Q,P]=i, not by the appendix's ambiguous coherent label.
--   - `conjugateCoefficient`: PDF pp.7,11, (45),(80): matrix coefficients of U X U-adjoint. For the concrete bounded Weyl unitaries used here, both iterated row series converge on trace-class X; no arbitrary distributional operator is used.
--   - `diffusionChannel`: PDF pp.7–8, (50)–(54): canonical trace-class Gaussian displacement average for t>0, with the identity at t=0. Scalar coefficient integrals are absolutely integrable on trace-class inputs and specify the trace-norm integral. The displacement density is exp(-||xi||^2/t)/(pi*t)^n, i.e. variance t/2.
--   - `independentHeat`: PDF p.8, (56): independent heat channels on both factors, including correlated trace-class inputs. The second-factor action retains every block.
--   - `directionCoefficient`: PDF p.11, (79): number coefficients of D_Q(theta)=exp(i theta P) and D_P(theta)=exp(-i theta Q), with Q encoded by 0 and P by 1.
--   - `directionOrbit`: PDF p.11, (80): actual normalized displacement family for a density input.
--   - `TotalFisherRegular`: PDF pp.9,11, (69),(81): genuine finite directional Fisher domain.
--   - `totalFisher`: PDF p.11, (81): unaveraged sum of exactly the 2n displacement-direction second derivatives, used only with TotalFisherRegular.
--   - `diffusionCharacteristic`: PDF p.6, (28): trace of D(xi) X on full trace-class operators. The inner row series and outer trace series converge on that domain.
--   - `qFunction`: PDF p.13, (100): the exact Fourier Gaussian-smoothed Q function. The sign is exp(+i xi.J.eta)=exp(-i (J xi).eta). The Gaussian times the bounded characteristic function is integrable; real part identifies the real-valued density without selecting a coherent-label correction.
--   - `raisingCoefficient`: PDF pp.5–6, (30)–(31): raising coefficient in the full number basis. This is an unbounded quadrature ingredient, not a bounded-operator surrogate.
--   - `loweringCoefficient`: PDF pp.5–6: lowering coefficient; the vacuum column is explicitly zero.
--   - `quadratureCoefficient`: PDF p.5: Q=(a+a_dagger)/sqrt(2), P=i(a_dagger-a)/sqrt(2), hence [Q,P]=i. Rows and columns are finitely supported; no bounded cfc is applied to them.
--   - `quadratureExpectation`: PDF p.6, (30)–(31): real expectation of a finite-band quadrature polynomial. Used for degree at most two on finite-mean-energy densities, where all displayed row and trace series converge absolutely.
--   - `firstMoments`: PDF p.6, (30): actual first moments of a finite-energy density.
--   - `quadratureCovariance`: PDF p.6, (31): twice the symmetrized centered covariance, with vacuum I. The anticommutator is evaluated using its finite-band coefficient matrix.
--   - `gaussianCoefficient`: PDF p.6, (27),(32): computed Gaussian density by Weyl inversion. For physical covariance gamma>=iJ (and thus gamma>0), the Gaussian integrand is integrable. The scalar characteristic is reused from Claimed50.P19 with v=J^T xi, fixing both the linear and quadratic source signs. No arbitrary state parameter replaces the state the page constructs.
--   - `gaussification`: PDF p.9, (64): the actual Gaussian with the first and second moments of X, used only on finite-energy normalized densities.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, https://arxiv.org/abs/1205.3409v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

/-!
Statements from Koenig and Smith, arXiv:1205.3409v2.
The imports are pinned accepted-library modules. No run-local chunk is imported.
Countable number-basis coordinates describe the full bosonic Hilbert space.
Deferred analytic interfaces and source discrepancies are recorded in HARD.md/GAPS.json.
Compilation is pending the explicitly requested batch handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Next46.P17

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff tensorApply)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)
open QAlgorithms.Papers.Independent.Claimed50.P19 (productWeyl FiniteMeanEnergy PhysicalCovariance Cov FockIndex covarianceCharacteristicValue)
open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

/-!
Definition reuse in this repair: `FockIndex` and `covarianceCharacteristicValue`
come directly from the pinned Claimed50.P19 import. In Gaussian inversion the
argument v=J^T xi gives m.v=xi.J.m and v^T gamma v=xi^T J^T gamma J xi.

The distinct descriptive local names retain the source's interfaces:
* `bosonicEntropyPower` is exp(S/n), rather than Dependency50.P05's 2^(-h).
* `InterleavedPhaseVector` is a Euclidean vector with interleaved coordinates;
  Dependency50.P10.Phase is a grouped coordinate index, not a vector space.
* `interleavedSymplecticForm` is imported from pinned Frontier30.P08.
  Its matrix J is contracted as xi^T J eta in the Q-function Fourier phase;
  the interleaved order and [[0,1],[-1,0]] blocks agree with (25).
* `diffusionChannel` is the full bosonic Gaussian channel; Information100.P32.heat
  is a real qubit collision-energy transfer.
* `diffusionCharacteristic` is a multimode coefficient trace; the one-mode
  bounded-operator characteristic in Dependency50.P39 has a different domain.
* `quadratureCovariance` is the actual quantum anticommutator covariance;
  FiniteVectorMoments.covariance is a classical random-vector covariance.
The exact source and reuse decisions are recorded separately in ASSESSMENT.json.
-/

/-- PDF pp.9–10, (69): the relative entropy to a moving state, in nats.
`toReal` is used only under local finiteness in `FisherRegular` below. -/
def divergenceCurve {I : Type} (rho : ℝ → Matrix I I ℂ) (base : ℝ) : ℝ → ℝ :=
  fun theta => (extendedRelativeEntropyNats (rho base) (rho theta)).toReal

/-- PDF pp.5,9, the actual finite twice-differentiability domain of (69).
The first derivative exists throughout a neighborhood; its derivative exists at
`base`. No symmetric Dini derivative or default derivative is substituted. -/
def FisherRegular {I : Type} (rho : ℝ → Matrix I I ℂ) (base : ℝ) : Prop :=
  (∀ᶠ theta in 𝓝 base, extendedRelativeEntropyNats (rho base) (rho theta) ≠ ⊤) ∧
  (∀ᶠ theta in 𝓝 base, DifferentiableAt ℝ (divergenceCurve rho base) theta) ∧
  DifferentiableAt ℝ (deriv (divergenceCurve rho base)) base

/-- PDF p.10, (69): genuine divergence-based Fisher information when
`FisherRegular rho base` holds. State normalization is required by each theorem. -/
def fisher {I : Type} (rho : ℝ → Matrix I I ℂ) (base : ℝ) : ℝ :=
  deriv (deriv (divergenceCurve rho base)) base

example {I : Type} (rho : State I) :
    (∑' i, (rho.coefficients i i).re) = 1 := rho.density.2.2.2

example {I : Type} (rho : ℝ → Matrix I I ℂ) (base : ℝ)
    (h : FisherRegular rho base) :
    DifferentiableAt ℝ (deriv (divergenceCurve rho base)) base := h.2.2

/-- PDF p.7, (44): number-basis coefficient of the one-pair beam splitter.
This is the binomial expansion of (a*x+b*y)^p (b*x-a*y)^q on normalized
number vectors, a=sqrt(lambda), b=sqrt(1-lambda). The second port has the
printed minus sign. This definition includes every finite photon sector. -/
def singleBeamCoefficient (lam : ℝ) (r s p q : ℕ) : ℝ :=
  if r + s = p + q then
    Real.sqrt (((Nat.factorial r : ℝ) * (Nat.factorial s : ℝ)) /
      ((Nat.factorial p : ℝ) * (Nat.factorial q : ℝ))) *
      ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (q + 1),
        if k + l = r then
          (Nat.choose p k : ℝ) * (Nat.choose q l : ℝ) *
            Real.sqrt lam ^ k * Real.sqrt (1 - lam) ^ (p - k) *
            Real.sqrt (1 - lam) ^ l * (-Real.sqrt lam) ^ (q - l)
        else 0
  else 0

/-- PDF p.7, (44): the source's n independent pairs of beam splitters. -/
def beamCoefficient {n : ℕ} (lam : ℝ)
    (out input : FockIndex n × FockIndex n) : ℝ :=
  ∏ j : Fin n, singleBeamCoefficient lam (out.1 j) (out.2 j) (input.1 j) (input.2 j)

/-- PDF p.7, (45): conjugate by the full number-basis unitary and trace the
second n modes. Each row of U has finite support by photon conservation;
the remaining trace series converges on trace-class inputs. In particular this
acts on correlated densities, and not only on product or Gaussian inputs. -/
def beamSplitter {n : ℕ} (lam : ℝ)
    (X : Matrix (FockIndex n × FockIndex n) (FockIndex n × FockIndex n) ℂ) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  fun a b => ∑' k : FockIndex n,
    ∑' u : FockIndex n × FockIndex n, ∑' v : FockIndex n × FockIndex n,
      (beamCoefficient lam (a, k) u : ℂ) * X u v *
        star (beamCoefficient lam (b, k) v : ℂ)

/-- PDF pp.2,12, (89): entropy power, including infinite entropy.
For positive n and finite S this is exp(S/n); infinite S gives infinity. -/
def bosonicEntropyPower (n : ℕ) (S : ℝ≥0∞) : ℝ≥0∞ :=
  if S = ⊤ then ⊤ else ENNReal.ofReal (Real.exp (S.toReal / (n : ℝ)))

example (lam : ℝ) : singleBeamCoefficient lam 0 0 0 0 = 1 := by
  simp [singleBeamCoefficient]

example (lam : ℝ) : singleBeamCoefficient lam 1 0 1 0 = Real.sqrt lam := by
  simp [singleBeamCoefficient, Finset.sum_range_succ]

example (lam : ℝ) : singleBeamCoefficient lam 1 0 0 1 = Real.sqrt (1 - lam) := by
  simp [singleBeamCoefficient, Finset.sum_range_succ]

example (lam : ℝ) : singleBeamCoefficient lam 0 1 0 1 = -Real.sqrt lam := by
  simp [singleBeamCoefficient, Finset.sum_range_succ]

example {n : ℕ} (lam : ℝ) :
    beamCoefficient lam ((fun _ : Fin n => 0), (fun _ : Fin n => 0))
      ((fun _ : Fin n => 0), (fun _ : Fin n => 0)) = 1 := by
  simp [beamCoefficient, singleBeamCoefficient]

example (n : ℕ) : bosonicEntropyPower n ⊤ = ⊤ := by simp [bosonicEntropyPower]

example (n : ℕ) : bosonicEntropyPower n 0 = 1 := by simp [bosonicEntropyPower]

/-- PDF pp.5–6, (25)–(28): full 2n-dimensional real phase space. -/
abbrev InterleavedPhaseVector (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin 2)

/-- PDF p.5, (25): D(xi)=exp(i xi.J.R). The accepted displacement coefficients
are exp(z*a_dagger-conj(z)*a); hence z_j=-(xi_Q+i*xi_P)/sqrt(2).
This sign is fixed by [Q,P]=i, not by the appendix's ambiguous coherent label. -/
def weylCoefficient {n : ℕ} (xi : InterleavedPhaseVector n) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  productWeyl (fun j => -((xi (j, 0) : ℂ) + Complex.I * (xi (j, 1) : ℂ)) /
    (Real.sqrt 2 : ℂ))

/-- PDF pp.7,11, (45),(80): matrix coefficients of U X U-adjoint.
For the concrete bounded Weyl unitaries used here, both iterated row series
converge on trace-class X; no arbitrary distributional operator is used. -/
def conjugateCoefficient {I : Type} (U X : Matrix I I ℂ) : Matrix I I ℂ :=
  fun a b => ∑' i, ∑' j, U a i * X i j * star (U b j)

/-- PDF pp.7–8, (50)–(54): canonical trace-class Gaussian displacement
average for t>0, with the identity at t=0. Scalar coefficient integrals are
absolutely integrable on trace-class inputs and specify the trace-norm integral.
The displacement density is exp(-||xi||^2/t)/(pi*t)^n, i.e. variance t/2. -/
def diffusionChannel {n : ℕ} (t : ℝ) (X : Matrix (FockIndex n) (FockIndex n) ℂ) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  if 0 < t then fun a b => ∫ xi : InterleavedPhaseVector n,
    (((Real.pi * t) ^ n)⁻¹ * Real.exp (-‖xi‖ ^ 2 / t) : ℝ) •
      conjugateCoefficient (weylCoefficient xi) X a b
  else X

/-- PDF p.8, (56): independent heat channels on both factors, including
correlated trace-class inputs. The second-factor action retains every block. -/
def independentHeat {n : ℕ} (tX tY : ℝ)
    (X : Matrix (FockIndex n × FockIndex n) (FockIndex n × FockIndex n) ℂ) :
    Matrix (FockIndex n × FockIndex n) (FockIndex n × FockIndex n) ℂ :=
  tensorApply (diffusionChannel tX) (fun p q =>
    diffusionChannel tY (fun a b => X (p.1, a) (q.1, b)) p.2 q.2)

/-- PDF p.11, (79): number coefficients of D_Q(theta)=exp(i theta P)
and D_P(theta)=exp(-i theta Q), with Q encoded by 0 and P by 1. -/
def directionCoefficient {n : ℕ} (R : Fin n × Fin 2) (theta : ℝ) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  productWeyl (fun j => if j = R.1 then
    if R.2 = 0 then -(theta : ℂ) / (Real.sqrt 2 : ℂ)
    else -Complex.I * (theta : ℂ) / (Real.sqrt 2 : ℂ)
    else 0)

/-- PDF p.11, (80): actual normalized displacement family for a density input. -/
def directionOrbit {n : ℕ} (R : Fin n × Fin 2)
    (X : Matrix (FockIndex n) (FockIndex n) ℂ) (theta : ℝ) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  conjugateCoefficient (directionCoefficient R theta) X

/-- PDF pp.9,11, (69),(81): genuine finite directional Fisher domain. -/
def TotalFisherRegular {n : ℕ} (X : Matrix (FockIndex n) (FockIndex n) ℂ) : Prop :=
  ∀ R : Fin n × Fin 2, FisherRegular (directionOrbit R X) 0

/-- PDF p.11, (81): unaveraged sum of exactly the 2n displacement-direction
second derivatives, used only with TotalFisherRegular. -/
def totalFisher {n : ℕ} (X : Matrix (FockIndex n) (FockIndex n) ℂ) : ℝ :=
  ∑ R : Fin n × Fin 2, fisher (directionOrbit R X) 0

/-- PDF p.6, (28): trace of D(xi) X on full trace-class operators.
The inner row series and outer trace series converge on that domain. -/
def diffusionCharacteristic {n : ℕ} (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (xi : InterleavedPhaseVector n) : ℂ :=
  ∑' i, ∑' j, weylCoefficient xi i j * X j i

/-- PDF p.13, (100): the exact Fourier Gaussian-smoothed Q function.
The sign is exp(+i xi.J.eta)=exp(-i (J xi).eta). The Gaussian times the
bounded characteristic function is integrable; real part identifies the
real-valued density without selecting a coherent-label correction. -/
def qFunction {n : ℕ} (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (xi : InterleavedPhaseVector n) : ℝ :=
  (((2 * Real.pi) ^ (2 * n))⁻¹ : ℝ) *
    (∫ eta : InterleavedPhaseVector n, Complex.exp (Complex.I * ((∑ i : Fin n × Fin 2, ∑ j : Fin n × Fin 2,
        xi i * interleavedSymplecticForm n i j * eta j : ℝ) : ℂ)) *
      diffusionCharacteristic X eta * (Real.exp (-‖eta‖ ^ 2 / 4) : ℂ)).re

example {n : ℕ} (X : Matrix (FockIndex n) (FockIndex n) ℂ) : diffusionChannel 0 X = X := by
  simp [diffusionChannel]

example {n : ℕ} (xi : InterleavedPhaseVector n) :
    (∑ i : Fin n × Fin 2, ∑ j : Fin n × Fin 2,
      xi i * interleavedSymplecticForm n i j * (0 : InterleavedPhaseVector n) j) = 0 := by
  simp

example {n : ℕ} (X : Matrix (FockIndex n) (FockIndex n) ℂ)
    (h : TotalFisherRegular X) (R : Fin n × Fin 2) :
    FisherRegular (directionOrbit R X) 0 := h R

/-- PDF pp.5–6, (30)–(31): raising coefficient in the full number basis.
This is an unbounded quadrature ingredient, not a bounded-operator surrogate. -/
def raisingCoefficient {n : ℕ} (mode : Fin n) (a b : FockIndex n) : ℂ :=
  if a = Function.update b mode (b mode + 1) then (Real.sqrt (b mode + 1) : ℂ) else 0

/-- PDF pp.5–6: lowering coefficient; the vacuum column is explicitly zero. -/
def loweringCoefficient {n : ℕ} (mode : Fin n) (a b : FockIndex n) : ℂ :=
  if 0 < b mode ∧ a = Function.update b mode (b mode - 1) then
    (Real.sqrt (b mode) : ℂ) else 0

/-- PDF p.5: Q=(a+a_dagger)/sqrt(2), P=i(a_dagger-a)/sqrt(2), hence [Q,P]=i.
Rows and columns are finitely supported; no bounded cfc is applied to them. -/
def quadratureCoefficient {n : ℕ} (R : Fin n × Fin 2) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  fun a b => if R.2 = 0 then
    (raisingCoefficient R.1 a b + loweringCoefficient R.1 a b) / (Real.sqrt 2 : ℂ)
  else Complex.I * (raisingCoefficient R.1 a b - loweringCoefficient R.1 a b) /
    (Real.sqrt 2 : ℂ)

/-- PDF p.6, (30)–(31): real expectation of a finite-band quadrature polynomial.
Used for degree at most two on finite-mean-energy densities, where all displayed
row and trace series converge absolutely. -/
def quadratureExpectation {n : ℕ}
    (X A : Matrix (FockIndex n) (FockIndex n) ℂ) : ℝ :=
  (∑' i, ∑' j, A i j * X j i).re

/-- PDF p.6, (30): actual first moments of a finite-energy density. -/
def firstMoments {n : ℕ} (X : Matrix (FockIndex n) (FockIndex n) ℂ) :
    (Fin n × Fin 2) → ℝ :=
  fun R => quadratureExpectation X (quadratureCoefficient R)

/-- PDF p.6, (31): twice the symmetrized centered covariance, with vacuum I.
The anticommutator is evaluated using its finite-band coefficient matrix. -/
def quadratureCovariance {n : ℕ} (X : Matrix (FockIndex n) (FockIndex n) ℂ) : Cov n :=
  fun R S => quadratureExpectation X (fun a b => ∑' k : FockIndex n,
    (quadratureCoefficient R a k * quadratureCoefficient S k b +
    quadratureCoefficient S a k * quadratureCoefficient R k b)) -
      2 * firstMoments X R * firstMoments X S

/-- PDF p.6, (27),(32): computed Gaussian density by Weyl inversion.
For physical covariance gamma>=iJ (and thus gamma>0), the Gaussian integrand
is integrable. The scalar characteristic is reused from Claimed50.P19 with
v=J^T xi, fixing both the linear and quadratic source signs.
No arbitrary state parameter replaces the state the page constructs. -/
def gaussianCoefficient {n : ℕ} (gamma : Cov n)
    (d : (Fin n × Fin 2) → ℝ) : Matrix (FockIndex n) (FockIndex n) ℂ :=
  fun a b => (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
    ∫ xi : InterleavedPhaseVector n,
      covarianceCharacteristicValue gamma d
        (fun R => if R.2 = 0 then -xi (R.1, 1) else xi (R.1, 0)) *
      weylCoefficient (-xi) a b

/-- PDF p.9, (64): the actual Gaussian with the first and second moments of X,
used only on finite-energy normalized densities. -/
def gaussification {n : ℕ} (X : Matrix (FockIndex n) (FockIndex n) ℂ) :
    Matrix (FockIndex n) (FockIndex n) ℂ :=
  gaussianCoefficient (quadratureCovariance X) (firstMoments X)

example {n : ℕ} (gamma : Cov n) (d : (Fin n × Fin 2) → ℝ) :
    covarianceCharacteristicValue gamma d 0 = 1 := by simp [covarianceCharacteristicValue]

example {n : ℕ} (mode : Fin n) (a : FockIndex n) :
    loweringCoefficient mode a (fun _ => 0) = 0 := by simp [loweringCoefficient]

example {n : ℕ} (R : Fin n × Fin 2) :
    firstMoments (0 : Matrix (FockIndex n) (FockIndex n) ℂ) R = 0 := by
  simp [firstMoments, quadratureExpectation]

end QAlgorithms.Papers.Independent.Next46.P17


