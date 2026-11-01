-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P89
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P89
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:17:24.91066+00:00
-- url     : https://prove2.me/theorems/6a81e707-c7c5-417b-a984-8ff7dcef2a31
-- title:
--   Definitions for Optimal continuous variable quantum teleportation with limited resources
-- statement:
--   The objects the formalized statements of *Optimal continuous variable quantum teleportation with limited resources* (arXiv:1705.03017) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `OscillatorChannel`: PDF p.2: an operation on complete single-oscillator coefficient arrays.
--   - `pairKernel`: PDF p.2: basis relabeling of the actual two-mode density, without a cutoff.
--   - `CenteredResource`: PDF p.2: the specified, symmetric, centered Gaussian covariance of an actual normalized trace-class resource. All characteristic series converge. The accepted physicality uses V+iOmega; complex conjugation makes this identical to the source's V-iOmega condition for real V.
--   - `twoModeMeanPhotonEnergy`: PDF p.2: actual per-mode mean photon number, in extended nonnegative reals; infinite energy is retained as infinity, rather than converted to zero.
--   - `bkTest`: PDF pp.2--3: source BK signs, in the argument of exp(i v^T R). D(z) at the output tests D(-g conjugate(z)) on A and D(z) on B. This encodes q_out=q_B+g q_A+g q_in, p_out=p_B-g p_A+g p_in.
--   - `IsBK`: PDF pp.2--3, deterministic BK protocol: exact characteristic-function representation on EVERY input density, including non-Gaussian inputs. The resource, gain and single CPTP map are fixed before the input. This is independent of any asserted Gaussian noise formula.
--   - `FiniteBKRealization`: PDF pp.3--4: a finite-energy Gaussian-resource BK realization with EXACT logarithmic negativity 2r. No photon-energy budget is imposed.
--   - `FiniteBKSimulates`: PDF p.3: finite-energy realizability, distinguished from the closed region.
--   - `priorDensity`: PDF p.4, (11): density of the NORMALIZED Gaussian prior for lambda>0, against planar Lebesgue measure. It is never used as a flat prior at lambda=0.
--   - `teleportedCoherentOverlap`: PDF pp.3--4: squared pure-state overlap. The accepted husimiQ has no 1/pi factor, so it is precisely the overlap, not this paper's Q function. All uses are on trace-class channel outputs; realization is concluded below.
--   - `gaussianPriorFidelity`: PDF p.4, (11): actual prior-averaged overlap, independently of (12).
--   - `phaseInsensitiveFidelityFormula`: PDF p.4, (12): the scalar expression, separate from the actual integral.
--   - `entanglementAccessibleRegion`: PDF pp.3--4, (3),(8): CLOSED scalar region, including limiting channels.
--   - `scalarValues`: PDF p.4: independent scalar objective set over the closed region.
--   - `scalarOptimum`: PDF p.4: the optimum is defined independently of the claimed answer.
--   - `finiteBKValues`: PDF pp.3--4: actually attainable fidelities of finite-energy protocols. A resource and channel precede every input in IsBK.
--   - `finiteBKOptimum`: PDF p.4: operational supremum, independently of the scalar formula.
--   - `stationaryTau`: PDF p.4, immediately before (13): unconstrained stationary transmissivity.
--   - `optimalTau`: PDF p.4: maximizing closed-region channel transmissivity.
--   - `optimalNoise`: PDF p.4: maximizing channel noise.
--   - `optimumClosedForm`: PDF p.4, (13): CLAIMED closed form, not the definition of an optimum.
--   - `familyDenominator`: PDF p.3, (9): denominator, used only where strictly positive.
--   - `familyMinB`: PDF p.3, (9): the lower b coefficient on the nonsingular domain.
--   - `familyA`: PDF p.3, (9): a computed from b, not an independent state hypothesis.
--   - `familyC`: PDF p.3, (9): c computed from b, with source block C=-c sigma_z.
--   - `familyEnergy`: PDF p.3: energy within the displayed family; no global energy minimization.
--   - `familyMinA`: PDF p.3: a on the minimum-energy member of (9).
--   - `familyMinC`: PDF p.3: c on the minimum-energy member of (9).
--   - `familyMinEnergy`: PDF p.3: minimum energy WITHIN family (9).
--   - `tmssCoefficient`: PDF p.3: actual pure TMSS coefficients with the source correlation sign. The alternating sign yields C=-sinh(2r) sigma_z; r is finite.
--   - `tmssKernel`: PDF p.3: full TMSS rank-one coefficient array; normalization is concluded.
--   - `tmssNoise`: PDF p.3, (7): independently defined TMSS noise at gain g and squeezing s.
--   - `minimumSqueezing`: PDF p.3, (10): minimum is defined by the noise equation, NOT its answer. The theorem concludes a least element; no empty real-infimum default is used.
--   - `squeezingClosedForm`: PDF p.3, (10): real arcosh written as log(x+sqrt(x^2-1)). The stated domain ensures its argument is at least one. tau=1 uses (7) directly.
--   - `heterodynePrepare`: PDF p.4: heterodyne POVM d^2beta |beta><beta|/pi followed by coherent preparation |g beta>. The complex overlap retains linearity on trace class.
--   - `tmssOptimalGain`: PDF p.4, (16): optimized positive displacement gain for a fixed TMSS.
--   - `tmssClosedForm`: PDF p.4, (16): claimed fixed-TMSS optimum, distinct from its supremum.
--   - `tmssValues`: PDF p.4: actual fidelities with this fixed TMSS, optimized only over g>0.
--   - `tmssOptimum`: PDF p.4: fixed-TMSS optimum, defined independently of (16).
-- source:
--   Optimal continuous variable quantum teleportation with limited resources, arXiv:1705.03017v5, https://arxiv.org/abs/1705.03017v5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability

/-!
Liuzzo-Scorpo et al., arXiv:1705.03017v5, PDF pp.1--4.
Full completed oscillator spaces, hbar=1, interleaved coordinates, doubled
covariance with vacuum I, squared overlap fidelity, and natural logarithms.
Accepted paper definitions are imported under the independent-paper override.
No finite photon cutoff and no infinite-energy density are introduced.

The BK map is specified by its exact all-input Weyl characteristic, the
phase-space representation of the balanced homodyne/feed-forward protocol.
It is defined from the actual resource characteristic, independently of the
Gaussian-channel simulation assertions. It tests every normalized input.
The local centered-Gaussian adapter explicitly requires covariance symmetry;
it never uses Claimed50.P47.HasBipartiteMoments.

Corrections needing independent moderation: (14)'s tau is gain squared;
(10) is extended at tau=1 and its strict comparison has equality exceptions.
The abstract's all-channel assertion is deferred, not silently restricted.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P89

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel tensorApply traceSize)
open QAlgorithms.Papers.Independent.Dependency50.P39
  (coherentKet coherentCoefficient operatorOfMatrix husimiQ HasFockMatrix CoherentRealized)
open QAlgorithms.Papers.Independent.Frontier30.P14 (weylCharacteristic)
open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel PhysicalCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue standardFormCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Gap48.P26 (PhaseInsensitive coherentKernel)
open QAlgorithms.Entanglement (partialTransposeFirst)

/-!
Repair reuse audit: these paper-specific objects have descriptive names because
accepted short-name matches are different concepts, not reusable equivalents.
Support50.P14.photonEnergy sums all modes on occupation-function indices;
twoModeMeanPhotonEnergy averages two modes on pair indices. Claimed50.P36's
coherentOverlap is a complex overlap of two coherent kets; the present output
fidelity uses the already imported Dependency50.P39.husimiQ. QuditFidelity's
averageFidelity is a finite-dimensional Haar average. Support50.P11's
channelFidelity is finite-dimensional entanglement fidelity. Frontier30.P06's
FeedbackExecution.accessible is accessible information of an executed protocol.
None replaces a Gaussian-prior oscillator integral or the closed (tau,y) region.
The five local bodies and all theorem propositions are otherwise unchanged.
-/

/-- PDF p.2: an operation on complete single-oscillator coefficient arrays. -/
abbrev OscillatorChannel := Matrix ℕ ℕ ℂ → Matrix ℕ ℕ ℂ

/-- PDF p.2: basis relabeling of the actual two-mode density, without a cutoff. -/
def pairKernel (X : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ) : DensityKernel 2 :=
  fun u v => X (u 0, u 1) (v 0, v 1)

/-- PDF p.2: the specified, symmetric, centered Gaussian covariance of an
actual normalized trace-class resource. All characteristic series converge.
The accepted physicality uses V+iOmega; complex conjugation makes this
identical to the source's V-iOmega condition for real V. -/
def CenteredResource (rho : State (ℕ × ℕ)) (V : Cov 2) : Prop :=
  V.transpose = V ∧ PhysicalCovariance V ∧
    ∀ v : QuadratureIndex 2 → ℝ,
      CharacteristicSummable (pairKernel rho.coefficients) v ∧
      multimodeWeylTrace (pairKernel rho.coefficients) v =
        covarianceCharacteristicValue V 0 v

/-- PDF p.2: actual per-mode mean photon number, in extended nonnegative
reals; infinite energy is retained as infinity, rather than converted to zero. -/
def twoModeMeanPhotonEnergy (rho : State (ℕ × ℕ)) : ℝ≥0∞ :=
  ∑' u : ℕ × ℕ,
    ENNReal.ofReal ((((u.1 : ℝ) + (u.2 : ℝ)) / 2) *
      (rho.coefficients u u).re)

/-- PDF pp.2--3: source BK signs, in the argument of exp(i v^T R).
D(z) at the output tests D(-g conjugate(z)) on A and D(z) on B.
This encodes q_out=q_B+g q_A+g q_in, p_out=p_B-g p_A+g p_in. -/
def bkTest (g : ℝ) (z : ℂ) : QuadratureIndex 2 → ℝ :=
  fun i => if i.1 = 0 then
    (if i.2 = 0 then Real.sqrt 2 * g * z.im else Real.sqrt 2 * g * z.re)
  else (if i.2 = 0 then Real.sqrt 2 * z.im else -Real.sqrt 2 * z.re)

/-- PDF pp.2--3, deterministic BK protocol: exact characteristic-function
representation on EVERY input density, including non-Gaussian inputs.
The resource, gain and single CPTP map are fixed before the input.
This is independent of any asserted Gaussian noise formula. -/
def IsBK (rho : State (ℕ × ℕ)) (g : ℝ) (Phi : OscillatorChannel) : Prop :=
  0 < g ∧ IsTraceClassChannel Phi ∧
    ∀ (sigma : State ℕ) (z : ℂ),
      weylCharacteristic (Phi sigma.coefficients) z =
        weylCharacteristic sigma.coefficients ((g : ℂ) * z) *
          multimodeWeylTrace (pairKernel rho.coefficients) (bkTest g z)

/-- PDF pp.3--4: a finite-energy Gaussian-resource BK realization with EXACT
logarithmic negativity 2r. No photon-energy budget is imposed. -/
def FiniteBKRealization (r tau y : ℝ) (Phi : OscillatorChannel) : Prop :=
  ∃ (rho : State (ℕ × ℕ)) (V : Cov 2) (g : ℝ),
    CenteredResource rho V ∧ twoModeMeanPhotonEnergy rho < ⊤ ∧
    traceSize (partialTransposeFirst rho.coefficients) = ENNReal.ofReal (Real.exp (2 * r)) ∧
    IsBK rho g Phi ∧ g ^ 2 = tau ∧ 0 ≤ tau ∧ PhaseInsensitive Phi tau y

/-- PDF p.3: finite-energy realizability, distinguished from the closed region. -/
def FiniteBKSimulates (r tau y : ℝ) : Prop :=
  ∃ Phi : OscillatorChannel, FiniteBKRealization r tau y Phi

/-- PDF p.4, (11): density of the NORMALIZED Gaussian prior for lambda>0,
against planar Lebesgue measure. It is never used as a flat prior at lambda=0. -/
def priorDensity (lambda : ℝ) (alpha : ℂ) : ℝ :=
  (lambda / Real.pi) * Real.exp (-lambda * Complex.normSq alpha)

/-- PDF pp.3--4: squared pure-state overlap. The accepted husimiQ has no
1/pi factor, so it is precisely the overlap, not this paper's Q function.
All uses are on trace-class channel outputs; realization is concluded below. -/
def teleportedCoherentOverlap (Phi : OscillatorChannel) (alpha : ℂ) : ℝ :=
  husimiQ (operatorOfMatrix (Phi (coherentKernel alpha))) alpha

/-- PDF p.4, (11): actual prior-averaged overlap, independently of (12). -/
def gaussianPriorFidelity (lambda : ℝ) (Phi : OscillatorChannel) : ℝ :=
  ∫ alpha : ℂ, priorDensity lambda alpha * teleportedCoherentOverlap Phi alpha

/-- PDF p.4, (12): the scalar expression, separate from the actual integral. -/
def phaseInsensitiveFidelityFormula (lambda tau y : ℝ) : ℝ :=
  2 * lambda / (2 * (1 - Real.sqrt tau) ^ 2 + lambda * (1 + y + tau))

/-- PDF pp.3--4, (3),(8): CLOSED scalar region, including limiting channels. -/
def entanglementAccessibleRegion (r : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ |1 - p.1| ≤ p.2 ∧ Real.exp (-2 * r) * (1 + p.1) ≤ p.2}

/-- PDF p.4: independent scalar objective set over the closed region. -/
def scalarValues (lambda r : ℝ) : Set ℝ :=
  (fun p : ℝ × ℝ => phaseInsensitiveFidelityFormula lambda p.1 p.2) '' entanglementAccessibleRegion r

/-- PDF p.4: the optimum is defined independently of the claimed answer. -/
def scalarOptimum (lambda r : ℝ) : ℝ := sSup (scalarValues lambda r)

/-- PDF pp.3--4: actually attainable fidelities of finite-energy protocols.
A resource and channel precede every input in IsBK. -/
def finiteBKValues (lambda r : ℝ) : Set ℝ :=
  {f | ∃ (tau y : ℝ) (Phi : OscillatorChannel),
    FiniteBKRealization r tau y Phi ∧ f = gaussianPriorFidelity lambda Phi}

/-- PDF p.4: operational supremum, independently of the scalar formula. -/
def finiteBKOptimum (lambda r : ℝ) : ℝ := sSup (finiteBKValues lambda r)

/-- PDF p.4, immediately before (13): unconstrained stationary transmissivity. -/
def stationaryTau (lambda r : ℝ) : ℝ :=
  Real.exp (2 * r) / (Real.exp r + lambda * Real.cosh r) ^ 2

/-- PDF p.4: maximizing closed-region channel transmissivity. -/
def optimalTau (lambda r : ℝ) : ℝ := max (Real.tanh r) (stationaryTau lambda r)

/-- PDF p.4: maximizing channel noise. -/
def optimalNoise (lambda r : ℝ) : ℝ := Real.exp (-2 * r) * (1 + optimalTau lambda r)

/-- PDF p.4, (13): CLAIMED closed form, not the definition of an optimum. -/
def optimumClosedForm (lambda r : ℝ) : ℝ :=
  if stationaryTau lambda r ≤ Real.tanh r then
    lambda / (lambda + (1 - Real.sqrt (Real.tanh r)) ^ 2)
  else Real.exp r * (1 + lambda + Real.tanh r) /
    (2 * Real.exp r + lambda * Real.cosh r)

/-- PDF p.3, (9): denominator, used only where strictly positive. -/
def familyDenominator (r tau : ℝ) : ℝ := tau + 1 - Real.exp (2 * r) * |tau - 1|

/-- PDF p.3, (9): the lower b coefficient on the nonsingular domain. -/
def familyMinB (r tau : ℝ) : ℝ :=
  (Real.exp (2 * r) * tau + Real.exp (-2 * r) - |tau - 1|) /
    familyDenominator r tau

/-- PDF p.3, (9): a computed from b, not an independent state hypothesis. -/
def familyA (r tau b : ℝ) : ℝ := (b + Real.exp (-2 * r) * (tau - 1)) / tau

/-- PDF p.3, (9): c computed from b, with source block C=-c sigma_z. -/
def familyC (r tau b : ℝ) : ℝ := (b - Real.exp (-2 * r)) / Real.sqrt tau

/-- PDF p.3: energy within the displayed family; no global energy minimization. -/
def familyEnergy (r tau b : ℝ) : ℝ := (familyA r tau b + b - 2) / 4

/-- PDF p.3: a on the minimum-energy member of (9). -/
def familyMinA (r tau : ℝ) : ℝ := familyA r tau (familyMinB r tau)

/-- PDF p.3: c on the minimum-energy member of (9). -/
def familyMinC (r tau : ℝ) : ℝ := familyC r tau (familyMinB r tau)

/-- PDF p.3: minimum energy WITHIN family (9). -/
def familyMinEnergy (r tau : ℝ) : ℝ := familyEnergy r tau (familyMinB r tau)

/-- PDF p.3: actual pure TMSS coefficients with the source correlation sign.
The alternating sign yields C=-sinh(2r) sigma_z; r is finite. -/
def tmssCoefficient (r : ℝ) (u : ℕ × ℕ) : ℂ :=
  if u.1 = u.2 then (((-Real.tanh r) ^ u.1 / Real.cosh r : ℝ) : ℂ) else 0

/-- PDF p.3: full TMSS rank-one coefficient array; normalization is concluded. -/
def tmssKernel (r : ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun u v => tmssCoefficient r u * star (tmssCoefficient r v)

/-- PDF p.3, (7): independently defined TMSS noise at gain g and squeezing s. -/
def tmssNoise (g s : ℝ) : ℝ :=
  (1 + g ^ 2) * Real.cosh (2 * s) - 2 * g * Real.sinh (2 * s)

/-- PDF p.3, (10): minimum is defined by the noise equation, NOT its answer.
The theorem concludes a least element; no empty real-infimum default is used. -/
def minimumSqueezing (tau y : ℝ) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ tmssNoise (Real.sqrt tau) s = y}

/-- PDF p.3, (10): real arcosh written as log(x+sqrt(x^2-1)). The stated
domain ensures its argument is at least one. tau=1 uses (7) directly. -/
def squeezingClosedForm (tau y : ℝ) : ℝ :=
  if tau = 1 then Real.log (2 / y) / 2 else
    let x := (y * (1 + tau) - 2 * Real.sqrt (tau * (y ^ 2 - (1 - tau) ^ 2))) /
      (1 - tau) ^ 2
    Real.log (x + Real.sqrt (x ^ 2 - 1)) / 2

/-- PDF p.4: heterodyne POVM d^2beta |beta><beta|/pi followed by coherent
preparation |g beta>. The complex overlap retains linearity on trace class. -/
def heterodynePrepare (g : ℝ) : OscillatorChannel :=
  fun X m n => ∫ beta : ℂ,
    (inner (𝕜 := ℂ) (coherentKet beta) ((operatorOfMatrix X) (coherentKet beta)) /
      (Real.pi : ℂ)) * coherentKernel ((g : ℂ) * beta) m n

/-- PDF p.4, (16): optimized positive displacement gain for a fixed TMSS. -/
def tmssOptimalGain (lambda r : ℝ) : ℝ :=
  (2 + lambda * Real.sinh (2 * r)) / (2 + lambda + lambda * Real.cosh (2 * r))

/-- PDF p.4, (16): claimed fixed-TMSS optimum, distinct from its supremum. -/
def tmssClosedForm (lambda r : ℝ) : ℝ :=
  ((1 / Real.cosh r) ^ 2 + lambda) / (2 + lambda - 2 * Real.tanh r)

/-- PDF p.4: actual fidelities with this fixed TMSS, optimized only over g>0. -/
def tmssValues (lambda r : ℝ) : Set ℝ :=
  {f | ∃ (rho : State (ℕ × ℕ)) (g : ℝ) (Phi : OscillatorChannel),
    rho.coefficients = tmssKernel r ∧ IsBK rho g Phi ∧ f = gaussianPriorFidelity lambda Phi}

/-- PDF p.4: fixed-TMSS optimum, defined independently of (16). -/
def tmssOptimum (lambda r : ℝ) : ℝ := sSup (tmssValues lambda r)

/-! Sanity checks pin coordinate order, signs, normalization conventions,
independent optimization domains and the nonsingular vacuum case. -/

example (X : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ) :
    pairKernel X ![2, 3] ![4, 5] = X (2, 3) (4, 5) := rfl

example (g : ℝ) (z : ℂ) : bkTest g z (0, 1) = Real.sqrt 2 * g * z.re := by
  simp [bkTest]

example (g : ℝ) (z : ℂ) : bkTest g z (1, 1) = -Real.sqrt 2 * z.re := by
  simp [bkTest]

example (rho : State (ℕ × ℕ)) (g : ℝ) (Phi : OscillatorChannel)
    (h : IsBK rho g Phi) : 0 < g := h.1

example (rho : State (ℕ × ℕ)) (V : Cov 2) (h : CenteredResource rho V) :
    V.transpose = V := h.1

example (lambda : ℝ) : priorDensity lambda 0 = lambda / Real.pi := by
  simp [priorDensity]

example : phaseInsensitiveFidelityFormula 1 1 0 = 1 := by norm_num [phaseInsensitiveFidelityFormula]

example (lambda r f : ℝ) : f ∈ scalarValues lambda r ↔
    ∃ p ∈ entanglementAccessibleRegion r, phaseInsensitiveFidelityFormula lambda p.1 p.2 = f := Iff.rfl

example (lambda r : ℝ) : scalarOptimum lambda r = sSup (scalarValues lambda r) := rfl

example : familyDenominator 0 1 = 2 := by norm_num [familyDenominator]

example : familyMinB 0 1 = 1 := by norm_num [familyMinB, familyDenominator]

example : familyMinA 0 1 = 1 := by norm_num [familyMinA, familyA, familyMinB, familyDenominator]

example : familyMinC 0 1 = 0 := by norm_num [familyMinC, familyC, familyMinB, familyDenominator]

example : familyMinEnergy 0 1 = 0 := by
  norm_num [familyMinEnergy, familyEnergy, familyA, familyMinB, familyDenominator]

example : tmssKernel 0 (0, 0) (0, 0) = 1 := by
  simp [tmssKernel, tmssCoefficient]

example (g : ℝ) : tmssNoise g 0 = 1 + g ^ 2 := by simp [tmssNoise]

example (y : ℝ) : squeezingClosedForm 1 y = Real.log (2 / y) / 2 := by
  simp [squeezingClosedForm]

end QAlgorithms.Papers.Independent.Intakethird100.P89


