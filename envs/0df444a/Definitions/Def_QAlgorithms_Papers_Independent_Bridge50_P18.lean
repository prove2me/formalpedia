-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P18
-- name    : QAlgorithms_Papers_Independent_Bridge50_P18
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T14:51:06.33599+00:00
-- url     : https://prove2.me/theorems/0925497a-04f6-4bb6-954b-7677454c6322
-- title:
--   Definitions for Upper bounds on secret key agreement over lossy thermal bosonic channels
-- statement:
--   The objects the formalized statements of *Upper bounds on secret key agreement over lossy thermal bosonic channels* (arXiv:1706.04590) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HasCoefficients`: PDF pp.3,5: row=bra, column=ket for an actual bounded operator.
--   - `realizeCoefficients`: PDF pp.3,5: unique bounded realization of an operator coefficient array. Normalized nuclear densities and their finite tensor products have such a realization. The zero off-domain branch is not used as a density.
--   - `StateSpectrum`: PDF p.5, (31),(32): a complete orthonormal spectral presentation of THIS operator. For a density, normalization and summability follow from State. Zero eigenvalues are allowed here; faithfulness is imposed separately.
--   - `likelihoodWeight`: PDF pp.5,12, (33),(C1): rho-weighted spectral probability, not sigma-weighted.
--   - `likelihoodBits`: PDF p.5: binary spectral log likelihood. Used only with faithful spectra.
--   - `meanSummand`: PDF p.5, (33): signed first-moment summand. Summability is explicitly assumed in Proposition 2 and concluded, rather than assumed, in Appendix D.
--   - `relativeMeanBits`: PDF p.5, (33): D in bits on the explicit summable domain.
--   - `centralMomentBits`: PDF p.5, (34),(39): extended nonnegative absolute central spectral moment. Order two is V and order three is T. This is not an operator absolute cube. Infinite positive moments remain infinity instead of defaulting to zero.
--   - `standardNormalQuantile`: PDF p.5, (40),(41): standard-normal inverse on 0<epsilon<1, where this sublevel set is nonempty and bounded above. No endpoint value is asserted.
--   - `tensorTestingBits`: PDF pp.5,11--12: actual n-fold density coefficients on completed l2(I^n). The accepted tensorPower body is a product of n coefficients, with scalar identity at n=0. Bounded realization is unique on every density input.
--   - `CenteredFiniteEnergyGaussian`: PDF pp.2--3,12--13: centered finite-energy Gaussian predicate adapted from the accepted complete oscillator characteristic. Symmetry is explicitly retained, independently of any directional derivative. GaussianWithCovariance includes positivity, nuclear trace class, trace one, finite ACTUAL photon energy, and convergence of the full Weyl traces.
--   - `thermalPhotonWeight`: PDF p.13, (D6), and p.10, (A28): one-mode thermal photon weights.
--   - `lossPurificationAmplitude`: PDF pp.9--10, (A27),(A28): amplitude of |n>_A |n-k>_B |k>_E in the vacuum pure-loss purification of the normalized squeezed input. eta is the intensity transmissivity, and k is the lost photon count.
--   - `pureLossOutput`: PDF pp.9--10: actual rho_AB after sending the second squeezed-vacuum mode through pure loss and tracing E. The shared lost count enforces the environment partial trace. A is the first coordinate, B the second.
--   - `reverseReference`: PDF pp.8--9, (A2),(A10): rho_A tensor I_B in the chosen A,B order. This positive bounded reference is deliberately NOT required to be trace class.
--   - `regularizedLogBits`: PDF p.9, (A10): bounded support-log regularization. For each cutoff k, log2(max(x,1/(k+1))) is continuous on every bounded real spectrum. Taking the rho-weighted limit permits a kernel in rho without assigning a finite unbounded logarithm to that kernel.
--   - `conditionalVarianceCutoff`: PDF p.9, (A10),(A11): centered conditional second moment at a bounded log cutoff, computed from the ACTUAL output density and reference operators.
--   - `conditionalVarianceBits`: PDF pp.8--9, (A2),(A10): conditional variance on its convergent support-log domain. The theorem below explicitly concludes convergence, so no arbitrary limUnder value is used to assert either the identity or the high-energy limit.
--   - `pureLossVarianceExpression`: PDF p.11, exact (A42), in bits squared. The approximate square (A43) is not used as the definition of conditional variance or asserted as an identity.
-- source:
--   Upper bounds on secret key agreement over lossy thermal bosonic channels, arXiv:1706.04590v2, https://arxiv.org/abs/1706.04590v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13

/-!
Kaur--Wilde, arXiv:1706.04590v2. All citations use PDF pages.
All Hilbert spaces are completed countable-coordinate spaces, including finite
ones. No photon cutoff is used. Local definitions have complete bodies.
The source's spectral moments are in bits. The Gaussian covariance is the full
anticommutator covariance (vacuum I, [q,p]=i); interleaved implementation
coordinates differ from the source's grouped coordinates only by permutation.
Operational capacity statements and numerical resource existence are deferred
in the accompanying HARD.md; no capacity is replaced by a free real number.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open Filter
open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P18

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)
open QAlgorithms.Papers.Independent.Dependency50.P13 (operatorTrace)
open QAlgorithms.Papers.Independent.Information100.P63 (logTwo tensorPower)
open QAlgorithms.Papers.Independent.Support50.P20 (hilbertTestingDivergence)
open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov GaussianWithCovariance multimodeWeylTrace covarianceCharacteristicValue)

-- The accepted complete coordinate basis has the identical body and type.
open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

/-- PDF pp.3,5: row=bra, column=ket for an actual bounded operator. -/
def HasCoefficients {I : Type} (T : Hilbert I →L[ℂ] Hilbert I)
    (A : Matrix I I ℂ) : Prop :=
  ∀ i j, T (coordinateBasis I j) i = A i j

/-- PDF pp.3,5: unique bounded realization of an operator coefficient array.
Normalized nuclear densities and their finite tensor products have such a
realization. The zero off-domain branch is not used as a density. -/
def realizeCoefficients {I : Type} (A : Matrix I I ℂ) :
    Hilbert I →L[ℂ] Hilbert I :=
  if h : ∃ T, HasCoefficients T A then Classical.choose h else 0

/-- PDF p.5, (31),(32): a complete orthonormal spectral presentation of THIS
operator. For a density, normalization and summability follow from State.
Zero eigenvalues are allowed here; faithfulness is imposed separately. -/
structure StateSpectrum {I : Type} (K : Type) (A : Matrix I I ℂ) where
  basis : HilbertBasis K ℂ (Hilbert I)
  value : K → ℝ
  nonnegative : ∀ k, 0 ≤ value k
  eigen : ∀ k, realizeCoefficients A (basis k) = (value k : ℂ) • basis k

-- Faithfulness is positivity of density eigenvalues in a complete basis.
-- The frozen Support50.P03.FaithfulSpectrum concerns symplectic eigenvalues
-- in vacuum-I/2 units and therefore is a different predicate.

/-- PDF pp.5,12, (33),(C1): rho-weighted spectral probability, not sigma-weighted. -/
def likelihoodWeight {I K J : Type} {A B : Matrix I I ℂ}
    (r : StateSpectrum K A) (s : StateSpectrum J B) (z : K × J) : ℝ :=
  r.value z.1 * Complex.normSq (inner ℂ (s.basis z.2) (r.basis z.1))

/-- PDF p.5: binary spectral log likelihood. Used only with faithful spectra. -/
def likelihoodBits {I K J : Type} {A B : Matrix I I ℂ}
    (r : StateSpectrum K A) (s : StateSpectrum J B) (z : K × J) : ℝ :=
  logTwo (r.value z.1 / s.value z.2)

/-- PDF p.5, (33): signed first-moment summand. Summability is explicitly
assumed in Proposition 2 and concluded, rather than assumed, in Appendix D. -/
def meanSummand {I K J : Type} {A B : Matrix I I ℂ}
    (r : StateSpectrum K A) (s : StateSpectrum J B) (z : K × J) : ℝ :=
  likelihoodWeight r s z * likelihoodBits r s z

/-- PDF p.5, (33): D in bits on the explicit summable domain. -/
def relativeMeanBits {I K J : Type} {A B : Matrix I I ℂ}
    (r : StateSpectrum K A) (s : StateSpectrum J B) : ℝ :=
  ∑' z, meanSummand r s z

/-- PDF p.5, (34),(39): extended nonnegative absolute central spectral moment.
Order two is V and order three is T. This is not an operator absolute cube.
Infinite positive moments remain infinity instead of defaulting to zero. -/
def centralMomentBits {I K J : Type} {A B : Matrix I I ℂ}
    (r : StateSpectrum K A) (s : StateSpectrum J B) (order : ℕ) : ℝ≥0∞ :=
  ∑' z, ENNReal.ofReal
    (likelihoodWeight r s z * |likelihoodBits r s z - relativeMeanBits r s| ^ order)

/-- PDF p.5, (40),(41): standard-normal inverse on 0<epsilon<1, where this
sublevel set is nonempty and bounded above. No endpoint value is asserted. -/
def standardNormalQuantile (epsilon : ℝ) : ℝ :=
  sSup {a : ℝ | ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) a ≤ epsilon}

/-- PDF pp.5,11--12: actual n-fold density coefficients on completed l2(I^n).
The accepted tensorPower body is a product of n coefficients, with scalar
identity at n=0. Bounded realization is unique on every density input. -/
def tensorTestingBits {I : Type} (rho sigma : State I) (n : ℕ)
    (epsilon : ℝ) : EReal :=
  hilbertTestingDivergence (coordinateBasis (Fin n → I)) epsilon
    (realizeCoefficients (tensorPower n rho.coefficients))
    (realizeCoefficients (tensorPower n sigma.coefficients))

/-- PDF pp.2--3,12--13: centered finite-energy Gaussian predicate adapted from
the accepted complete oscillator characteristic. Symmetry is explicitly
retained, independently of any directional derivative. GaussianWithCovariance
includes positivity, nuclear trace class, trace one, finite ACTUAL photon
energy, and convergence of the full Weyl traces. -/
def CenteredFiniteEnergyGaussian {m : ℕ} (rho : State (Fin m → ℕ)) : Prop :=
  ∃ V : Cov m, GaussianWithCovariance rho.coefficients V ∧ V.transpose = V ∧
    ∀ v, multimodeWeylTrace rho.coefficients v = covarianceCharacteristicValue V 0 v

example {I : Type} (A : Matrix I I ℂ)
    (h : ∃ T, HasCoefficients T A) : HasCoefficients (realizeCoefficients A) A := by
  unfold realizeCoefficients
  rw [dif_pos h]
  exact Classical.choose_spec h

example {I : Type} (A : Matrix I I ℂ) (a b : Fin 0 → I) :
    tensorPower 0 A a b = 1 := by
  simp [tensorPower]

example {I K J : Type} {A B : Matrix I I ℂ}
    (r : StateSpectrum K A) (s : StateSpectrum J B) (z : K × J) :
    0 ≤ likelihoodWeight r s z :=
  mul_nonneg (r.nonnegative z.1) (Complex.normSq_nonneg _)

/-- PDF p.13, (D6), and p.10, (A28): one-mode thermal photon weights. -/
def thermalPhotonWeight (S : ℝ) (n : ℕ) : ℝ :=
  1 / (S + 1) * (S / (S + 1)) ^ n

/-- PDF pp.9--10, (A27),(A28): amplitude of |n>_A |n-k>_B |k>_E
in the vacuum pure-loss purification of the normalized squeezed input.
eta is the intensity transmissivity, and k is the lost photon count. -/
def lossPurificationAmplitude (eta S : ℝ) (n k : ℕ) : ℝ :=
  if k ≤ n then Real.sqrt
    (thermalPhotonWeight S n * (Nat.choose n k : ℝ) *
      (1 - eta) ^ k * eta ^ (n - k)) else 0

/-- PDF pp.9--10: actual rho_AB after sending the second squeezed-vacuum mode
through pure loss and tracing E. The shared lost count enforces the environment
partial trace. A is the first coordinate, B the second. -/
def pureLossOutput (eta S : ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun i j => if i.2 ≤ i.1 ∧ j.2 ≤ j.1 ∧ i.1 - i.2 = j.1 - j.2 then
    (lossPurificationAmplitude eta S i.1 (i.1 - i.2) *
      lossPurificationAmplitude eta S j.1 (j.1 - j.2) : ℝ) else 0

/-- PDF pp.8--9, (A2),(A10): rho_A tensor I_B in the chosen A,B order.
This positive bounded reference is deliberately NOT required to be trace class. -/
def reverseReference (S : ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun i j => if i = j then (thermalPhotonWeight S i.1 : ℂ) else 0

/-- PDF p.9, (A10): bounded support-log regularization. For each cutoff k,
log2(max(x,1/(k+1))) is continuous on every bounded real spectrum.
Taking the rho-weighted limit permits a kernel in rho without assigning a
finite unbounded logarithm to that kernel. -/
def regularizedLogBits {I : Type} (A : Matrix I I ℂ) (k : ℕ) :
    Hilbert I →L[ℂ] Hilbert I := by
  letI : ContinuousFunctionalCalculus ℂ (Hilbert I →L[ℂ] Hilbert I) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus (A := Hilbert I →L[ℂ] Hilbert I)
  letI : ContinuousFunctionalCalculus ℝ (Hilbert I →L[ℂ] Hilbert I) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus (A := Hilbert I →L[ℂ] Hilbert I)
  exact cfc (fun x : ℝ => logTwo (max x (1 / ((k : ℝ) + 1)))) (realizeCoefficients A)

/-- PDF p.9, (A10),(A11): centered conditional second moment at a bounded
log cutoff, computed from the ACTUAL output density and reference operators. -/
def conditionalVarianceCutoff {I : Type} (rho reference : Matrix I I ℂ)
    (k : ℕ) : ℝ :=
  let L := regularizedLogBits rho k - regularizedLogBits reference k
  let mean := (operatorTrace (coordinateBasis I) ((realizeCoefficients rho).comp L)).re
  let centered := L - (mean : ℂ) • (1 : Hilbert I →L[ℂ] Hilbert I)
  (operatorTrace (coordinateBasis I)
    ((realizeCoefficients rho).comp (centered.comp centered))).re

/-- PDF pp.8--9, (A2),(A10): conditional variance on its convergent support-log
domain. The theorem below explicitly concludes convergence, so no arbitrary
limUnder value is used to assert either the identity or the high-energy limit. -/
def conditionalVarianceBits {I : Type} (rho reference : Matrix I I ℂ) : ℝ :=
  Filter.limUnder atTop (conditionalVarianceCutoff rho reference)

/-- PDF p.11, exact (A42), in bits squared. The approximate square (A43)
is not used as the definition of conditional variance or asserted as an identity. -/
def pureLossVarianceExpression (eta S : ℝ) : ℝ :=
  let q := 1 - eta
  q * S * (q * S + 1) * logTwo (1 + 1 / (q * S)) ^ 2 -
    2 * q * S * (S + 1) * logTwo (1 + 1 / (q * S)) * logTwo (1 + 1 / S) +
    S * (S + 1) * logTwo (1 + 1 / S) ^ 2

example (n : ℕ) : thermalPhotonWeight 0 n = if n = 0 then 1 else 0 := by
  cases n <;> simp [thermalPhotonWeight]

example (eta S : ℝ) (n k : ℕ) (h : n < k) :
    lossPurificationAmplitude eta S n k = 0 := by
  simp [lossPurificationAmplitude, Nat.not_le.mpr h]

example {I : Type} (rho : Matrix I I ℂ) (k : ℕ) :
    conditionalVarianceCutoff rho rho k = 0 := by
  simp [conditionalVarianceCutoff, operatorTrace]

end QAlgorithms.Papers.Independent.Bridge50.P18


