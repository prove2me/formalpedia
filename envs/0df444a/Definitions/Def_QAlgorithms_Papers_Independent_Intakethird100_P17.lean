-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P17
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P17
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T07:23:35.196976+00:00
-- url     : https://prove2.me/theorems/acb119b3-7490-4c31-a80c-9e6669af8a78
-- title:
--   Definitions for Tight bounds for private communication over bosonic Gaussian channels based on teleportation simulation with optimal finite resources
-- statement:
--   The objects the formalized statements of *Tight bounds for private communication over bosonic Gaussian channels based on teleportation simulation with optimal finite resources* (arXiv:1808.00608) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `GaussianInConvention`: Appendix A, PDF p.7, (A1): rescale the pinned [q,p]=2i coordinates. Covariance here is the centered half anticommutator, and the vacuum is I/(2κ). Finite photon energy is explicit; no moment identity is a field.
--   - `quadratureKernel`: Appendix A, PDF p.7, before (A1): actual quadrature coefficients on the finite-particle core. The momentum has +i on creation and -i on annihilation.
--   - `polynomialKernelProduct`: Appendix A, PDF p.7, (A9): composition of finite-band polynomial kernels. The theorem asserts convergence of the internal sums, not a default tsum value.
--   - `PolynomialProductSummable`: Domain guard for the unbounded polynomial product on its common core.
--   - `quadraticKernel`: Appendix A, PDF p.7, (A7): coefficients of the genuine q^T A q.
--   - `densityCoefficients`: Actual Fock matrix coefficients of a bounded oscillator density.
--   - `PolynomialPairingSummable`: Absolute convergence of the density-weighted polynomial trace pairing.
--   - `polynomialExpectation`: Appendix A, PDF p.7, (A8)--(A12): actual polynomial expectation. Only the summable domain is used, and the source theorem concludes that domain.
--   - `quadraticVariance`: Appendix A, PDF p.7, (A12): variance formed from actual first/second moments.
--   - `complexCovariance`: Entrywise real-to-complex conversion of a finite covariance matrix.
--   - `StrictGibbsCovariance`: Appendix A, PDF p.7, finite Gibbs domain of (A2)--(A4). Strict uncertainty is equivalent to all symplectic eigenvalues >1/(2κ). No pure-mode log or inverse-coth endpoint is assigned a finite value.
--   - `gibbsSeriesTerm`: Appendix A, PDF p.7, (A4): analytic arcoth series in inverse powers. The strict Gibbs domain has spectral radius of the inverse <1; convergence is concluded in each theorem using this definition. No normality of sigma*iOmega is assumed, and no covariance commutativity is required.
--   - `kappaGibbsMatrix`: Appendix A, PDF p.7, (A4): G=2iOmega arcoth(2κ sigma iOmega). The result is real on the stated physical domain.
--   - `gaussianSigma`: Appendix A, PDF p.7, (A19): the covariance expression, independently of operator entropy. Strict uncertainty makes the determinant positive real.
--   - `oscillatorLogCutoff`: Appendix A, PDF pp.7--8: bounded support-log regularization in BITS. At faithful but not bounded-below densities the unbounded logarithm is obtained only through the explicitly convergent density-weighted limits below.
--   - `crossEntropyCutoff`: Appendix A, PDF p.7, (A18): independently computed regularized cross entropy.
--   - `oscillatorCrossEntropy`: The actual cross entropy on its convergent finite-log-moment domain. Each identity below also states convergence, excluding off-domain limUnder defaults.
--   - `oscillatorRelativeEntropy`: Independently defined Umegaki relative entropy, in bits, retaining +infinity. The accepted finite-projection definition is used, not the Gaussian formula.
--   - `relativeVarianceCutoff`: Appendix A, PDF p.7, (A14)--(A15): square of the ACTUAL centered operator log difference at a bounded cutoff, without assuming the density operators commute.
--   - `oscillatorRelativeVariance`: Relative entropy variance on the domain where the density-weighted squared support-log difference converges. Convergence is part of the theorem.
--   - `gaussianVarianceExpression`: Appendix A, PDF p.8, final unnumbered formula. The Omega term is positive as printed: replacing the last Omega by its transpose would reverse its sign.
-- source:
--   Tight bounds for private communication over bosonic Gaussian channels based on teleportation simulation with optimal finite resources, arXiv:1808.00608v4, https://arxiv.org/abs/1808.00608v4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17

/-!
arXiv:1808.00608v4, Appendix A, PDF pp.7--8.
Actual oscillator densities use the pinned complete Fock Weyl system. All
paper-local definitions have bodies; no entropy or moment identity is assumed.
Operational nodes and source ambiguities are recorded individually in HARD.md.
Compilation and independent moderation are pending the separate handoff.
-/

noncomputable section

open Filter
open scoped BigOperators ENNReal ComplexOrder Topology Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P17

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeOperator Quadrature PhaseVector numberKet trace TraceSummable
   FockWeylSystem GaussianMoments canonicalOmega)
open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass relativeEntropy)
open QAlgorithms.Papers.Independent.Next46.P17 (raisingCoefficient)

/-- Appendix A, PDF p.7, (A1): rescale the pinned [q,p]=2i coordinates.
Covariance here is the centered half anticommutator, and the vacuum is I/(2κ).
Finite photon energy is explicit; no moment identity is a field. -/
def GaussianInConvention {n : ℕ} (W : FockWeylSystem n) (kappa : ℝ)
    (rho : ModeOperator n) (u : PhaseVector n)
    (sigma : Matrix (Quadrature n) (Quadrature n) ℝ) : Prop :=
  GaussianMoments W rho (Real.sqrt (2 * kappa) • u) ((2 * kappa) • sigma) ∧
    Summable (fun j : Fin n → ℕ =>
      (∑ m, (j m : ℝ)) * (inner ℂ (numberKet j) (rho (numberKet j))).re)

/-- Appendix A, PDF p.7, before (A1): actual quadrature coefficients on the
finite-particle core. The momentum has +i on creation and -i on annihilation. -/
def quadratureKernel {n : ℕ} (kappa : ℝ) (a : Quadrature n)
    (i j : Fin n → ℕ) : ℂ :=
  if a.2 = 0 then
    (raisingCoefficient a.1 i j + raisingCoefficient a.1 j i) /
      (Real.sqrt (2 * kappa) : ℂ)
  else Complex.I *
    (raisingCoefficient a.1 i j - raisingCoefficient a.1 j i) /
      (Real.sqrt (2 * kappa) : ℂ)

/-- Appendix A, PDF p.7, (A9): composition of finite-band polynomial kernels.
The theorem asserts convergence of the internal sums, not a default tsum value. -/
def polynomialKernelProduct {n : ℕ}
    (A B : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) :
    Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ :=
  fun i j => ∑' k, A i k * B k j

/-- Domain guard for the unbounded polynomial product on its common core. -/
def PolynomialProductSummable {n : ℕ}
    (A B : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) : Prop :=
  ∀ i j, Summable (fun k => A i k * B k j)

/-- Appendix A, PDF p.7, (A7): coefficients of the genuine q^T A q. -/
def quadraticKernel {n : ℕ} (kappa : ℝ)
    (A : Matrix (Quadrature n) (Quadrature n) ℝ) :
    Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ :=
  fun i j => ∑ a, ∑ b, (A a b : ℂ) *
    polynomialKernelProduct (quadratureKernel kappa a) (quadratureKernel kappa b) i j

/-- Actual Fock matrix coefficients of a bounded oscillator density. -/
def densityCoefficients {n : ℕ} (rho : ModeOperator n) :
    Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ :=
  fun i j => rho (numberKet j) i

/-- Absolute convergence of the density-weighted polynomial trace pairing. -/
def PolynomialPairingSummable {n : ℕ} (rho : ModeOperator n)
    (A : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) : Prop :=
  Summable (fun z : (Fin n → ℕ) × (Fin n → ℕ) =>
    densityCoefficients rho z.1 z.2 * A z.2 z.1)

/-- Appendix A, PDF p.7, (A8)--(A12): actual polynomial expectation.
Only the summable domain is used, and the source theorem concludes that domain. -/
def polynomialExpectation {n : ℕ} (rho : ModeOperator n)
    (A : Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) : ℝ :=
  (∑' z : (Fin n → ℕ) × (Fin n → ℕ),
    densityCoefficients rho z.1 z.2 * A z.2 z.1).re

/-- Appendix A, PDF p.7, (A12): variance formed from actual first/second moments. -/
def quadraticVariance {n : ℕ} (rho : ModeOperator n) (kappa : ℝ)
    (A : Matrix (Quadrature n) (Quadrature n) ℝ) : ℝ :=
  let Q := quadraticKernel kappa A
  polynomialExpectation rho (polynomialKernelProduct Q Q) - polynomialExpectation rho Q ^ 2

/-- Entrywise real-to-complex conversion of a finite covariance matrix. -/
def complexCovariance {n : ℕ} (sigma : Matrix (Quadrature n) (Quadrature n) ℝ) :
    Matrix (Quadrature n) (Quadrature n) ℂ := fun i j => (sigma i j : ℂ)

/-- Appendix A, PDF p.7, finite Gibbs domain of (A2)--(A4).
Strict uncertainty is equivalent to all symplectic eigenvalues >1/(2κ).
No pure-mode log or inverse-coth endpoint is assigned a finite value. -/
def StrictGibbsCovariance {n : ℕ} (kappa : ℝ)
    (sigma : Matrix (Quadrature n) (Quadrature n) ℝ) : Prop :=
  sigma.transpose = sigma ∧ sigma.PosDef ∧
    ((kappa : ℂ) • complexCovariance sigma +
      (Complex.I / 2) • complexCovariance (canonicalOmega n)).PosDef

/-- Appendix A, PDF p.7, (A4): analytic arcoth series in inverse powers.
The strict Gibbs domain has spectral radius of the inverse <1; convergence is
concluded in each theorem using this definition. No normality of sigma*iOmega
is assumed, and no covariance commutativity is required. -/
def gibbsSeriesTerm {n : ℕ} (kappa : ℝ)
    (sigma : Matrix (Quadrature n) (Quadrature n) ℝ) (k : ℕ) :
    Matrix (Quadrature n) (Quadrature n) ℂ :=
  let B := ((2 * kappa : ℝ) : ℂ) •
    (complexCovariance sigma * (Complex.I • complexCovariance (canonicalOmega n)))
  (((2 * k + 1 : ℕ) : ℂ)⁻¹) • (B⁻¹) ^ (2 * k + 1)

/-- Appendix A, PDF p.7, (A4): G=2iOmega arcoth(2κ sigma iOmega).
The result is real on the stated physical domain. -/
def kappaGibbsMatrix {n : ℕ} (kappa : ℝ)
    (sigma : Matrix (Quadrature n) (Quadrature n) ℝ) :
    Matrix (Quadrature n) (Quadrature n) ℝ :=
  let G := (2 * Complex.I) •
    (complexCovariance (canonicalOmega n) * ∑' k, gibbsSeriesTerm kappa sigma k)
  fun i j => (G i j).re

/-- Appendix A, PDF p.7, (A19): the covariance expression, independently of
operator entropy. Strict uncertainty makes the determinant positive real. -/
def gaussianSigma {n : ℕ} (kappa : ℝ)
    (sigma1 sigma2 : Matrix (Quadrature n) (Quadrature n) ℝ)
    (delta : PhaseVector n) : ℝ :=
  let G := kappaGibbsMatrix kappa sigma2
  let Zsquare := ((kappa : ℂ) • complexCovariance sigma2 +
    (Complex.I / 2) • complexCovariance (canonicalOmega n)).det.re
  (Real.log Zsquare + kappa * (sigma1 * G).trace +
    kappa * ∑ i, ∑ j, delta i * G i j * delta j) / (2 * Real.log 2)

/-- Appendix A, PDF pp.7--8: bounded support-log regularization in BITS.
At faithful but not bounded-below densities the unbounded logarithm is obtained
only through the explicitly convergent density-weighted limits below. -/
def oscillatorLogCutoff {n : ℕ} (rho : ModeOperator n) (k : ℕ) : ModeOperator n := by
  letI : ContinuousFunctionalCalculus ℝ (ModeOperator n) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus (A := ModeOperator n)
  exact cfc (fun x : ℝ => Real.log (max x (1 / ((k : ℝ) + 1))) / Real.log 2) rho

/-- Appendix A, PDF p.7, (A18): independently computed regularized cross entropy. -/
def crossEntropyCutoff {n : ℕ} (rho sigma : ModeOperator n) (k : ℕ) : ℝ :=
  -(trace (rho.comp (oscillatorLogCutoff sigma k))).re

/-- The actual cross entropy on its convergent finite-log-moment domain.
Each identity below also states convergence, excluding off-domain limUnder defaults. -/
def oscillatorCrossEntropy {n : ℕ} (rho sigma : ModeOperator n) : ℝ :=
  Filter.limUnder atTop (crossEntropyCutoff rho sigma)

/-- Independently defined Umegaki relative entropy, in bits, retaining +infinity.
The accepted finite-projection definition is used, not the Gaussian formula. -/
def oscillatorRelativeEntropy {n : ℕ} (rho sigma : ModeOperator n)
    (hrho : IsTraceClass rho) (hsigma : IsTraceClass sigma) : ℝ≥0∞ :=
  relativeEntropy ⟨rho, hrho⟩ ⟨sigma, hsigma⟩ / ENNReal.ofReal (Real.log 2)

/-- Appendix A, PDF p.7, (A14)--(A15): square of the ACTUAL centered operator
log difference at a bounded cutoff, without assuming the density operators commute. -/
def relativeVarianceCutoff {n : ℕ} (rho sigma : ModeOperator n)
    (mean : ℝ) (k : ℕ) : ℝ :=
  let L := oscillatorLogCutoff rho k - oscillatorLogCutoff sigma k -
    (mean : ℂ) • (1 : ModeOperator n)
  (trace (rho.comp (L.comp L))).re

/-- Relative entropy variance on the domain where the density-weighted squared
support-log difference converges. Convergence is part of the theorem. -/
def oscillatorRelativeVariance {n : ℕ} (rho sigma : ModeOperator n) (mean : ℝ) : ℝ :=
  Filter.limUnder atTop (relativeVarianceCutoff rho sigma mean)

/-- Appendix A, PDF p.8, final unnumbered formula. The Omega term is positive
as printed: replacing the last Omega by its transpose would reverse its sign. -/
def gaussianVarianceExpression {n : ℕ} (kappa : ℝ)
    (sigma1 sigma2 : Matrix (Quadrature n) (Quadrature n) ℝ)
    (delta : PhaseVector n) : ℝ :=
  let G1 := kappaGibbsMatrix kappa sigma1
  let G2 := kappaGibbsMatrix kappa sigma2
  let D := G1 - G2
  let Omega := canonicalOmega n
  let B := (8 * kappa ^ 2) • (G2 * sigma1 * G2)
  (4 * kappa ^ 2 * (sigma1 * D * sigma1 * D).trace +
    (D * Omega * D * Omega).trace + ∑ i, ∑ j, delta i * B i j * delta j) /
    (2 * (2 * Real.log 2) ^ 2)

example {n : ℕ} (m : Fin n) (j : Fin n → ℕ) :
    raisingCoefficient m (Function.update j m (j m + 1)) j =
      (Real.sqrt ((j m : ℝ) + 1) : ℂ) := by
  simp [raisingCoefficient]

example {n : ℕ} (kappa : ℝ) (m : Fin n) (i j : Fin n → ℕ) :
    quadratureKernel kappa (m, 1) i j = Complex.I *
      (raisingCoefficient m i j - raisingCoefficient m j i) /
      (Real.sqrt (2 * kappa) : ℂ) := by
  simp [quadratureKernel]

example {n : ℕ} (rho : ModeOperator n) (k : ℕ) :
    relativeVarianceCutoff rho rho 0 k = 0 := by
  simp [relativeVarianceCutoff, trace,
    QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace]

example {n : ℕ} (kappa : ℝ) (sigma : Matrix (Quadrature n) (Quadrature n) ℝ) :
    gaussianVarianceExpression kappa sigma sigma 0 = 0 := by
  simp [gaussianVarianceExpression]

end QAlgorithms.Papers.Independent.Intakethird100.P17


