-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P01
-- name    : QAlgorithms_Papers_Independent_Advance50_P01
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T14:57:54.800496+00:00
-- url     : https://prove2.me/theorems/8264661f-11d1-4715-b1a0-7c6878e0b2f7
-- title:
--   Definitions for Second-order asymptotics for quantum hypothesis testing
-- statement:
--   The objects the formalized statements of *Second-order asymptotics for quantum hypothesis testing* (arXiv:1208.1400) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `relativeEntropyNats`: Relative entropy in nats (source p. 3), obtained by converting the accepted finite Umegaki expression in bits. On PSD, support-included pairs this equals Tr[rho(log rho-log sigma)]; the accepted formula assigns x log x = 0 at x = 0.
--   - `relativeVarianceNats`: Quantum relative variance in nats squared, source p. 3, equation (1). The accepted centered operator-square variance is in bits squared, so its conversion factor is (ln 2)^2. For normalized, support-included states this is precisely Tr[rho(log rho-log sigma)^2] - D(rho||sigma)^2, including singular rho and V = 0.
--   - `iidMatrix`: Tensor power in the product basis (source pp. 4, 7). The zeroth tensor power is the scalar identity on the singleton empty-product index.
--   - `IIDTest`: All binary POVMs on n copies (source p. 4), represented by their rho-accepting effect. This indexed effect subtype differs from accepted Dependency50.P32.Test, a predicate on a channel, a pure input and an effect with an error-tolerance constraint. `IsEffect` requires both A and I-A positive semidefinite.
--   - `iidTypeI`: Type-I error on a bundled iid effect (source p. 4). This only adapts the accepted raw-matrix type-I primitive to the local effect subtype.
--   - `typeII`: Type-II error Tr[sigma^n A] (source p. 4), without a prior or factor 1/2.
--   - `constrainedTypeI`: Definition 1, source p. 5: minimum type-I error under the exponential type-II constraint. This iid state optimum differs from accepted Bridge50.P43.optimalAlpha, which optimizes adaptive channel strategies at a first-order rate in bits. On the density-matrix domain the set contains the zero effect, is contained in [0,1], and has a minimum by finite-dimensional compactness; hence its real infimum is that minimum.
--   - `iidOptimalBeta`: Iid adapter to the accepted unrestricted testing optimum (source p. 14). For normalized rho, its condition 1-epsilon <= Tr[A rho^n] is equivalent to Tr[rho^n(I-A)] <= epsilon. The optimum is unnormalized, with no prior factor.
--   - `iidTestingDivergenceNats`: Iid testing divergence in nats, source pp. 3, 14–17. Convert the accepted extended testing divergence in bits by the positive factor ln 2; zero optimal beta remains +infinity. No division by 1-epsilon is introduced.
--   - `normalQuantileReal`: Real normal quantile on the interior (0,1), source pp. 3, 15. The defining set is nonempty and bounded below on that domain. The value outside the interior is explicitly set to zero and is never used as an endpoint quantile.
--   - `extendedNormalQuantile`: Extended normal quantile: -infinity at 0 and +infinity at 1. This preserves the weak endpoint conditions in Theorem 5 (source p. 15). The same constants are used outside [0,1], where no theorem invokes this definition.
--   - `SpectralDecomposition`: A complete spectral presentation of a density matrix (source p. 7). This is a genuine orthonormal eigenbasis and reconstruction, allowing degeneracies and zeros.
--   - `spectralLaw`: The rho-weighted joint law lambda(x)|<b_y|a_x>|^2, source p. 7. The inner product is conjugate-linear in its first argument.
--   - `spectralLogRatio`: Classical log likelihood on a spectral outcome (source pp. 7–8). The explicit zero extension has weight zero under spectralLaw when supports are nested. The sigma-kernel extension implements the p. 5 compression to supp(sigma).
--   - `spectralLogMean`: Expectation of the log likelihood under the specific spectral law (source p. 8, Lemma 3). Accepted Gap20.P15.spectralMean is instead a nonnegative extended energy expectation on a trace-class state; it cannot replace this signed, finite log-likelihood mean.
--   - `spectralVariance`: Classical variance centered at its own mean, not at an assumed quantum identity (source p. 8, Lemma 3).
--   - `spectralThirdMoment`: T^3 in Theorem 5: the absolute third central moment of the classical spectral law (source pp. 14–15), centered at the constructed quantum D.
--   - `finiteLawMean`: Mean of an explicitly weighted finite real law, auxiliary to the Berry–Esseen contract. Accepted Frontier18.P10.finiteMean takes a normalized FiniteEnsemble on a topological vector space; this raw-law helper is defined before imposing probability hypotheses (source p. 14).
--   - `finiteVariance`: Central second moment of a finite real probability law (source p. 14).
--   - `finiteThirdMoment`: Absolute third central moment of a finite real probability law (source p. 14).
--   - `finiteStandardizedCDF`: CDF of the standardized iid sum, written as a finite product-law sum (source p. 14). Only n>=1, normalized p, and positive finiteVariance are used in the BE contract.
--   - `IsBerryEsseenConstant`: A valid universal Berry–Esseen constant for all finite real laws (source p. 14, (43)). The constant is fixed before the alphabet, law, sample size, and threshold. This is an actual BE validity predicate; membership in the numerical interval alone is insufficient. Finite laws cover all spectral laws in this finite-dimensional paper.
--   - `secondOrderCenter`: The two leading iid terms, with the source's plus sign (source pp. 3, 15).
--   - `beCorrection`: Berry–Esseen correction CT^3/(sqrt(n)(sqrt(V))^3), source p. 15.
--   - `finiteLower`: Lower bounding expression in Theorem 5, with its extended endpoint quantile (p. 15).
--   - `finiteUpper`: Upper bounding expression in Theorem 5, including log(2^9 n^2), source pp. 15–16.
--   - `rankOneApply`: Rank-one operator |phi><phi| applied to v (source p. 8, Lemma 4).
-- source:
--   Second-order asymptotics for quantum hypothesis testing, arXiv:1208.1400v3, https://arxiv.org/abs/1208.1400v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71

/-!
# Ke Li: second-order asymptotics for quantum hypothesis testing

Source: arXiv:1208.1400v3, PDF pp. 3–18 (printed pages agree).
Natural logarithms, unnormalized conditional testing errors, and all binary POVMs.
Pinned accepted definitions are imported unchanged; the new adapters below are local
to this paper. Unit conversions are explicit: entropy in nats, variance in nats squared.
The Gaussian assertions exclude the singular point V = 0, discussed on source p. 17;
the iid expansion and exact tradeoff include it.
-/

noncomputable section

open Filter
open scoped Topology

namespace QAlgorithms.Papers.Independent.Advance50.P01

-- These are pinned accepted modules from the supplied library catalogue.
open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)
open QAlgorithms.Papers.Independent.Information100.P63 (normalCDF normalQuantile tensorPower)
open QAlgorithms.Papers.Independent.Information100.P58 (testingBeta testingD)
open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropyFinite)

attribute [local instance] Classical.propDecidable

-- Match the universe-zero matrix indices of the pinned accepted interfaces.
variable {I : Type} [Fintype I] [DecidableEq I]

-- SupportIncluded is opened directly from the accepted Information100.P71 module.

/-- Relative entropy in nats (source p. 3), obtained by converting the accepted
finite Umegaki expression in bits. On PSD, support-included pairs this equals
Tr[rho(log rho-log sigma)]; the accepted formula assigns x log x = 0 at x = 0. -/
def relativeEntropyNats (rho sigma : Matrix I I ℂ) : ℝ :=
  Real.log 2 * relativeEntropyFinite rho sigma

/-- Quantum relative variance in nats squared, source p. 3, equation (1).
The accepted centered operator-square variance is in bits squared, so its conversion
factor is (ln 2)^2. For normalized, support-included states this is precisely
Tr[rho(log rho-log sigma)^2] - D(rho||sigma)^2, including singular rho and V = 0. -/
def relativeVarianceNats (rho sigma : Matrix I I ℂ) : ℝ :=
  (Real.log 2) ^ 2 *
    QAlgorithms.Papers.Independent.Bridge50.P01.relativeVariance rho sigma

/-- Tensor power in the product basis (source pp. 4, 7).
The zeroth tensor power is the scalar identity on the singleton empty-product index. -/
def iidMatrix (M : Matrix I I ℂ) (n : ℕ) :
    Matrix (Fin n → I) (Fin n → I) ℂ :=
  tensorPower n M

/-- All binary POVMs on n copies (source p. 4), represented by their rho-accepting effect.
This indexed effect subtype differs from accepted Dependency50.P32.Test, a predicate
on a channel, a pure input and an effect with an error-tolerance constraint.
`IsEffect` requires both A and I-A positive semidefinite. -/
abbrev IIDTest (I : Type) [Fintype I] [DecidableEq I] (n : ℕ) :=
  {A : Matrix (Fin n → I) (Fin n → I) ℂ // IsEffect A}

/-- Type-I error on a bundled iid effect (source p. 4).
This only adapts the accepted raw-matrix type-I primitive to the local effect subtype. -/
def iidTypeI (rho : Matrix I I ℂ) {n : ℕ} (A : IIDTest I n) : ℝ :=
  QAlgorithms.Papers.Independent.Dependency50.P28.typeI rho n A.val

/-- Type-II error Tr[sigma^n A] (source p. 4), without a prior or factor 1/2. -/
def typeII (sigma : Matrix I I ℂ) {n : ℕ} (A : IIDTest I n) : ℝ :=
  (iidMatrix sigma n * A.val).trace.re

/-- Definition 1, source p. 5: minimum type-I error under the exponential type-II constraint.
This iid state optimum differs from accepted Bridge50.P43.optimalAlpha, which optimizes
adaptive channel strategies at a first-order rate in bits.
On the density-matrix domain the set contains the zero effect, is contained in [0,1],
and has a minimum by finite-dimensional compactness; hence its real infimum is that minimum. -/
def constrainedTypeI (rho sigma : Matrix I I ℂ) (E1 E2 : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  sInf {a : ℝ | ∃ A : IIDTest I n, a = iidTypeI rho A ∧
    typeII sigma A ≤ Real.exp (-(E1 * n + E2 * Real.sqrt n + f n))}

/-- Iid adapter to the accepted unrestricted testing optimum (source p. 14).
For normalized rho, its condition 1-epsilon <= Tr[A rho^n] is equivalent to
Tr[rho^n(I-A)] <= epsilon. The optimum is unnormalized, with no prior factor. -/
def iidOptimalBeta (rho sigma : Matrix I I ℂ) (n : ℕ) (epsilon : ℝ) : ℝ :=
  testingBeta epsilon (iidMatrix rho n) (iidMatrix sigma n)

/-- Iid testing divergence in nats, source pp. 3, 14–17.
Convert the accepted extended testing divergence in bits by the positive factor ln 2;
zero optimal beta remains +infinity. No division by 1-epsilon is introduced. -/
def iidTestingDivergenceNats (rho sigma : Matrix I I ℂ) (n : ℕ) (epsilon : ℝ) : EReal :=
  ((Real.log 2 : ℝ) : EReal) * testingD epsilon (iidMatrix rho n) (iidMatrix sigma n)

-- normalCDF and the interior normalQuantile are opened from accepted Information100.P63.

/-- Real normal quantile on the interior (0,1), source pp. 3, 15.
The defining set is nonempty and bounded below on that domain. The value outside the
interior is explicitly set to zero and is never used as an endpoint quantile. -/
def normalQuantileReal (p : ℝ) : ℝ :=
  if 0 < p ∧ p < 1 then normalQuantile p else 0

/-- Extended normal quantile: -infinity at 0 and +infinity at 1.
This preserves the weak endpoint conditions in Theorem 5 (source p. 15).
The same constants are used outside [0,1], where no theorem invokes this definition. -/
def extendedNormalQuantile (p : ℝ) : EReal :=
  if p ≤ 0 then ⊥ else if 1 ≤ p then ⊤ else (normalQuantileReal p : EReal)

/-- A complete spectral presentation of a density matrix (source p. 7).
This is a genuine orthonormal eigenbasis and reconstruction, allowing degeneracies and zeros. -/
structure SpectralDecomposition (M : Matrix I I ℂ) where
  basis : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)
  values : I → ℝ
  nonneg : ∀ x, 0 ≤ values x
  normalized : ∑ x, values x = 1
  reconstruct : M = ∑ x, (values x : ℂ) • pureDensity (basis x)

/-- The rho-weighted joint law lambda(x)|<b_y|a_x>|^2, source p. 7.
The inner product is conjugate-linear in its first argument. -/
def spectralLaw {rho sigma : Matrix I I ℂ}
    (r : SpectralDecomposition rho) (s : SpectralDecomposition sigma) (x y : I) : ℝ :=
  r.values x * ‖inner ℂ (s.basis y) (r.basis x)‖ ^ 2

/-- Classical log likelihood on a spectral outcome (source pp. 7–8).
The explicit zero extension has weight zero under spectralLaw when supports are nested.
The sigma-kernel extension implements the p. 5 compression to supp(sigma). -/
def spectralLogRatio {rho sigma : Matrix I I ℂ}
    (r : SpectralDecomposition rho) (s : SpectralDecomposition sigma) (x y : I) : ℝ :=
  if r.values x = 0 ∨ s.values y = 0 then 0 else Real.log (r.values x / s.values y)

/-- Expectation of the log likelihood under the specific spectral law (source p. 8, Lemma 3).
Accepted Gap20.P15.spectralMean is instead a nonnegative extended energy expectation
on a trace-class state; it cannot replace this signed, finite log-likelihood mean. -/
def spectralLogMean {rho sigma : Matrix I I ℂ}
    (r : SpectralDecomposition rho) (s : SpectralDecomposition sigma) : ℝ :=
  ∑ x, ∑ y, spectralLaw r s x y * spectralLogRatio r s x y

/-- Classical variance centered at its own mean, not at an assumed quantum identity
(source p. 8, Lemma 3). -/
def spectralVariance {rho sigma : Matrix I I ℂ}
    (r : SpectralDecomposition rho) (s : SpectralDecomposition sigma) : ℝ :=
  ∑ x, ∑ y, spectralLaw r s x y * (spectralLogRatio r s x y - spectralLogMean r s) ^ 2

/-- T^3 in Theorem 5: the absolute third central moment of the classical spectral law
(source pp. 14–15), centered at the constructed quantum D. -/
def spectralThirdMoment {rho sigma : Matrix I I ℂ}
    (r : SpectralDecomposition rho) (s : SpectralDecomposition sigma) : ℝ :=
  ∑ x, ∑ y, spectralLaw r s x y *
    |spectralLogRatio r s x y - relativeEntropyNats rho sigma| ^ 3

/-- Mean of an explicitly weighted finite real law, auxiliary to the Berry–Esseen contract.
Accepted Frontier18.P10.finiteMean takes a normalized FiniteEnsemble on a topological
vector space; this raw-law helper is defined before imposing probability hypotheses
(source p. 14). -/
def finiteLawMean {d : ℕ} (p z : Fin d → ℝ) : ℝ := ∑ i, p i * z i

/-- Central second moment of a finite real probability law (source p. 14). -/
def finiteVariance {d : ℕ} (p z : Fin d → ℝ) : ℝ :=
  ∑ i, p i * (z i - finiteLawMean p z) ^ 2

/-- Absolute third central moment of a finite real probability law (source p. 14). -/
def finiteThirdMoment {d : ℕ} (p z : Fin d → ℝ) : ℝ :=
  ∑ i, p i * |z i - finiteLawMean p z| ^ 3

/-- CDF of the standardized iid sum, written as a finite product-law sum (source p. 14).
Only n>=1, normalized p, and positive finiteVariance are used in the BE contract. -/
def finiteStandardizedCDF {d : ℕ} (p z : Fin d → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∑ x : Fin n → Fin d,
    if ((∑ j, z (x j)) - n * finiteLawMean p z) /
        (Real.sqrt n * Real.sqrt (finiteVariance p z)) ≤ t
    then ∏ j, p (x j) else 0

/-- A valid universal Berry–Esseen constant for all finite real laws (source p. 14, (43)).
The constant is fixed before the alphabet, law, sample size, and threshold. This is an
actual BE validity predicate; membership in the numerical interval alone is insufficient.
Finite laws cover all spectral laws in this finite-dimensional paper. -/
def IsBerryEsseenConstant (C : ℝ) : Prop :=
  0 < C ∧ ∀ (d : ℕ) (p z : Fin d → ℝ), (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
    0 < finiteVariance p z → ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ,
      |finiteStandardizedCDF p z n t - normalCDF t| ≤
        C * finiteThirdMoment p z / (Real.sqrt n * Real.sqrt (finiteVariance p z) ^ 3)

/-- The two leading iid terms, with the source's plus sign (source pp. 3, 15). -/
def secondOrderCenter (rho sigma : Matrix I I ℂ) (epsilon : ℝ) (n : ℕ) : ℝ :=
  n * relativeEntropyNats rho sigma +
    Real.sqrt n * Real.sqrt (relativeVarianceNats rho sigma) * normalQuantileReal epsilon

/-- Berry–Esseen correction CT^3/(sqrt(n)(sqrt(V))^3), source p. 15. -/
def beCorrection (C V T3 : ℝ) (n : ℕ) : ℝ :=
  C * T3 / (Real.sqrt n * Real.sqrt V ^ 3)

/-- Lower bounding expression in Theorem 5, with its extended endpoint quantile (p. 15). -/
def finiteLower (rho sigma : Matrix I I ℂ) (epsilon C T3 : ℝ) (n : ℕ) : EReal :=
  ((n * relativeEntropyNats rho sigma : ℝ) : EReal) +
    ((Real.sqrt n * Real.sqrt (relativeVarianceNats rho sigma) : ℝ) : EReal) *
      extendedNormalQuantile (epsilon - beCorrection C (relativeVarianceNats rho sigma) T3 n)

/-- Upper bounding expression in Theorem 5, including log(2^9 n^2), source pp. 15–16. -/
def finiteUpper (rho sigma : Matrix I I ℂ) (epsilon C T3 : ℝ) (n : ℕ) : EReal :=
  ((n * relativeEntropyNats rho sigma : ℝ) : EReal) +
    ((Real.sqrt n * Real.sqrt (relativeVarianceNats rho sigma) : ℝ) : EReal) *
      extendedNormalQuantile (epsilon + beCorrection C (relativeVarianceNats rho sigma) T3 n +
        2 / Real.sqrt n) + ((Real.log ((2 : ℝ) ^ 9 * (n : ℝ) ^ 2) : ℝ) : EReal)

/-- Rank-one operator |phi><phi| applied to v (source p. 8, Lemma 4). -/
def rankOneApply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (phi v : E) : E := (inner ℂ phi v) • phi

/-! Sanity examples pin the tensor, logarithm, endpoint, error, and normalization conventions.
These are definition checks, not proofs of any source theorem. -/

example (rho : Matrix I I ℂ) : SupportIncluded rho rho := le_rfl

example (rho sigma : Matrix I I ℂ) :
    relativeEntropyNats rho sigma = Real.log 2 * relativeEntropyFinite rho sigma := rfl

example (rho sigma : Matrix I I ℂ) :
    relativeVarianceNats rho sigma = (Real.log 2) ^ 2 *
      QAlgorithms.Papers.Independent.Bridge50.P01.relativeVariance rho sigma := rfl

example (M : Matrix I I ℂ) (x y : Fin 0 → I) : iidMatrix M 0 x y = 1 := by
  simp [iidMatrix, tensorPower]

example (M : Matrix I I ℂ) (x y : Fin 1 → I) : iidMatrix M 1 x y = M (x 0) (y 0) := by
  simp [iidMatrix, tensorPower]

example (rho : Matrix I I ℂ) (n : ℕ) (h : IsEffect (0 : Matrix (Fin n → I) (Fin n → I) ℂ)) :
    typeII rho (⟨0, h⟩ : IIDTest I n) = 0 := by
  simp [typeII]

example (rho : Matrix I I ℂ) (n : ℕ) (h : IsEffect (1 : Matrix (Fin n → I) (Fin n → I) ℂ)) :
    iidTypeI rho (⟨1, h⟩ : IIDTest I n) = 0 := by
  simp [iidTypeI, QAlgorithms.Papers.Independent.Dependency50.P28.typeI,
    QAlgorithms.Papers.Independent.Dependency50.P28.tr]

example : extendedNormalQuantile 0 = ⊥ ∧ extendedNormalQuantile 1 = ⊤ := by
  norm_num [extendedNormalQuantile]

example {rho sigma : Matrix I I ℂ} (r : SpectralDecomposition rho)
    (s : SpectralDecomposition sigma) (x y : I) (h : r.values x = 0) :
    spectralLaw r s x y = 0 ∧ spectralLogRatio r s x y = 0 := by
  simp [spectralLaw, spectralLogRatio, h]

example (C V : ℝ) (n : ℕ) : beCorrection C V 0 n = 0 := by
  simp [beCorrection]

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (phi : E) :
    rankOneApply phi (0 : E) = 0 := by
  simp [rankOneApply]

end QAlgorithms.Papers.Independent.Advance50.P01


