-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
-- name    : QAlgorithms_Papers_Independent_Claimed50_P47
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T11:32:39.582145+00:00
-- url     : https://prove2.me/theorems/47dca330-bc0b-49e7-85b6-d37c0bc755f2
-- title:
--   Definitions for Gaussian quantum channels
-- statement:
--   The objects the formalized statements of *Gaussian quantum channels* (arXiv:quant-ph/0505151) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Occupation`: PDF p.3: occupation labels for finitely many complete oscillator modes.
--   - `Quadratures`: PDF p.3: a permutation to grouped position/momentum coordinates.
--   - `phaseRelabel`: Basis relabeling of the accepted canonical coordinates; no rescaling.
--   - `canonicalForm`: PDF p.3, (2): the accepted symplectic form in arbitrary finite mode labels.
--   - `thermalDiagonal`: PDF p.7: the accepted Williamson diagonal in the same relabeled coordinates.
--   - `quadraticForm`: PDF p.3: the quadratic form, with both sums over all quadratures.
--   - `characteristicMean`: PDF p.3, (3)--(4): xi^T sigma d, including its sign.
--   - `characteristicVariance`: PDF p.3: covariance expressed in the source's Weyl arguments.
--   - `gaussianStateCharacteristic`: PDF p.3, corrected (4): the actual Gaussian characteristic function; the linear term is imaginary and pure covariances are allowed. This scalar state characteristic differs from Frontier30.P10.gaussianCharacteristic, which is an operator-valued Gaussian observable characteristic (arXiv:0802.0235, PDF p.8, (22)); the latter cannot replace this state function.
--   - `weylArgument`: PDF p.3, W_xi=exp(i xi^T sigma R): D(z) has z=-(xi_x+i xi_p)/sqrt(2).
--   - `weylKernel`: PDF p.3, (2)--(3): finite tensor product of the accepted full Fock Weyl kernels.
--   - `singleCharacteristic`: PDF p.3, (3): bounded Weyl/trace-class pairing, product first and trace second. Only trace-class arguments occur below. The iterated sums are not reordered.
--   - `firstQuadratures`: Inclusion of one party's quadratures into the total quadratures.
--   - `secondQuadratures`: Inclusion of the second party's quadratures, retaining its own local order.
--   - `bipartiteWeyl`: PDF p.8: the actual tensor-product Weyl kernel on the displayed A|B cut.
--   - `bipartiteCharacteristic`: PDF pp.3,8: characteristic function on the full bipartite oscillator space.
--   - `bipartitePhotonEnergy`: PDF pp.3,7: finite oscillator energy is equivalent to finite mean total occupation for finitely many modes; the additive zero-point energy is irrelevant to finiteness. Divergence remains infinity.
--   - `HasBipartiteMoments`: PDF pp.3,7--8: finite first/second moments, in the equivalent Weyl-derivative form. Energy finiteness enforces the quadratic-form domain; all real directions are tested, fixing the full mean and covariance rather than energy alone.
--   - `HasBipartiteGaussianCharacteristic`: PDF pp.7--8: Gaussian counterpart with its specified moments, on actual densities.
--   - `covarianceAction`: PDF p.16, (53): X gamma X^T+Y, as opposed to (8)'s transposed X convention.
--   - `weylPullback`: PDF pp.3--4: the contravariant Weyl argument belonging to a quadrature map X.
--   - `IsGaussianChannel`: PDF pp.2--4,16: a full trace-class CPTP Gaussian channel, allowing affine first-moment displacements omitted from the covariance formulas. Its normal unital CP dual is determined by the all-state Weyl pairing. The noise factor /4 matches the covariance normalization and corrects printed (6).
--   - `splitQuadratures`: Regroup positions and momenta by subsystem, without changing any physical mode.
--   - `jointInputCovariance`: PDF p.16: tensor-product covariance, in the common grouped coordinate convention.
--   - `firstCovariance`: PDF pp.7,16: principal covariance corresponding to subsystem A.
--   - `IsBipartiteGaussianUnitary`: PDF pp.3--4,16: an actual bounded metaplectic implementation on the completed bipartite oscillator space, expressed through all Weyl operators. Affine shifts are retained even though they do not appear in the covariance transformation.
--   - `PureGaussianDilation`: PDF p.16, (53): the full pure environmental dilation. The same environment, unitary, and symplectic matrix serve every input. Purity concerns the actual trace-class density, as well as its covariance. Zero environmental modes are allowed.
--   - `dilatedCovariance`: PDF p.16: gamma prime in (53), using the same fixed dilation.
--   - `gaussianEntropy`: PDF p.7, (20): entropy of rho_gamma through all Williamson diagonalizations. On physical covariances these have the same finite entropy. An empty set yields infinity, never a default real zero. No density-operator full-rank assumption occurs.
--   - `CovarianceBelow`: PDF p.15, (48): semidefinite covariance order, not entrywise matrix order.
--   - `gaussianEoF`: PDF p.15, second line of (48): Gaussian EoF across A|B. This covariance variational formula allows pure boundary points; it is not a definition through channel capacity or through minimum output entropy. The unrestricted Gaussian ensemble law in the original definition is not assumed Gaussian.
--   - `gaussianOutputEntropy`: PDF p.16, (56): Gaussian output entropy, independently of EoF.
--   - `gaussianMinimumOutputEntropy`: PDF pp.14,16, (46),(57), alpha=1: all Gaussian inputs, with no energy constraint or density full-rank restriction. First moments do not affect entropy.
--   - `regroupPairs`: Regroup two pairs so that all A modes precede all B modes.
--   - `pairedDirectSum`: PDF p.16, (I): direct sum regrouped as A1 A2 | B1 B2.
--   - `GaussianEoFAdditive`: PDF pp.16--17: additivity is a global property, at every finite positive mode count and on every physical bipartite covariance. Either party may have zero modes, but an entire paired subsystem has positive total mode count.
--   - `GaussianEoFCovarianceConvex`: PDF pp.15--17, (50),(IV): global convexity of covariance arguments. These arithmetic mixtures are not density-operator mixtures.
--   - `pairedInclusion`: Inclusion of one paired subsystem on both parties; correlations are retained in the total covariance and only the selected principal submatrix is extracted.
--   - `GaussianEoFSuperadditive`: PDF p.16, (58), footnote 19: all finite families of arbitrary local mode counts. The total covariance need not be a direct sum. The global positive mode convention is expressed by positive family size and positive paired mode counts.
-- source:
--   Gaussian quantum channels, arXiv:quant-ph/0505151v1, https://arxiv.org/abs/quant-ph/0505151v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49

/-!
Eisert--Wolf, arXiv:quant-ph/0505151v1. Full oscillator states have occupation
labels I -> Nat, with no cutoff. Coordinates below are grouped (all x, all p),
a permutation of the interleaved coordinates on PDF p.3. Covariance is doubled,
vacuum I, hbar=1. Entropies are in nats. The covariance entropy uses the source's
Williamson formula (20); Gaussian EoF uses the second, noncircular line of (48).
Neither function is defined by any of the identities asserted below.

Source corrections in these adapters: (4) requires i in its linear term;
the Weyl multiplier compatible with (3),(8) and vacuum covariance I has /4,
rather than the /2 printed in (6). Section 5.4 uses X gamma X^T, so the CP
matrix imported from P10 receives X.transpose. See MODERATION_NOTES.md.
These corrections require independent moderation. Compilation is pending.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P47

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P10
  (Phase sigma physicalCovariance pureCovariance thermalCovariance cpMatrix)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (PureDensity partialRight boundedUnitaryConjugation dilationReceiver)
open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- PDF p.3: occupation labels for finitely many complete oscillator modes. -/
abbrev Occupation (I : Type) := I → ℕ

/-- PDF p.3: a permutation to grouped position/momentum coordinates. -/
abbrev Quadratures (I : Type) := I ⊕ I

/-- Basis relabeling of the accepted canonical coordinates; no rescaling. -/
def phaseRelabel (I : Type) [Fintype I] : Quadratures I ≃ Phase (Fintype.card I) :=
  Equiv.sumCongr (Fintype.equivFin I) (Fintype.equivFin I)

/-- PDF p.3, (2): the accepted symplectic form in arbitrary finite mode labels. -/
def canonicalForm (I : Type) [Fintype I] : Matrix (Quadratures I) (Quadratures I) ℝ :=
  (sigma (Fintype.card I)).submatrix (phaseRelabel I) (phaseRelabel I)

/-- PDF p.7: the accepted Williamson diagonal in the same relabeled coordinates. -/
def thermalDiagonal {I : Type} [Fintype I] (c : I → ℝ) :
    Matrix (Quadratures I) (Quadratures I) ℝ :=
  (thermalCovariance (fun j => c ((Fintype.equivFin I).symm j))).submatrix
    (phaseRelabel I) (phaseRelabel I)

/-- PDF p.3: the quadratic form, with both sums over all quadratures. -/
def quadraticForm {I : Type} [Fintype I]
    (gamma : Matrix (Quadratures I) (Quadratures I) ℝ) (xi : Quadratures I → ℝ) : ℝ :=
  ∑ i, ∑ j, xi i * gamma i j * xi j

/-- PDF p.3, (3)--(4): xi^T sigma d, including its sign. -/
def characteristicMean {I : Type} [Fintype I]
    (d xi : Quadratures I → ℝ) : ℝ :=
  ∑ i, xi i * (∑ j, canonicalForm I i j * d j)

/-- PDF p.3: covariance expressed in the source's Weyl arguments. -/
def characteristicVariance {I : Type} [Fintype I]
    (gamma : Matrix (Quadratures I) (Quadratures I) ℝ) (xi : Quadratures I → ℝ) : ℝ :=
  quadraticForm ((canonicalForm I).transpose * gamma * canonicalForm I) xi

/-- PDF p.3, corrected (4): the actual Gaussian characteristic function;
the linear term is imaginary and pure covariances are allowed.
This scalar state characteristic differs from Frontier30.P10.gaussianCharacteristic,
which is an operator-valued Gaussian observable characteristic (arXiv:0802.0235,
PDF p.8, (22)); the latter cannot replace this state function. -/
def gaussianStateCharacteristic {I : Type} [Fintype I]
    (d : Quadratures I → ℝ) (gamma : Matrix (Quadratures I) (Quadratures I) ℝ)
    (xi : Quadratures I → ℝ) : ℂ :=
  Complex.exp (((-characteristicVariance gamma xi / 4 : ℝ) : ℂ) +
    Complex.I * (characteristicMean d xi : ℂ))

/-- PDF p.3, W_xi=exp(i xi^T sigma R): D(z) has z=-(xi_x+i xi_p)/sqrt(2). -/
def weylArgument {I : Type} (xi : Quadratures I → ℝ) (i : I) : ℂ :=
  -((xi (Sum.inl i) : ℂ) + Complex.I * (xi (Sum.inr i) : ℂ)) / (Real.sqrt 2 : ℂ)

/-- PDF p.3, (2)--(3): finite tensor product of the accepted full Fock Weyl kernels. -/
def weylKernel {I : Type} [Fintype I] (xi : Quadratures I → ℝ) :
    Matrix (Occupation I) (Occupation I) ℂ :=
  fun u v => ∏ i, displacementMatrix (weylArgument xi i) (u i) (v i)

/-- PDF p.3, (3): bounded Weyl/trace-class pairing, product first and trace second.
Only trace-class arguments occur below. The iterated sums are not reordered. -/
def singleCharacteristic {I : Type} [Fintype I]
    (rho : Matrix (Occupation I) (Occupation I) ℂ) (xi : Quadratures I → ℝ) : ℂ :=
  ∑' u, ∑' v, rho u v * weylKernel xi v u

/-- Inclusion of one party's quadratures into the total quadratures. -/
def firstQuadratures {A B : Type} : Quadratures A → Quadratures (A ⊕ B) :=
  Sum.map Sum.inl Sum.inl

/-- Inclusion of the second party's quadratures, retaining its own local order. -/
def secondQuadratures {A B : Type} : Quadratures B → Quadratures (A ⊕ B) :=
  Sum.map Sum.inr Sum.inr

/-- PDF p.8: the actual tensor-product Weyl kernel on the displayed A|B cut. -/
def bipartiteWeyl {A B : Type} [Fintype A] [Fintype B]
    (xi : Quadratures (A ⊕ B) → ℝ) :
    Matrix (Occupation A × Occupation B) (Occupation A × Occupation B) ℂ :=
  productCoeff (weylKernel (xi ∘ firstQuadratures))
    (weylKernel (xi ∘ secondQuadratures))

/-- PDF pp.3,8: characteristic function on the full bipartite oscillator space. -/
def bipartiteCharacteristic {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (Occupation A × Occupation B) (Occupation A × Occupation B) ℂ)
    (xi : Quadratures (A ⊕ B) → ℝ) : ℂ :=
  ∑' u, ∑' v, rho u v * bipartiteWeyl xi v u

/-- PDF pp.3,7: finite oscillator energy is equivalent to finite mean total
occupation for finitely many modes; the additive zero-point energy is irrelevant
to finiteness. Divergence remains infinity. -/
def bipartitePhotonEnergy {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (Occupation A × Occupation B) (Occupation A × Occupation B) ℂ) : ℝ≥0∞ :=
  ∑' u : Occupation A × Occupation B,
    ENNReal.ofReal ((∑ i, (u.1 i : ℝ)) + (∑ j, (u.2 j : ℝ))) *
      ENNReal.ofReal (rho u u).re

/-- PDF pp.3,7--8: finite first/second moments, in the equivalent Weyl-derivative
form. Energy finiteness enforces the quadratic-form domain; all real directions
are tested, fixing the full mean and covariance rather than energy alone. -/
def HasBipartiteMoments {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (Occupation A × Occupation B) (Occupation A × Occupation B) ℂ)
    (d : Quadratures (A ⊕ B) → ℝ)
    (gamma : Matrix (Quadratures (A ⊕ B)) (Quadratures (A ⊕ B)) ℝ) : Prop :=
  bipartitePhotonEnergy rho < ⊤ ∧
  ∀ xi : Quadratures (A ⊕ B) → ℝ,
    HasDerivAt (fun t : ℝ => bipartiteCharacteristic rho (t • xi))
      (Complex.I * (characteristicMean d xi : ℂ)) 0 ∧
    HasDerivAt (deriv (fun t : ℝ => bipartiteCharacteristic rho (t • xi)))
      (((-characteristicVariance gamma xi / 2 - (characteristicMean d xi) ^ 2 : ℝ) : ℂ)) 0

/-- PDF pp.7--8: Gaussian counterpart with its specified moments, on actual densities. -/
def HasBipartiteGaussianCharacteristic {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (Occupation A × Occupation B) (Occupation A × Occupation B) ℂ)
    (d : Quadratures (A ⊕ B) → ℝ)
    (gamma : Matrix (Quadratures (A ⊕ B)) (Quadratures (A ⊕ B)) ℝ) : Prop :=
  ∀ xi, bipartiteCharacteristic rho xi = gaussianStateCharacteristic d gamma xi

/-- PDF p.16, (53): X gamma X^T+Y, as opposed to (8)'s transposed X convention. -/
def covarianceAction {I : Type} [Fintype I]
    (X Y gamma : Matrix (Quadratures I) (Quadratures I) ℝ) :
    Matrix (Quadratures I) (Quadratures I) ℝ := X * gamma * X.transpose + Y

/-- PDF pp.3--4: the contravariant Weyl argument belonging to a quadrature map X. -/
def weylPullback {I : Type} [Fintype I]
    (X : Matrix (Quadratures I) (Quadratures I) ℝ) (xi : Quadratures I → ℝ) :
    Quadratures I → ℝ :=
  (-canonicalForm I * X.transpose * canonicalForm I).mulVec xi

/-- PDF pp.2--4,16: a full trace-class CPTP Gaussian channel, allowing affine
first-moment displacements omitted from the covariance formulas. Its normal
unital CP dual is determined by the all-state Weyl pairing. The noise
factor /4 matches the covariance normalization and corrects printed (6). -/
def IsGaussianChannel {I : Type} [Fintype I]
    (Phi : Matrix (Occupation I) (Occupation I) ℂ → Matrix (Occupation I) (Occupation I) ℂ)
    (X Y : Matrix (Quadratures I) (Quadratures I) ℝ) : Prop :=
  IsTraceClassChannel Phi ∧
  physicalCovariance Y (canonicalForm I - X * canonicalForm I * X.transpose) ∧
  ∃ shift : Quadratures I → ℝ,
    ∀ (rho : State (Occupation I)) (xi : Quadratures I → ℝ),
      singleCharacteristic (Phi rho.coefficients) xi =
        singleCharacteristic rho.coefficients (weylPullback X xi) *
        Complex.exp (((-characteristicVariance Y xi / 4 : ℝ) : ℂ) +
          Complex.I * (characteristicMean shift xi : ℂ))

/-- Regroup positions and momenta by subsystem, without changing any physical mode. -/
def splitQuadratures (A B : Type) :
    Quadratures (A ⊕ B) ≃ (Quadratures A ⊕ Quadratures B) where
  toFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inr (Sum.inl a) => Sum.inl (Sum.inr a)
    | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
    | Sum.inr (Sum.inr b) => Sum.inr (Sum.inr b)
  invFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr a) => Sum.inr (Sum.inl a)
    | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
    | Sum.inr (Sum.inr b) => Sum.inr (Sum.inr b)
  left_inv := by intro x; rcases x with (a | a) <;> rcases a with (a | b) <;> rfl
  right_inv := by intro x; rcases x with (a | a) <;> rcases a with (a | b) <;> rfl

/-- PDF p.16: tensor-product covariance, in the common grouped coordinate convention. -/
def jointInputCovariance {A B : Type} [Fintype A] [Fintype B]
    (gamma : Matrix (Quadratures A) (Quadratures A) ℝ)
    (gamma0 : Matrix (Quadratures B) (Quadratures B) ℝ) :
    Matrix (Quadratures (A ⊕ B)) (Quadratures (A ⊕ B)) ℝ :=
  (Matrix.fromBlocks gamma 0 0 gamma0).submatrix (splitQuadratures A B) (splitQuadratures A B)

/-- PDF pp.7,16: principal covariance corresponding to subsystem A. -/
def firstCovariance {A B : Type}
    (gamma : Matrix (Quadratures (A ⊕ B)) (Quadratures (A ⊕ B)) ℝ) :
    Matrix (Quadratures A) (Quadratures A) ℝ :=
  gamma.submatrix firstQuadratures firstQuadratures

/-- PDF pp.3--4,16: an actual bounded metaplectic implementation on the completed
bipartite oscillator space, expressed through all Weyl operators. Affine shifts
are retained even though they do not appear in the covariance transformation. -/
def IsBipartiteGaussianUnitary {A B : Type} [Fintype A] [Fintype B]
    (U : Hilbert (Occupation A × Occupation B) ≃ₗᵢ[ℂ] Hilbert (Occupation A × Occupation B))
    (S : Matrix (Quadratures (A ⊕ B)) (Quadratures (A ⊕ B)) ℝ) : Prop :=
  S * canonicalForm (A ⊕ B) * S.transpose = canonicalForm (A ⊕ B) ∧
  ∃ shift : Quadratures (A ⊕ B) → ℝ,
    ∀ xi, boundedUnitaryConjugation U.symm (bipartiteWeyl xi) =
      Complex.exp (Complex.I * (characteristicMean shift xi : ℂ)) •
        bipartiteWeyl (weylPullback S xi)

/-- PDF p.16, (53): the full pure environmental dilation. The same environment,
unitary, and symplectic matrix serve every input. Purity concerns the actual
trace-class density, as well as its covariance. Zero environmental modes are allowed. -/
structure PureGaussianDilation {n : ℕ}
    (Phi : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ →
      Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (X Y : Matrix (Quadratures (Fin n)) (Quadratures (Fin n)) ℝ) where
  modes : ℕ
  modes_bound : modes ≤ 2 * n
  environment : State (Occupation (Fin modes))
  environmentCovariance : Matrix (Quadratures (Fin modes)) (Quadratures (Fin modes)) ℝ
  environment_physical : pureCovariance environmentCovariance (canonicalForm (Fin modes))
  environment_pure : PureDensity environment.coefficients
  environment_gaussian : ∀ xi,
    singleCharacteristic environment.coefficients xi =
      gaussianStateCharacteristic 0 environmentCovariance xi
  symplecticMatrix : Matrix (Quadratures (Fin n ⊕ Fin modes)) (Quadratures (Fin n ⊕ Fin modes)) ℝ
  unitary : Hilbert (Occupation (Fin n) × Occupation (Fin modes)) ≃ₗᵢ[ℂ]
    Hilbert (Occupation (Fin n) × Occupation (Fin modes))
  unitary_gaussian : IsBipartiteGaussianUnitary unitary symplecticMatrix
  implements : ∀ rho, IsTraceClass rho →
    Phi rho = dilationReceiver unitary environment.coefficients rho
  covariance_identity : ∀ gamma,
    physicalCovariance gamma (canonicalForm (Fin n)) →
    firstCovariance (symplecticMatrix *
      jointInputCovariance gamma environmentCovariance * symplecticMatrix.transpose) =
      covarianceAction X Y gamma

/-- PDF p.16: gamma prime in (53), using the same fixed dilation. -/
def dilatedCovariance {n : ℕ} {Phi X Y} (D : @PureGaussianDilation n Phi X Y)
    (gamma : Matrix (Quadratures (Fin n)) (Quadratures (Fin n)) ℝ) :
    Matrix (Quadratures (Fin n ⊕ Fin D.modes)) (Quadratures (Fin n ⊕ Fin D.modes)) ℝ :=
  D.symplecticMatrix * jointInputCovariance gamma D.environmentCovariance *
    D.symplecticMatrix.transpose

/-- PDF p.7, (20): entropy of rho_gamma through all Williamson diagonalizations.
On physical covariances these have the same finite entropy. An empty set yields
infinity, never a default real zero. No density-operator full-rank assumption occurs. -/
def gaussianEntropy {I : Type} [Fintype I]
    (gamma : Matrix (Quadratures I) (Quadratures I) ℝ) : ℝ≥0∞ :=
  ⨅ w : {w : Matrix (Quadratures I) (Quadratures I) ℝ × (I → ℝ) //
      w.1 * canonicalForm I * w.1.transpose = canonicalForm I ∧
      (∀ i, 1 ≤ w.2 i) ∧ w.1 * gamma * w.1.transpose = thermalDiagonal w.2},
    ∑ i, ENNReal.ofReal (thermalEntropy ((w.val.2 i - 1) / 2))

/-- PDF p.15, (48): semidefinite covariance order, not entrywise matrix order. -/
def CovarianceBelow {I : Type} [Fintype I]
    (small large : Matrix (Quadratures I) (Quadratures I) ℝ) : Prop :=
  (large - small).PosSemidef

/-- PDF p.15, second line of (48): Gaussian EoF across A|B. This covariance
variational formula allows pure boundary points; it is not a definition through
channel capacity or through minimum output entropy. The unrestricted Gaussian
ensemble law in the original definition is not assumed Gaussian. -/
def gaussianEoF {A B : Type} [Fintype A] [Fintype B]
    (gamma : Matrix (Quadratures (A ⊕ B)) (Quadratures (A ⊕ B)) ℝ) : ℝ≥0∞ :=
  ⨅ p : {p : Matrix (Quadratures (A ⊕ B)) (Quadratures (A ⊕ B)) ℝ //
      pureCovariance p (canonicalForm (A ⊕ B)) ∧ CovarianceBelow p gamma},
    gaussianEntropy (firstCovariance p.val)

/-- PDF p.16, (56): Gaussian output entropy, independently of EoF. -/
def gaussianOutputEntropy {I : Type} [Fintype I]
    (X Y gamma : Matrix (Quadratures I) (Quadratures I) ℝ) : ℝ≥0∞ :=
  gaussianEntropy (covarianceAction X Y gamma)

/-- PDF pp.14,16, (46),(57), alpha=1: all Gaussian inputs, with no energy
constraint or density full-rank restriction. First moments do not affect entropy. -/
def gaussianMinimumOutputEntropy {I : Type} [Fintype I]
    (X Y : Matrix (Quadratures I) (Quadratures I) ℝ) : ℝ≥0∞ :=
  ⨅ gamma : {gamma : Matrix (Quadratures I) (Quadratures I) ℝ //
      physicalCovariance gamma (canonicalForm I)}, gaussianOutputEntropy X Y gamma.val

/-- Regroup two pairs so that all A modes precede all B modes. -/
def regroupPairs (A B C D : Type) : ((A ⊕ C) ⊕ (B ⊕ D)) ≃ ((A ⊕ B) ⊕ (C ⊕ D)) where
  toFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr c) => Sum.inr (Sum.inl c)
    | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
    | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)
  invFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inr (Sum.inl c) => Sum.inl (Sum.inr c)
    | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
    | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)
  left_inv := by intro x; rcases x with (a | a) <;> rcases a with (a | b) <;> rfl
  right_inv := by intro x; rcases x with (a | a) <;> rcases a with (a | b) <;> rfl

/-- PDF p.16, (I): direct sum regrouped as A1 A2 | B1 B2. -/
def pairedDirectSum {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (gamma1 : Matrix (Quadratures (A ⊕ B)) (Quadratures (A ⊕ B)) ℝ)
    (gamma2 : Matrix (Quadratures (C ⊕ D)) (Quadratures (C ⊕ D)) ℝ) :
    Matrix (Quadratures ((A ⊕ C) ⊕ (B ⊕ D))) (Quadratures ((A ⊕ C) ⊕ (B ⊕ D))) ℝ :=
  let r := regroupPairs A B C D
  let e := (Equiv.sumCongr r r).trans (splitQuadratures (A ⊕ B) (C ⊕ D))
  (Matrix.fromBlocks gamma1 0 0 gamma2).submatrix e e

/-- PDF pp.16--17: additivity is a global property, at every finite positive
mode count and on every physical bipartite covariance. Either party may have
zero modes, but an entire paired subsystem has positive total mode count. -/
def GaussianEoFAdditive : Prop :=
  ∀ (A B C D : Type) [Fintype A] [Fintype B] [Fintype C] [Fintype D],
    0 < Fintype.card A + Fintype.card B → 0 < Fintype.card C + Fintype.card D →
    ∀ (gamma1 : Matrix (Quadratures (A ⊕ B)) (Quadratures (A ⊕ B)) ℝ)
      (gamma2 : Matrix (Quadratures (C ⊕ D)) (Quadratures (C ⊕ D)) ℝ),
      physicalCovariance gamma1 (canonicalForm (A ⊕ B)) →
      physicalCovariance gamma2 (canonicalForm (C ⊕ D)) →
      gaussianEoF (pairedDirectSum gamma1 gamma2) = gaussianEoF gamma1 + gaussianEoF gamma2

/-- PDF pp.15--17, (50),(IV): global convexity of covariance arguments.
These arithmetic mixtures are not density-operator mixtures. -/
def GaussianEoFCovarianceConvex : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B],
    0 < Fintype.card A + Fintype.card B →
    ∀ (gamma1 gamma2 : Matrix (Quadratures (A ⊕ B)) (Quadratures (A ⊕ B)) ℝ),
      physicalCovariance gamma1 (canonicalForm (A ⊕ B)) →
      physicalCovariance gamma2 (canonicalForm (A ⊕ B)) →
      ∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 →
        gaussianEoF (lambda • gamma1 + (1 - lambda) • gamma2) ≤
          ENNReal.ofReal lambda * gaussianEoF gamma1 +
          ENNReal.ofReal (1 - lambda) * gaussianEoF gamma2

/-- Inclusion of one paired subsystem on both parties; correlations are retained
in the total covariance and only the selected principal submatrix is extracted. -/
def pairedInclusion {k : ℕ} (A B : Fin k → Type) (i : Fin k) :
    Quadratures (A i ⊕ B i) → Quadratures ((Sigma A) ⊕ (Sigma B)) :=
  Sum.map (Sum.map (Sigma.mk i) (Sigma.mk i)) (Sum.map (Sigma.mk i) (Sigma.mk i))

/-- PDF p.16, (58), footnote 19: all finite families of arbitrary local mode
counts. The total covariance need not be a direct sum. The global positive mode
convention is expressed by positive family size and positive paired mode counts. -/
def GaussianEoFSuperadditive : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (A B : Fin k → Type)
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)],
    (∀ i, 0 < Fintype.card (A i) + Fintype.card (B i)) →
    ∀ gamma : Matrix (Quadratures ((Sigma A) ⊕ (Sigma B)))
      (Quadratures ((Sigma A) ⊕ (Sigma B))) ℝ,
      physicalCovariance gamma (canonicalForm ((Sigma A) ⊕ (Sigma B))) →
      (∑ i, gaussianEoF (gamma.submatrix (pairedInclusion A B i) (pairedInclusion A B i))) ≤
        gaussianEoF gamma

/-! Sanity checks on the adapters; no source theorem is proved here. -/

example {I : Type} (i : I) : weylArgument (0 : Quadratures I → ℝ) i = 0 := by
  simp [weylArgument]

example {I : Type} [Fintype I] (d : Quadratures I → ℝ)
    (gamma : Matrix (Quadratures I) (Quadratures I) ℝ) :
    gaussianStateCharacteristic d gamma 0 = 1 := by
  simp [gaussianStateCharacteristic, characteristicVariance, quadraticForm, characteristicMean]

example {I : Type} [Fintype I] (gamma : Matrix (Quadratures I) (Quadratures I) ℝ) :
    CovarianceBelow gamma gamma := by
  simp only [CovarianceBelow, sub_self]
  exact Matrix.PosSemidef.zero

example {I : Type} [Fintype I] :
    weylKernel (0 : Quadratures I → ℝ) (fun _ => 0) (fun _ => 0) = 1 := by
  simp [weylKernel, weylArgument, displacementMatrix]

example : thermalEntropy 0 = 0 := by
  simp [thermalEntropy]

example {A B : Type} [Fintype A] [Fintype B]
    (gamma : Matrix (Quadratures A) (Quadratures A) ℝ)
    (gamma0 : Matrix (Quadratures B) (Quadratures B) ℝ) :
    firstCovariance (jointInputCovariance gamma gamma0) = gamma := by
  ext i j
  rcases i with (i | i) <;> rcases j with (j | j) <;> rfl

example {I : Type} [Fintype I] (gamma : Matrix (Quadratures I) (Quadratures I) ℝ) :
    covarianceAction 1 0 gamma = gamma := by
  simp [covarianceAction]

example {n : ℕ} {Phi X Y} (D : @PureGaussianDilation n Phi X Y) : D.modes ≤ 2 * n :=
  D.modes_bound

end QAlgorithms.Papers.Independent.Claimed50.P47


