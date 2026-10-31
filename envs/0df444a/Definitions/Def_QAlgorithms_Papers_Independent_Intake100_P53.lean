-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P53
-- name    : QAlgorithms_Papers_Independent_Intake100_P53
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T13:43:10.634931+00:00
-- url     : https://prove2.me/theorems/f7e0cf9b-3ec6-4291-85d8-2ef86ca5124f
-- title:
--   Definitions for Security of coherent state quantum cryptography in the presence of Gaussian noise
-- statement:
--   The objects the formalized statements of *Security of coherent state quantum cryptography in the presence of Gaussian noise* (arXiv:quant-ph/0608015) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CoherentHeterodyneParameters`: PDF pp.2--3: finite modulation, channel transmittivity, and excess noise.
--   - `priorDensity`: PDF p.2, (2): planar modulation density.
--   - `circularGaussian`: PDF pp.2--3: circular Gaussian measure with real-coordinate variance v.
--   - `modulation`: PDF p.2, (2): actual modulation probability measure.
--   - `heterodyneDensity`: PDF p.3, (5): heterodyne density relative to planar Lebesgue measure.
--   - `receivedState`: PDF p.3: actual displaced thermal operator; accepted thermal a=1+delta has mean photon number (a-1)/2=delta/2. Realization is a theorem conclusion.
--   - `modulationOutcomeLaw`: PDF p.3, (5): joint modulation/outcome law, with independent Gaussian heterodyne noise of coordinate variance (2+delta)/4.
--   - `rawBit`: PDF p.2: false=0, true=1; the null real axis is assigned bit zero.
--   - `announcement`: PDF p.2: both components (absolute real part, imaginary part) are public.
--   - `signedAmplitude`: PDF p.4: the labelled preimages of an announcement on its half-plane.
--   - `announcementLaw`: PDF pp.4--5: induced public law; neither imaginary coordinate is discarded.
--   - `signAnnouncementDensity`: PDF p.4: joint sign/announcement density from the four preimages.
--   - `announcementDensity`: PDF p.4: announcement density obtained by marginalizing the signs.
--   - `signKernel`: PDF p.4: density disintegration, not singleton-event conditioning.
--   - `bitError`: PDF p.4: actual bit-error probability before evaluating (12).
--   - `aliceAnnouncementDensity`: PDF p.4, (6): Alice's announcement density on the half-plane.
--   - `bobAnnouncementDensity`: PDF p.4, (9): Bob's conditional announcement density.
--   - `aliceMagnitudeDensity`: PDF p.5, (17): the half-normal absolute-real prior.
--   - `bobMagnitudeDensity`: PDF p.4, (16): the folded-normal absolute-real conditional density.
--   - `channelMutualInformation`: PDF p.4, (14): mutual information in bits computed from the finite sign kernel, including its actual row and column marginals.
--   - `announcedMutualInformation`: PDF pp.4--5: averaged conditional SIGN mutual information, not analog MI.
--   - `oscillatorVectorOfCoefficients`: PDF pp.3,6: realize coefficients in the complete l2 register. Every physical use concludes realization and unit norm; zero fallback is not silently used to manufacture a state.
--   - `GaussianAttack`: PDF pp.1--3: one pure isometry, fixed independently of the signal, repeated iid in the collective scenario. Eve keeps its entire supported environment. The receiver kernel is verified for every coherent input by complete tomography. Countable environment coordinates entail no energy cutoff: inaccessible unused ancillary directions may be removed. The source's incomplete finite-sample tomography step is not asserted as a theorem.
--   - `branchCoefficient`: PDF pp.3,6: coherent-bra projection onto Bob. Omitting 1/sqrt(pi) makes the branch norm squared equal to pi times the heterodyne density.
--   - `eveBranch`: PDF pp.3,6: physical unnormalized Eve branch.
--   - `eveVector`: PDF pp.3,5: conditional pure vector; positive density justifies normalization.
--   - `eveSupport`: PDF p.3: closed support of the full labelled conditional ensemble.
--   - `supportedVector`: PDF p.3: physical vector in its supported space.
--   - `physicalDyad`: PDF p.5: the actual four conditional pure projectors.
--   - `physicalMixture`: PDF p.5, (18): Eve's state from the actual sign disintegration.
--   - `physicalDR`: PDF p.5, (21): actual state conditioned on Alice's bit.
--   - `physicalRR`: PDF p.5, (21): actual state conditioned on Bob's bit.
--   - `splitterCoefficient`: PDF p.6, (28): bounded number-basis beam-splitter action. For c=sqrt(eta),s=sqrt(1-eta), b† maps to c b†+s e† and e† to -s b†+c e†. Only conserved-photon-number coefficients k≤m+n are used below.
--   - `clonerCoefficient`: PDF p.6, (27)--(28): three-mode coefficients in order B,E1,E2. The minus sign is the source's S=exp[-xi e1†e2†+conj(xi)e2e1], xi=r exp(i gamma). All number subtraction is guarded by the conserved total photon number.
--   - `clonerVector`: PDF p.6, (27): constructed vector on three complete oscillator spaces.
--   - `BinaryProductModel`: PDF pp.6--8, (36)--(41): independent product algebra, p=|c0|²,q=|c+|². Nonnegative square-root representatives fix irrelevant basis phases. The lower bounds mean the source's real overlaps are nonnegative; no physical A,B is asserted.
--   - `factorVector`: PDF p.7, (36)--(39): binary factor with either sign.
--   - `productDyad`: PDF pp.6--7: tensor dyads in the fixed factor order (Alice,Bob).
--   - `productMixture`: PDF p.5, (18): explicitly constructed product-model mixture.
--   - `productDR`: PDF pp.7--8, (45): direct conditional state, constructed from dyads.
--   - `productRR`: PDF p.8, (50): reverse conditional state in the same factor order. Constructing the dyads corrects (51)'s repeated |c+|² lower diagonal entry.
--   - `productHolevoDR`: PDF p.5, (24): direct Holevo quantity with both conditional entropies.
--   - `productHolevoRR`: PDF p.5, (25): reverse Holevo quantity with both conditional entropies.
--   - `blockRoot`: PDF p.7, (43): roots of a two-dimensional block; plus root first.
--   - `mixtureSpectrum`: PDF p.7, (43): all four eigenvalues with multiplicity.
--   - `conditionalSpectrum`: PDF p.8, (48),(52): the two conditional eigenvalue candidates.
-- source:
--   Security of coherent state quantum cryptography in the presence of Gaussian noise, arXiv:quant-ph/0608015v4, https://arxiv.org/abs/quant-ph/0608015v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

/-!
Heid--Luetkenhaus, arXiv:quant-ph/0608015v4. Physical oscillator conditioning
and binary-product algebra are separate. No definition identifies the disputed
printed (35) with physical overlaps. Operational extraction is deferred;
a numerical integral is not defined to be an achievable secret-key rate.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P53

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39
open scoped ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.2--3: finite modulation, channel transmittivity, and excess noise. -/
structure CoherentHeterodyneParameters where
  kappa : ℝ
  eta : ℝ
  delta : ℝ
  kappa_pos : 0 < kappa
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1
  delta_nonneg : 0 ≤ delta

/-- PDF p.2, (2): planar modulation density. -/
def priorDensity (P : CoherentHeterodyneParameters) (alpha : ℂ) : ℝ :=
  Real.exp (-Complex.normSq alpha / (2 * P.kappa)) / (2 * Real.pi * P.kappa)

/-- PDF pp.2--3: circular Gaussian measure with real-coordinate variance v. -/
def circularGaussian (v : NNReal) : Measure ℂ :=
  Measure.map (fun z : ℝ × ℝ => (z.1 : ℂ) + Complex.I * (z.2 : ℂ))
    ((ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v))

/-- PDF p.2, (2): actual modulation probability measure. -/
def modulation (P : CoherentHeterodyneParameters) : Measure ℂ :=
  circularGaussian ⟨P.kappa, P.kappa_pos.le⟩

/-- PDF p.3, (5): heterodyne density relative to planar Lebesgue measure. -/
def heterodyneDensity (P : CoherentHeterodyneParameters) (alpha beta : ℂ) : ℝ :=
  2 / (Real.pi * (2 + P.delta)) *
    Real.exp (-2 * Complex.normSq (beta - (Real.sqrt P.eta : ℂ) * alpha) / (2 + P.delta))

/-- PDF p.3: actual displaced thermal operator; accepted thermal a=1+delta
has mean photon number (a-1)/2=delta/2. Realization is a theorem conclusion. -/
def receivedState (P : CoherentHeterodyneParameters) (alpha : ℂ) : FockOperator :=
  let D := displacement ((Real.sqrt P.eta : ℂ) * alpha)
  (D.comp (thermalDensity (1 + P.delta))).comp (ContinuousLinearMap.adjoint D)

/-- PDF p.3, (5): joint modulation/outcome law, with independent Gaussian
heterodyne noise of coordinate variance (2+delta)/4. -/
def modulationOutcomeLaw (P : CoherentHeterodyneParameters) : Measure (ℂ × ℂ) :=
  Measure.map (fun z : ℂ × ℂ => (z.1, (Real.sqrt P.eta : ℂ) * z.1 + z.2))
    ((modulation P).prod (circularGaussian
      ⟨(2 + P.delta) / 4, by linarith [P.delta_nonneg]⟩))

/-- PDF p.2: false=0, true=1; the null real axis is assigned bit zero. -/
def rawBit (alpha : ℂ) : Bool := decide (alpha.re < 0)

/-- PDF p.2: both components (absolute real part, imaginary part) are public. -/
def announcement (alpha : ℂ) : ℝ × ℝ := (|alpha.re|, alpha.im)

/-- PDF p.4: the labelled preimages of an announcement on its half-plane. -/
def signedAmplitude (a : ℝ × ℝ) (i : Bool) : ℂ :=
  ((if i then -a.1 else a.1) : ℝ) + Complex.I * (a.2 : ℂ)

/-- PDF pp.4--5: induced public law; neither imaginary coordinate is discarded. -/
def announcementLaw (P : CoherentHeterodyneParameters) : Measure ((ℝ × ℝ) × (ℝ × ℝ)) :=
  Measure.map (fun z : ℂ × ℂ => (announcement z.1, announcement z.2)) (modulationOutcomeLaw P)

/-- PDF p.4: joint sign/announcement density from the four preimages. -/
def signAnnouncementDensity (P : CoherentHeterodyneParameters) (a b : ℝ × ℝ) (i j : Bool) : ℝ :=
  priorDensity P (signedAmplitude a i) *
    heterodyneDensity P (signedAmplitude a i) (signedAmplitude b j)

/-- PDF p.4: announcement density obtained by marginalizing the signs. -/
def announcementDensity (P : CoherentHeterodyneParameters) (a b : ℝ × ℝ) : ℝ :=
  ∑ i : Bool, ∑ j : Bool, signAnnouncementDensity P a b i j

/-- PDF p.4: density disintegration, not singleton-event conditioning. -/
def signKernel (P : CoherentHeterodyneParameters) (a b : ℝ × ℝ) (i j : Bool) : ℝ :=
  signAnnouncementDensity P a b i j / announcementDensity P a b

/-- PDF p.4: actual bit-error probability before evaluating (12). -/
def bitError (P : CoherentHeterodyneParameters) (a b : ℝ × ℝ) : ℝ :=
  ∑ i : Bool, signKernel P a b i (!i)

/-- PDF p.4, (6): Alice's announcement density on the half-plane. -/
def aliceAnnouncementDensity (P : CoherentHeterodyneParameters) (a : ℝ × ℝ) : ℝ :=
  ∑ i : Bool, priorDensity P (signedAmplitude a i)

/-- PDF p.4, (9): Bob's conditional announcement density. -/
def bobAnnouncementDensity (P : CoherentHeterodyneParameters) (a b : ℝ × ℝ) : ℝ :=
  announcementDensity P a b / aliceAnnouncementDensity P a

/-- PDF p.5, (17): the half-normal absolute-real prior. -/
def aliceMagnitudeDensity (P : CoherentHeterodyneParameters) (u : ℝ) : ℝ :=
  Real.sqrt (2 / (Real.pi * P.kappa)) * Real.exp (-u ^ 2 / (2 * P.kappa))

/-- PDF p.4, (16): the folded-normal absolute-real conditional density. -/
def bobMagnitudeDensity (P : CoherentHeterodyneParameters) (u w : ℝ) : ℝ :=
  Real.sqrt (2 / (Real.pi * (2 + P.delta))) *
    (Real.exp (-2 * (w + Real.sqrt P.eta * u) ^ 2 / (2 + P.delta)) +
      Real.exp (-2 * (w - Real.sqrt P.eta * u) ^ 2 / (2 + P.delta)))

/-- PDF p.4, (14): mutual information in bits computed from the finite sign
kernel, including its actual row and column marginals. -/
def channelMutualInformation (P : CoherentHeterodyneParameters) (a b : ℝ × ℝ) : ℝ :=
  ∑ i : Bool, ∑ j : Bool,
    signKernel P a b i j * Real.logb 2
      (signKernel P a b i j /
        ((∑ k : Bool, signKernel P a b i k) * (∑ k : Bool, signKernel P a b k j)))

/-- PDF pp.4--5: averaged conditional SIGN mutual information, not analog MI. -/
def announcedMutualInformation (P : CoherentHeterodyneParameters) : ℝ :=
  ∫ z, channelMutualInformation P z.1 z.2 ∂announcementLaw P

/-- PDF pp.3,6: realize coefficients in the complete l2 register.
Every physical use concludes realization and unit norm; zero fallback is not
silently used to manufacture a state. -/
def oscillatorVectorOfCoefficients {I : Type} (c : I → ℂ) : QAlgorithms.RealRegisters.Hilbert I :=
  if h : ∃ v : QAlgorithms.RealRegisters.Hilbert I, ∀ i, v i = c i then
    Classical.choose h else 0

/-- PDF pp.1--3: one pure isometry, fixed independently of the signal, repeated
iid in the collective scenario. Eve keeps its entire supported environment.
The receiver kernel is verified for every coherent input by complete tomography.
Countable environment coordinates entail no energy cutoff: inaccessible unused
ancillary directions may be removed. The source's incomplete finite-sample
tomography step is not asserted as a theorem. -/
structure GaussianAttack (P : CoherentHeterodyneParameters) where
  interaction : Fock →ₗᵢ[ℂ] QAlgorithms.RealRegisters.Hilbert (ℕ × ℕ)
  receiver : ∀ (alpha : ℂ) (m n : ℕ),
    (∑' k : ℕ, interaction (coherentKet alpha) (m, k) *
      conj (interaction (coherentKet alpha) (n, k))) =
      receivedState P alpha (fockKet n) m

/-- PDF pp.3,6: coherent-bra projection onto Bob. Omitting 1/sqrt(pi)
makes the branch norm squared equal to pi times the heterodyne density. -/
def branchCoefficient {P : CoherentHeterodyneParameters} (V : GaussianAttack P)
    (alpha beta : ℂ) (k : ℕ) : ℂ :=
  ∑' n : ℕ, conj (coherentKet beta n) * V.interaction (coherentKet alpha) (n, k)

/-- PDF pp.3,6: physical unnormalized Eve branch. -/
def eveBranch {P : CoherentHeterodyneParameters} (V : GaussianAttack P) (alpha beta : ℂ) : Fock :=
  oscillatorVectorOfCoefficients (branchCoefficient V alpha beta)

/-- PDF pp.3,5: conditional pure vector; positive density justifies normalization. -/
def eveVector {P : CoherentHeterodyneParameters} (V : GaussianAttack P) (alpha beta : ℂ) : Fock :=
  (‖eveBranch V alpha beta‖⁻¹ : ℂ) • eveBranch V alpha beta

/-- PDF p.3: closed support of the full labelled conditional ensemble. -/
def eveSupport {P : CoherentHeterodyneParameters} (V : GaussianAttack P) : Submodule ℂ Fock :=
  (Submodule.span ℂ (Set.range (fun z : ℂ × ℂ => eveVector V z.1 z.2))).topologicalClosure

/-- PDF p.3: physical vector in its supported space. -/
def supportedVector {P : CoherentHeterodyneParameters} (V : GaussianAttack P) (alpha beta : ℂ) : eveSupport V :=
  ⟨eveVector V alpha beta,
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(alpha, beta), rfl⟩)⟩

/-- PDF p.5: the actual four conditional pure projectors. -/
def physicalDyad {P : CoherentHeterodyneParameters} (V : GaussianAttack P)
    (a b : ℝ × ℝ) (i j : Bool) : FockOperator :=
  let v := eveVector V (signedAmplitude a i) (signedAmplitude b j)
  InnerProductSpace.rankOne ℂ v v

/-- PDF p.5, (18): Eve's state from the actual sign disintegration. -/
def physicalMixture {P : CoherentHeterodyneParameters} (V : GaussianAttack P) (a b : ℝ × ℝ) : FockOperator :=
  ∑ i : Bool, ∑ j : Bool, (signKernel P a b i j : ℂ) • physicalDyad V a b i j

/-- PDF p.5, (21): actual state conditioned on Alice's bit. -/
def physicalDR {P : CoherentHeterodyneParameters} (V : GaussianAttack P)
    (a b : ℝ × ℝ) (i : Bool) : FockOperator :=
  ((∑ j : Bool, signKernel P a b i j)⁻¹ : ℂ) •
    ∑ j : Bool, (signKernel P a b i j : ℂ) • physicalDyad V a b i j

/-- PDF p.5, (21): actual state conditioned on Bob's bit. -/
def physicalRR {P : CoherentHeterodyneParameters} (V : GaussianAttack P)
    (a b : ℝ × ℝ) (j : Bool) : FockOperator :=
  ((∑ i : Bool, signKernel P a b i j)⁻¹ : ℂ) •
    ∑ i : Bool, (signKernel P a b i j : ℂ) • physicalDyad V a b i j

/-- PDF p.6, (28): bounded number-basis beam-splitter action.
For c=sqrt(eta),s=sqrt(1-eta), b† maps to c b†+s e† and e† to -s b†+c e†.
Only conserved-photon-number coefficients k≤m+n are used below. -/
def splitterCoefficient (eta : ℝ) (m n k : ℕ) : ℂ :=
  if k ≤ m + n then
    (Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial (m + n - k) : ℝ) /
      ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
    ∑ j ∈ Finset.range (m + 1),
      if j ≤ k ∧ k - j ≤ n then
        (Nat.choose m j : ℂ) * (Nat.choose n (k - j) : ℂ) *
          (Real.sqrt eta : ℂ) ^ j * (Real.sqrt (1 - eta) : ℂ) ^ (m - j) *
          (-(Real.sqrt (1 - eta) : ℂ)) ^ (k - j) * (Real.sqrt eta : ℂ) ^ (n - (k - j))
      else 0
  else 0

/-- PDF p.6, (27)--(28): three-mode coefficients in order B,E1,E2.
The minus sign is the source's S=exp[-xi e1†e2†+conj(xi)e2e1], xi=r exp(i gamma).
All number subtraction is guarded by the conserved total photon number. -/
def clonerCoefficient (eta r gamma : ℝ) (alpha : ℂ) (z : ℕ × (ℕ × ℕ)) : ℂ :=
  let k := z.1
  let l := z.2.1
  let n := z.2.2
  if n ≤ k + l then
    coherentCoefficient alpha (k + l - n) *
      (-Complex.exp (Complex.I * (gamma : ℂ)) * (Real.tanh r : ℂ)) ^ n /
        (Real.cosh r : ℂ) * splitterCoefficient eta (k + l - n) n k
  else 0

/-- PDF p.6, (27): constructed vector on three complete oscillator spaces. -/
def clonerVector (eta r gamma : ℝ) (alpha : ℂ) :
    QAlgorithms.RealRegisters.Hilbert (ℕ × (ℕ × ℕ)) :=
  oscillatorVectorOfCoefficients (clonerCoefficient eta r gamma alpha)

/-- PDF pp.6--8, (36)--(41): independent product algebra, p=|c0|²,q=|c+|².
Nonnegative square-root representatives fix irrelevant basis phases. The lower
bounds mean the source's real overlaps are nonnegative; no physical A,B is asserted. -/
structure BinaryProductModel where
  p : ℝ
  q : ℝ
  e : ℝ
  p_lower : 1 / 2 ≤ p
  p_upper : p ≤ 1
  q_lower : 1 / 2 ≤ q
  q_upper : q ≤ 1
  e_lower : 0 ≤ e
  e_upper : e ≤ 1 / 2

/-- PDF p.7, (36)--(39): binary factor with either sign. -/
def factorVector (p : ℝ) (i : Bool) : EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 fun k => if k then
    (if i then -(Real.sqrt (1 - p) : ℂ) else (Real.sqrt (1 - p) : ℂ))
  else (Real.sqrt p : ℂ)

/-- PDF pp.6--7: tensor dyads in the fixed factor order (Alice,Bob). -/
def productDyad (M : BinaryProductModel) (i j : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.kronecker (QAlgorithms.pureDensity (factorVector M.p i))
    (QAlgorithms.pureDensity (factorVector M.q j))

/-- PDF p.5, (18): explicitly constructed product-model mixture. -/
def productMixture (M : BinaryProductModel) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  ((1 / 2 : ℝ) : ℂ) •
    (((1 - M.e : ℝ) : ℂ) • (productDyad M false false + productDyad M true true) +
      (M.e : ℂ) • (productDyad M false true + productDyad M true false))

/-- PDF pp.7--8, (45): direct conditional state, constructed from dyads. -/
def productDR (M : BinaryProductModel) (i : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  ((1 - M.e : ℝ) : ℂ) • productDyad M i i + (M.e : ℂ) • productDyad M i (!i)

/-- PDF p.8, (50): reverse conditional state in the same factor order.
Constructing the dyads corrects (51)'s repeated |c+|² lower diagonal entry. -/
def productRR (M : BinaryProductModel) (j : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  ((1 - M.e : ℝ) : ℂ) • productDyad M j j + (M.e : ℂ) • productDyad M (!j) j

/-- PDF p.5, (24): direct Holevo quantity with both conditional entropies. -/
def productHolevoDR (M : BinaryProductModel) : ℝ :=
  QAlgorithms.vnEntropy (productMixture M) -
    (QAlgorithms.vnEntropy (productDR M false) + QAlgorithms.vnEntropy (productDR M true)) / 2

/-- PDF p.5, (25): reverse Holevo quantity with both conditional entropies. -/
def productHolevoRR (M : BinaryProductModel) : ℝ :=
  QAlgorithms.vnEntropy (productMixture M) -
    (QAlgorithms.vnEntropy (productRR M false) + QAlgorithms.vnEntropy (productRR M true)) / 2

/-- PDF p.7, (43): roots of a two-dimensional block; plus root first. -/
def blockRoot (s d : ℝ) (k : Fin 2) : ℝ :=
  (s + (if k = 0 then 1 else -1) * Real.sqrt (s ^ 2 - d)) / 2

/-- PDF p.7, (43): all four eigenvalues with multiplicity. -/
def mixtureSpectrum (M : BinaryProductModel) : Fin 4 → ℝ :=
  let s := M.p * (1 - M.q) + (1 - M.p) * M.q
  let t := M.p * M.q + (1 - M.p) * (1 - M.q)
  let d := 16 * M.e * (1 - M.e) * M.p * (1 - M.p) * M.q * (1 - M.q)
  ![blockRoot s d 0, blockRoot s d 1, blockRoot t d 0, blockRoot t d 1]

/-- PDF p.8, (48),(52): the two conditional eigenvalue candidates. -/
def conditionalSpectrum (p e : ℝ) (k : Fin 2) : ℝ :=
  blockRoot 1 (16 * e * (1 - e) * p * (1 - p)) k

/-- Definition sanity: the heterodyne density at its center, PDF p.3, (5). -/

example (P : CoherentHeterodyneParameters) (alpha : ℂ) :
    heterodyneDensity P alpha ((Real.sqrt P.eta : ℂ) * alpha) = 2 / (Real.pi * (2 + P.delta)) := by
  simp [heterodyneDensity]

example (P : CoherentHeterodyneParameters) : priorDensity P 0 = 1 / (2 * Real.pi * P.kappa) := by
  simp [priorDensity]

example : oscillatorVectorOfCoefficients (fun _ : ℕ => (0 : ℂ)) = (0 : Fock) := by
  have h : ∃ v : Fock, ∀ n, v n = 0 := ⟨0, by simp⟩
  unfold oscillatorVectorOfCoefficients
  rw [dif_pos h]
  ext n
  exact Classical.choose_spec h n

example : rawBit (0 : ℂ) = false := by simp [rawBit]

example : announcement (0 : ℂ) = (0, 0) := by simp [announcement]

example (y : ℝ) : signedAmplitude (0, y) true = signedAmplitude (0, y) false := by
  simp [signedAmplitude]

example (P : CoherentHeterodyneParameters) : 0 < 2 + P.delta := by linarith [P.delta_nonneg]

example (P : CoherentHeterodyneParameters) (V : GaussianAttack P) (alpha beta : ℂ) :
    (supportedVector V alpha beta : Fock) = eveVector V alpha beta := rfl

example : splitterCoefficient (1 : ℝ) 0 0 0 = 1 := by simp [splitterCoefficient]

example (eta gamma : ℝ) : clonerCoefficient eta 0 gamma 0 (0, (0, 0)) = 1 := by
  simp [clonerCoefficient, coherentCoefficient, splitterCoefficient]

example : factorVector 1 false false = 1 := by simp [factorVector]

example : Nonempty CoherentHeterodyneParameters :=
  ⟨⟨1, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

example : Nonempty BinaryProductModel :=
  ⟨⟨1, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

example (p e : ℝ) : conditionalSpectrum p e 0 =
    (1 + Real.sqrt (1 - 16 * e * (1 - e) * p * (1 - p))) / 2 := by
  simp [conditionalSpectrum, blockRoot]

example (M : BinaryProductModel) : productDR M false =
    ((1 - M.e : ℝ) : ℂ) • productDyad M false false +
      (M.e : ℂ) • productDyad M false true := rfl

end QAlgorithms.Papers.Independent.Intake100.P53


