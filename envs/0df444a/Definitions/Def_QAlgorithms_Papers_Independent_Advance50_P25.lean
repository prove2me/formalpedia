-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25
-- name    : QAlgorithms_Papers_Independent_Advance50_P25
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T17:47:11.27188+00:00
-- url     : https://prove2.me/theorems/98c8c9fe-ec55-4f0f-9eba-d31cb1d7e54b
-- title:
--   Definitions for Non-negative discord strengthens the subadditivity of quantum entropy functions
-- statement:
--   The objects the formalized statements of *Non-negative discord strengthens the subadditivity of quantum entropy functions* (arXiv:1101.1717) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `EntropyFunction`: PDF p.1, §II: one entropy family on all finite matrix dimensions.
--   - `DensityEnsemble`: PDF p.2, Eq.(5): a finite normalized density ensemble. Zero-weight components may be filled by any density; deleting them leaves every quantity unchanged.
--   - `IsPureFiniteDensity`: PDF pp.3–4: purity means a density of a unit vector, not a pure marginal.
--   - `IsEntropy`: PDF p.1 and the proof of Theorem 2 on p.3: spectral, zero-padding invariant, concave entropy, with the implicit convention that every pure density has entropy zero. Concavity is finite-ensemble concavity, with no strictness requirement.
--   - `quadraticEntropy`: PDF p.1, Eq.(1): quadratic entropy, with no logarithm or dimension factor.
--   - `finiteTraceMoment`: PDF pp.1,4, Eqs.(1),(22): trace of a positive matrix's real power.
--   - `tsallisEntropy`: PDF p.1, Eq.(1): Tsallis entropy, with the stipulated q=1 extension.
--   - `renyiEntropyNats`: PDF p.1, Eq.(1): Renyi entropy; theorem domains impose 0 < q ≤ 1.
--   - `IsRankOnePOVM`: PDF p.2: every effect in a rank-one POVM has rank exactly one; no trace-one or projector restriction is imposed.
--   - `generalizedMutualInformation`: PDF p.1, Eq.(2): mutual information from actual partial traces.
--   - `generalEntropyHolevo`: PDF p.2, Eq.(5): Holevo quantity of the computed average.
--   - `localEffectProbability`: PDF p.2, Eq.(6): Born probability for an effect on the first register.
--   - `normalizeOutcome`: PDF p.2, Eqs.(6),(8): normalize only positive-probability outcomes. The zero placeholder at an impossible outcome is never treated as a density.
--   - `remoteOutcome`: PDF p.2, Eq.(6): remote state conditioned on an outcome on a.
--   - `jointOutcome`: PDF p.2, Eq.(8), normalized as in its remote expressions and p.4 proof: choose K=sqrt(P); its left polar unitary does not affect the entropies in Eq.(8).
--   - `remoteConditionalEntropy`: PDF p.2, Eq.(8): weighted remote conditional entropy; zero outcomes are omitted.
--   - `measurementHolevo`: PDF p.2, Eq.(7): measurement Holevo quantity, without an optimization.
--   - `povmSpecificDiscord`: PDF p.2, Eq.(9): measurement-specific discord.
--   - `localConditionalEntropy`: PDF p.2, Eq.(8): local conditional entropy using normalized joint outcomes.
--   - `conditionalMutualInformation`: PDF p.2, Eq.(8): conditional mutual information averaged over outcomes.
--   - `FirmlySubadditive`: PDF p.2, Definition 1: FSA uniformly over every finite positive dimension.
--   - `SubadditiveEntropy`: PDF p.1, Eq.(3): subadditivity over all bipartite densities.
--   - `LocalHolevoBound`: PDF p.3, Theorem 2(ii): universal local-entropy bound.
--   - `PureDiscardMonotone`: PDF p.3, Theorem 2(iii): only pure joint states and rank-one POVMs.
--   - `PureChannelMonotone`: PDF p.3, Theorem 2(iv): channel data processing only for pure input ensembles.
--   - `BasisFirmlySubadditive`: PDF pp.2–3: testing every orthonormal basis, including in enlarged dimensions.
--   - `StrongFirmlySubadditive`: PDF p.3, Theorem 3(i): the stronger, residual-mutual-information bound.
--   - `StrongLocalHolevoBound`: PDF p.3, Theorem 3(ii): the stronger local-entropy bound.
--   - `DiscardMonotone`: PDF p.3, Theorem 3(iii): arbitrary tripartite densities and arbitrary POVMs.
--   - `ChannelMonotone`: PDF p.3, Theorem 3(iv): channel data processing for arbitrary density ensembles.
--   - `hilbertSchmidtDistance`: PDF p.4, Eq.(21): squared Hilbert–Schmidt distance, without a square root.
--   - `matrixAbsolute`: PDF p.4, Eq.(22): matrix absolute value sqrt(X dagger X).
--   - `basisCQDensity`: PDF pp.4–5, Eq.(27): actual classical–quantum block density in basis w.
--   - `GeneralizedAdditive`: PDF pp.4–5, Eq.(27): generalized additivity as a global entropy property. Spectral invariance makes a fixed basis in each dimension equivalent to all bases.
--   - `AdditiveEntropy`: PDF p.4, Eq.(26): additivity on all products, not on a single mixture.
--   - `StronglySubadditive`: PDF p.2, Eq.(4): SSA in the source's mutual-information form. No equivalence with other SSA formulas is assumed for general entropies.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, https://arxiv.org/abs/1101.1717v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33

/-!
Finite-dimensional statements from Coles, arXiv:1101.1717v1, PDF pp.1–5.
New interfaces belong only to this paper; compatible primitives are imported
from the pinned accepted library. Entropy is a dimension-uniform family.
All physical registers are nonempty finite complex spaces. Zero-probability
measurement outcomes are omitted from conditional averages. No discord is optimized.
The normalized interpretation of the post-measurement matrices in Eq.(8) follows
the explicitly normalized remote matrices there and the proof on PDF p.4.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)
open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)
open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF p.1, §II: one entropy family on all finite matrix dimensions. -/
abbrev EntropyFunction :=
  ∀ {I : Type} [Fintype I] [DecidableEq I], Matrix I I ℂ → ℝ

/-- PDF p.2, Eq.(5): a finite normalized density ensemble. Zero-weight components
may be filled by any density; deleting them leaves every quantity unchanged. -/
def DensityEnsemble {I J : Type} [Fintype I] [Fintype J]
    (p : J → ℝ) (rho : J → Matrix I I ℂ) : Prop :=
  IsLaw p ∧ ∀ j, IsDensityMatrix (rho j)

/-- PDF pp.3–4: purity means a density of a unit vector, not a pure marginal. -/
def IsPureFiniteDensity {I : Type} [Fintype I] (rho : Matrix I I ℂ) : Prop :=
  ∃ psi : EuclideanSpace ℂ I, ‖psi‖ = 1 ∧ rho = pureDensity psi

/-- PDF p.1 and the proof of Theorem 2 on p.3: spectral, zero-padding invariant,
concave entropy, with the implicit convention that every pure density has entropy zero.
Concavity is finite-ensemble concavity, with no strictness requirement. -/
def IsEntropy (S : EntropyFunction) : Prop :=
  (∀ {I J : Type} [Fintype I] [DecidableEq I] [Nonempty I]
      [Fintype J] [DecidableEq J] [Nonempty J]
      (rho : Matrix I I ℂ) (sigma : Matrix J J ℂ),
      IsDensityMatrix rho → IsDensityMatrix sigma →
      nonzeroSpectrum rho = nonzeroSpectrum sigma → S rho = S sigma) ∧
  (∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
      (rho : Matrix I I ℂ), IsPureFiniteDensity rho → S rho = 0) ∧
  (∀ {I J : Type} [Fintype I] [DecidableEq I] [Nonempty I]
      [Fintype J] [DecidableEq J] [Nonempty J]
      (p : J → ℝ) (rho : J → Matrix I I ℂ), DensityEnsemble p rho →
      (∑ j, p j * S (rho j)) ≤ S (average rho p))

/-- PDF p.1, Eq.(1): quadratic entropy, with no logarithm or dimension factor. -/
def quadraticEntropy : EntropyFunction :=
  fun {_} _ _ rho => 1 - (rho * rho).trace.re

/-- PDF pp.1,4, Eqs.(1),(22): trace of a positive matrix's real power. -/
def finiteTraceMoment {I : Type} [Fintype I] [DecidableEq I]
    (q : ℝ) (A : Matrix I I ℂ) : ℝ :=
  (cfc (fun x : ℝ => x ^ q) A).trace.re

/-- PDF p.1, Eq.(1): Tsallis entropy, with the stipulated q=1 extension. -/
def tsallisEntropy (q : ℝ) : EntropyFunction :=
  fun {_} _ _ rho => if q = 1 then entropy rho
    else (finiteTraceMoment q rho - 1) / (1 - q)

/-- PDF p.1, Eq.(1): Renyi entropy; theorem domains impose 0 < q ≤ 1. -/
def renyiEntropyNats (q : ℝ) : EntropyFunction :=
  fun {_} _ _ rho => if q = 1 then entropy rho
    else Real.log (finiteTraceMoment q rho) / (1 - q)

/-- PDF p.2: every effect in a rank-one POVM has rank exactly one;
no trace-one or projector restriction is imposed. -/
def IsRankOnePOVM {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (P : J → Matrix I I ℂ) : Prop :=
  IsPOVM P ∧ ∀ j, (P j).rank = 1

/-- PDF p.1, Eq.(2): mutual information from actual partial traces. -/
def generalizedMutualInformation (S : EntropyFunction) {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  S (traceRight rho) + S (traceLeft rho) - S rho

/-- PDF p.2, Eq.(5): Holevo quantity of the computed average. -/
def generalEntropyHolevo (S : EntropyFunction) {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J]
    (p : J → ℝ) (rho : J → Matrix I I ℂ) : ℝ :=
  S (average rho p) - ∑ j, p j * S (rho j)

/-- PDF p.2, Eq.(6): Born probability for an effect on the first register. -/
def localEffectProbability {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] (rho : Matrix (A × B) (A × B) ℂ) (P : Matrix A A ℂ) : ℝ :=
  effectProb P (traceRight rho)

/-- PDF p.2, Eqs.(6),(8): normalize only positive-probability outcomes.
The zero placeholder at an impossible outcome is never treated as a density. -/
def normalizeOutcome {I : Type} (p : ℝ) (M : Matrix I I ℂ) : Matrix I I ℂ :=
  if 0 < p then (p⁻¹ : ℂ) • M else 0

/-- PDF p.2, Eq.(6): remote state conditioned on an outcome on a. -/
def remoteOutcome {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (P : Matrix A A ℂ) : Matrix B B ℂ :=
  normalizeOutcome (localEffectProbability rho P)
    (traceLeft (Matrix.kronecker P (1 : Matrix B B ℂ) * rho))

/-- PDF p.2, Eq.(8), normalized as in its remote expressions and p.4 proof:
choose K=sqrt(P); its left polar unitary does not affect the entropies in Eq.(8). -/
def jointOutcome {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (P : Matrix A A ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  let K := Matrix.kronecker (cfc Real.sqrt P) (1 : Matrix B B ℂ)
  normalizeOutcome (localEffectProbability rho P) (K * rho * Kᴴ)

/-- PDF p.2, Eq.(8): weighted remote conditional entropy; zero outcomes are omitted. -/
def remoteConditionalEntropy (S : EntropyFunction) {A B J : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype J]
    (rho : Matrix (A × B) (A × B) ℂ) (P : J → Matrix A A ℂ) : ℝ :=
  ∑ j, if 0 < localEffectProbability rho (P j) then
    localEffectProbability rho (P j) * S (remoteOutcome rho (P j)) else 0

/-- PDF p.2, Eq.(7): measurement Holevo quantity, without an optimization. -/
def measurementHolevo (S : EntropyFunction) {A B J : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype J]
    (rho : Matrix (A × B) (A × B) ℂ) (P : J → Matrix A A ℂ) : ℝ :=
  S (traceLeft rho) - remoteConditionalEntropy S rho P

/-- PDF p.2, Eq.(9): measurement-specific discord. -/
def povmSpecificDiscord (S : EntropyFunction) {A B J : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype J]
    (rho : Matrix (A × B) (A × B) ℂ) (P : J → Matrix A A ℂ) : ℝ :=
  generalizedMutualInformation S rho - measurementHolevo S rho P

/-- PDF p.2, Eq.(8): local conditional entropy using normalized joint outcomes. -/
def localConditionalEntropy (S : EntropyFunction) {A B J : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype J]
    (rho : Matrix (A × B) (A × B) ℂ) (P : J → Matrix A A ℂ) : ℝ :=
  ∑ j, if 0 < localEffectProbability rho (P j) then
    localEffectProbability rho (P j) * S (traceRight (jointOutcome rho (P j))) else 0

/-- PDF p.2, Eq.(8): conditional mutual information averaged over outcomes. -/
def conditionalMutualInformation (S : EntropyFunction) {A B J : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype J]
    (rho : Matrix (A × B) (A × B) ℂ) (P : J → Matrix A A ℂ) : ℝ :=
  ∑ j, if 0 < localEffectProbability rho (P j) then
    localEffectProbability rho (P j) * generalizedMutualInformation S (jointOutcome rho (P j)) else 0

/-- PDF p.2, Definition 1: FSA uniformly over every finite positive dimension. -/
def FirmlySubadditive (S : EntropyFunction) : Prop :=
  ∀ {A B J : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (rho : Matrix (A × B) (A × B) ℂ) (P : J → Matrix A A ℂ),
    IsDensityMatrix rho → IsPOVM P →
    measurementHolevo S rho P ≤ generalizedMutualInformation S rho

/-- PDF p.1, Eq.(3): subadditivity over all bipartite densities. -/
def SubadditiveEntropy (S : EntropyFunction) : Prop :=
  ∀ {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ), IsDensityMatrix rho →
    S rho ≤ S (traceRight rho) + S (traceLeft rho)

/-- PDF p.3, Theorem 2(ii): universal local-entropy bound. -/
def LocalHolevoBound (S : EntropyFunction) : Prop :=
  ∀ {A B J : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (rho : Matrix (A × B) (A × B) ℂ) (P : J → Matrix A A ℂ),
    IsDensityMatrix rho → IsPOVM P →
    measurementHolevo S rho P ≤ S (traceRight rho)

/-- PDF p.3, Theorem 2(iii): only pure joint states and rank-one POVMs. -/
def PureDiscardMonotone (S : EntropyFunction) : Prop :=
  ∀ {A B C J : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (rho : Matrix (A × (B × C)) (A × (B × C)) ℂ) (P : J → Matrix A A ℂ),
    IsDensityMatrix rho → IsPureFiniteDensity rho → IsRankOnePOVM P →
    measurementHolevo S (discardLast rho) P ≤ measurementHolevo S rho P

/-- PDF p.3, Theorem 2(iv): channel data processing only for pure input ensembles. -/
def PureChannelMonotone (S : EntropyFunction) : Prop :=
  ∀ {I O J : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype O] [DecidableEq O] [Nonempty O]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (E : Superop I O) (p : J → ℝ) (rho : J → Matrix I I ℂ),
    IsChannel E → DensityEnsemble p rho → (∀ j, IsPureFiniteDensity (rho j)) →
    generalEntropyHolevo S p (fun j => E (rho j)) ≤ generalEntropyHolevo S p rho

/-- PDF pp.2–3: testing every orthonormal basis, including in enlarged dimensions. -/
def BasisFirmlySubadditive (S : EntropyFunction) : Prop :=
  ∀ {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ)
    (w : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)), IsDensityMatrix rho →
    measurementHolevo S rho (fun j => pureDensity (w j)) ≤ generalizedMutualInformation S rho

/-- PDF p.3, Theorem 3(i): the stronger, residual-mutual-information bound. -/
def StrongFirmlySubadditive (S : EntropyFunction) : Prop :=
  ∀ {A B J : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (rho : Matrix (A × B) (A × B) ℂ) (P : J → Matrix A A ℂ),
    IsDensityMatrix rho → IsPOVM P →
    measurementHolevo S rho P ≤
      generalizedMutualInformation S rho - conditionalMutualInformation S rho P

/-- PDF p.3, Theorem 3(ii): the stronger local-entropy bound. -/
def StrongLocalHolevoBound (S : EntropyFunction) : Prop :=
  ∀ {A B J : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (rho : Matrix (A × B) (A × B) ℂ) (P : J → Matrix A A ℂ),
    IsDensityMatrix rho → IsPOVM P →
    measurementHolevo S rho P ≤ S (traceRight rho) - localConditionalEntropy S rho P

/-- PDF p.3, Theorem 3(iii): arbitrary tripartite densities and arbitrary POVMs. -/
def DiscardMonotone (S : EntropyFunction) : Prop :=
  ∀ {A B C J : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (rho : Matrix (A × (B × C)) (A × (B × C)) ℂ) (P : J → Matrix A A ℂ),
    IsDensityMatrix rho → IsPOVM P →
    measurementHolevo S (discardLast rho) P ≤ measurementHolevo S rho P

/-- PDF p.3, Theorem 3(iv): channel data processing for arbitrary density ensembles. -/
def ChannelMonotone (S : EntropyFunction) : Prop :=
  ∀ {I O J : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype O] [DecidableEq O] [Nonempty O]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (E : Superop I O) (p : J → ℝ) (rho : J → Matrix I I ℂ),
    IsChannel E → DensityEnsemble p rho →
    generalEntropyHolevo S p (fun j => E (rho j)) ≤ generalEntropyHolevo S p rho

/-- PDF p.4, Eq.(21): squared Hilbert–Schmidt distance, without a square root. -/
def hilbertSchmidtDistance {I : Type} [Fintype I]
    (rho sigma : Matrix I I ℂ) : ℝ :=
  ((rho - sigma) * (rho - sigma)).trace.re

/-- PDF p.4, Eq.(22): matrix absolute value sqrt(X dagger X). -/
def matrixAbsolute {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : Matrix I I ℂ :=
  cfc Real.sqrt (Xᴴ * X)

/-- PDF pp.4–5, Eq.(27): actual classical–quantum block density in basis w. -/
def basisCQDensity {A B : Type} [Fintype A]
    (w : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (p : A → ℝ) (rho : A → Matrix B B ℂ) : Matrix (A × B) (A × B) ℂ :=
  ∑ j, (p j : ℂ) • Matrix.kronecker (pureDensity (w j)) (rho j)

/-- PDF pp.4–5, Eq.(27): generalized additivity as a global entropy property.
Spectral invariance makes a fixed basis in each dimension equivalent to all bases. -/
def GeneralizedAdditive (S : EntropyFunction) : Prop :=
  ∀ {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (w : OrthonormalBasis A ℂ (EuclideanSpace ℂ A))
    (p : A → ℝ) (rho : A → Matrix B B ℂ), DensityEnsemble p rho →
    S (basisCQDensity w p rho) = S (traceRight (basisCQDensity w p rho)) + ∑ j, p j * S (rho j)

/-- PDF p.4, Eq.(26): additivity on all products, not on a single mixture. -/
def AdditiveEntropy (S : EntropyFunction) : Prop :=
  ∀ {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (rho : Matrix A A ℂ) (sigma : Matrix B B ℂ),
    IsDensityMatrix rho → IsDensityMatrix sigma →
    S (Matrix.kronecker rho sigma) = S rho + S sigma

/-- PDF p.2, Eq.(4): SSA in the source's mutual-information form.
No equivalence with other SSA formulas is assumed for general entropies. -/
def StronglySubadditive (S : EntropyFunction) : Prop :=
  ∀ {A B C : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Matrix (A × (B × C)) (A × (B × C)) ℂ), IsDensityMatrix rho →
    generalizedMutualInformation S (discardLast rho) ≤ generalizedMutualInformation S rho

/-- Sanity: Eq.(5) on a deterministic one-component ensemble is zero. -/
example (S : EntropyFunction) {I : Type} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) :
    generalEntropyHolevo S (fun _ : Fin 1 => (1 : ℝ)) (fun _ => rho) = 0 := by
  simp [generalEntropyHolevo, average]

/-- Sanity: impossible outcomes have a zero placeholder, with no inverse of zero. -/
example {I : Type} (M : Matrix I I ℂ) : normalizeOutcome 0 M = 0 := by
  simp [normalizeOutcome]

/-- Sanity: Eq.(21) vanishes on equal inputs, including rank-deficient states. -/
example {I : Type} [Fintype I] (rho : Matrix I I ℂ) :
    hilbertSchmidtDistance rho rho = 0 := by
  simp [hilbertSchmidtDistance]

/-- Sanity: the Tsallis q=1 extension is von Neumann entropy, not division by zero. -/
example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    tsallisEntropy 1 rho = entropy rho := by
  simp [tsallisEntropy]

/-- Sanity: the Renyi q=1 extension uses the same logarithm units. -/
example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    renyiEntropyNats 1 rho = entropy rho := by
  simp [renyiEntropyNats]

end QAlgorithms.Papers.Independent.Advance50.P25


