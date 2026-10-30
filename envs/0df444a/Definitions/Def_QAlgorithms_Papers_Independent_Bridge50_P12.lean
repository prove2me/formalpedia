-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P12
-- name    : QAlgorithms_Papers_Independent_Bridge50_P12
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T12:26:40.756382+00:00
-- url     : https://prove2.me/theorems/9007faaa-3d43-4302-aa33-55430c362c4c
-- title:
--   Definitions for Asymptotically Consistent Measures of General Quantum Resources: Discord, Non-Markovianity, and Non-Gaussianity
-- statement:
--   The objects the formalized statements of *Asymptotically Consistent Measures of General Quantum Resources: Discord, Non-Markovianity, and Non-Gaussianity* (arXiv:2103.05665) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `normalizedResourceDistance`: PDF pp.3,12,14,19, (2), S25, S39, S106: extended distance to normalized free states. D5: no generic attainment on an arbitrary nonclosed set is assumed. Unlike Dependency50.P15.relativeDistance, this optimizes over normalized densities and takes values in ENNReal, rather than over unnormalized operators in EReal.
--   - `classicalClassical`: PDF p.12, S24: diagonal in some independent local ON bases, whose columns are U and V. Density is imposed by normalizedResourceDistance. D2: the joint diagonal runs over A × B, not paired labels.
--   - `quantumClassical`: PDF p.14, S38: block diagonal in some B basis, with arbitrary A blocks. No ON basis restriction on conditional A states. Density is imposed in the distance.
--   - `ccDephase`: PDF p.13, S26: both-party dephasing of THIS input over all product outcomes.
--   - `qcDephase`: PDF pp.14–15, S40: B-only dephasing. The unnormalized conditional-block formula retains every A matrix entry and never divides by a zero probability.
--   - `weightedOutcomeEntropy`: PDF p.16, S62: weighted entropy of an unnormalized A outcome. A zero-probability outcome contributes zero, without choosing a conditional state. This is weighted von Neumann entropy, distinct from the frozen outcomeEntropy functions, which compute Shannon entropy of a classical outcome distribution.
--   - `measuredConditionalEntropy`: PDF p.16, S62: general local measurement operators on B. For normalized measurements and density inputs, these nonnegative terms sum to at most log₂(dim A), so the tsum is summable, including arbitrary discrete outcome sets.
--   - `measurementDiscord`: PDF p.16, S60–S62: discord for measurements on B. HasSum imposes ΣM†M=I. The outcome type is arbitrary, including all finite families without a cardinality bound. On density inputs the infimum domain is nonempty (one identity outcome) and bounded in [0,log₂(dim A)]. The remaining terms are H(B)-H(AB).
--   - `groupedBipartiteProduct`: PDF p.17, S64: rho⊗sigma regrouped as AA':BB', rather than AB:A'B'.
--   - `markovStates`: PDF p.19, S105: zero CMI in bits, in order A×(B×C). The accepted CMI is H(AB)+H(BC)-H(B)-H(ABC). Density is imposed by the distance; no convexity or faithfulness restriction is imposed on the reference state.
--   - `markovModulus`: PDF p.21, S129: equality t=2/3 uses the first branch. For density inputs, h₂ is only evaluated inside [0,1] in the selected branch.
--   - `gaussianStates`: PDF pp.21–22, S130: all displaced Gaussian densities on completed Fock space. Accepted V=2Λ and v=Ωξ give the source's sign and covariance convention. There is no centered-state restriction or photon-number cutoff.
--   - `nonGaussianity`: PDF p.22, S131: extended relative-entropy distance to all Gaussian states in bits; no infinite entropy subtraction. D5: define an infimum value.
--   - `oscillatorEnergyExpectation`: PDF p.22, S139–S140: extended expectation of H=hw a†a in one mode. The coefficient sum is nonnegative and retains infinite energy. This expectation is distinct from Dependency50.P15.oscillatorEnergy, the energy of one basis label.
-- source:
--   Asymptotically Consistent Measures of General Quantum Resources: Discord, Non-Markovianity, and Non-Gaussianity, arXiv:2103.05665v4, https://arxiv.org/abs/2103.05665v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

/-!
Kuroiwa and Yamasaki, arXiv:2103.05665v4; all pages below are PDF pages.
D2: c-c sums range over independent product outcomes, not equally labeled pairs.
D5: extended infima define distance values; S9/S13 assert attained entropy minima.
General state-QRT and copy-rate interfaces are deferred explicitly in HARD.md.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Bridge50.P12

-- Exact frozen normalized-state divergence in bits; no local alias.
open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

/-- PDF pp.3,12,14,19, (2), S25, S39, S106: extended distance to normalized
free states. D5: no generic attainment on an arbitrary nonclosed set is assumed.
Unlike Dependency50.P15.relativeDistance, this optimizes over normalized densities
and takes values in ENNReal, rather than over unnormalized operators in EReal. -/
def normalizedResourceDistance {I : Type} [Fintype I] [DecidableEq I]
    (F : Set (Matrix I I ℂ)) (rho : Matrix I I ℂ) : ℝ≥0∞ :=
  ⨅ sigma : {sigma : Matrix I I ℂ // IsDensityMatrix sigma ∧ sigma ∈ F},
    relativeEntropyBits rho sigma.val

/-- PDF p.12, S24: diagonal in some independent local ON bases, whose columns
are U and V. Density is imposed by normalizedResourceDistance. D2: the joint diagonal
runs over A × B, not paired labels. -/
def classicalClassical {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] : Set (Matrix (A × B) (A × B) ℂ) :=
  {rho | ∃ (U : Matrix.unitaryGroup A ℂ) (V : Matrix.unitaryGroup B ℂ),
    let W := Matrix.kronecker (U : Matrix A A ℂ) (V : Matrix B B ℂ)
    ∀ p q : A × B, p ≠ q → (Wᴴ * rho * W) p q = 0}

/-- PDF p.14, S38: block diagonal in some B basis, with arbitrary A blocks.
No ON basis restriction on conditional A states. Density is imposed in the distance. -/
def quantumClassical {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] : Set (Matrix (A × B) (A × B) ℂ) :=
  {rho | ∃ V : Matrix.unitaryGroup B ℂ,
    let W := Matrix.kronecker (1 : Matrix A A ℂ) (V : Matrix B B ℂ)
    ∀ a a' : A, ∀ b b' : B, b ≠ b' → (Wᴴ * rho * W) (a,b) (a',b') = 0}

/-- PDF p.13, S26: both-party dephasing of THIS input over all product outcomes. -/
def ccDephase {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup B ℂ) (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  let W := Matrix.kronecker (U : Matrix A A ℂ) (V : Matrix B B ℂ)
  let X := Wᴴ * rho * W
  W * Matrix.diagonal (fun p => X p p) * Wᴴ

/-- PDF pp.14–15, S40: B-only dephasing. The unnormalized conditional-block
formula retains every A matrix entry and never divides by a zero probability. -/
def qcDephase {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (V : Matrix.unitaryGroup B ℂ)
    (rho : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ :=
  let W := Matrix.kronecker (1 : Matrix A A ℂ) (V : Matrix B B ℂ)
  let X := Wᴴ * rho * W
  W * Matrix.of (fun (p q : A × B) => if p.2 = q.2 then X p q else 0) * Wᴴ

/-- PDF p.16, S62: weighted entropy of an unnormalized A outcome. A
zero-probability outcome contributes zero, without choosing a conditional state.
This is weighted von Neumann entropy, distinct from the frozen outcomeEntropy
functions, which compute Shannon entropy of a classical outcome distribution. -/
def weightedOutcomeEntropy {A : Type} [Fintype A] [DecidableEq A]
    (X : Matrix A A ℂ) : ℝ :=
  let p := X.trace.re
  if p = 0 then 0 else p * vnEntropy (((p⁻¹ : ℝ) : ℂ) • X)

/-- PDF p.16, S62: general local measurement operators on B. For normalized
measurements and density inputs, these nonnegative terms sum to at most log₂(dim A),
so the tsum is summable, including arbitrary discrete outcome sets. -/
def measuredConditionalEntropy {A B O : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (M : O → Matrix B B ℂ) : ℝ :=
  ∑' k, weightedOutcomeEntropy (traceRight
    ((Matrix.kronecker (1 : Matrix A A ℂ) (M k)) * rho *
      (Matrix.kronecker (1 : Matrix A A ℂ) (M k))ᴴ))

/-- PDF p.16, S60–S62: discord for measurements on B. HasSum imposes ΣM†M=I.
The outcome type is arbitrary, including all finite families without a cardinality
bound. On density inputs the infimum domain is nonempty (one identity outcome)
and bounded in [0,log₂(dim A)]. The remaining terms are H(B)-H(AB). -/
def measurementDiscord {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  vnEntropy (traceLeft rho) - vnEntropy rho +
    sInf {x : ℝ | ∃ (O : Type) (M : O → Matrix B B ℂ),
      HasSum (fun k => (M k)ᴴ * M k) (1 : Matrix B B ℂ) ∧
      x = measuredConditionalEntropy rho M}

/-- PDF p.17, S64: rho⊗sigma regrouped as AA':BB', rather than AB:A'B'. -/
def groupedBipartiteProduct {A B A2 B2 : Type}
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix (A2 × B2) (A2 × B2) ℂ) :
    Matrix ((A × A2) × (B × B2)) ((A × A2) × (B × B2)) ℂ :=
  fun p q => rho (p.1.1,p.2.1) (q.1.1,q.2.1) * sigma (p.1.2,p.2.2) (q.1.2,q.2.2)

/-- PDF p.19, S105: zero CMI in bits, in order A×(B×C).
The accepted CMI is H(AB)+H(BC)-H(B)-H(ABC). Density is imposed by the distance;
no convexity or faithfulness restriction is imposed on the reference state. -/
def markovStates {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Set (Matrix (A × (B × C)) (A × (B × C)) ℂ) :=
  {rho | QAlgorithms.Papers.Independent.Claimed50.P12.cmi rho = 0}

/-- PDF p.21, S129: equality t=2/3 uses the first branch. For density inputs,
h₂ is only evaluated inside [0,1] in the selected branch. -/
def markovModulus (D : ℕ) (t : ℝ) : ℝ :=
  if t ≤ 2 / 3 then 2 * (t * Real.logb 2 D + binEntropy2 t)
  else t / 2 * Real.logb 2 D + binEntropy2 (t / 2) + Real.logb 2 D

/-- PDF pp.21–22, S130: all displaced Gaussian densities on completed Fock
space. Accepted V=2Λ and v=Ωξ give the source's sign and covariance convention.
There is no centered-state restriction or photon-number cutoff. -/
def gaussianStates (m : ℕ) :
    Set (QAlgorithms.Papers.Independent.Dependency50.P33.State
      (QAlgorithms.Papers.Independent.Claimed50.P19.FockIndex m)) :=
  {rho | ∃ V, QAlgorithms.Papers.Independent.Claimed50.P19.GaussianWithCovariance
    rho.coefficients V}

/-- PDF p.22, S131: extended relative-entropy distance to all Gaussian states
in bits; no infinite entropy subtraction. D5: define an infimum value. -/
def nonGaussianity {m : ℕ}
    (rho : QAlgorithms.Papers.Independent.Dependency50.P33.State
      (QAlgorithms.Papers.Independent.Claimed50.P19.FockIndex m)) : ℝ≥0∞ :=
  ⨅ sigma : {sigma : QAlgorithms.Papers.Independent.Dependency50.P33.State
      (QAlgorithms.Papers.Independent.Claimed50.P19.FockIndex m) // sigma ∈ gaussianStates m},
    QAlgorithms.Papers.Independent.Frontier18.P07.extendedRelativeEntropyNats
      rho.coefficients sigma.val.coefficients / ENNReal.ofReal (Real.log 2)

/-- PDF p.22, S139–S140: extended expectation of H=hw a†a in one mode.
The coefficient sum is nonnegative and retains infinite energy. This expectation
is distinct from Dependency50.P15.oscillatorEnergy, the energy of one basis label. -/
def oscillatorEnergyExpectation (hw : ℝ) (rho : Matrix (Fin 1 → ℕ) (Fin 1 → ℕ) ℂ) : ℝ≥0∞ :=
  ∑' i : Fin 1 → ℕ, ENNReal.ofReal (hw * (i 0 : ℝ)) * ENNReal.ofReal (rho i i).re

/-- Sanity check for the imported divergence: invalid density arguments give infinity. -/

example {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (h : ¬ (IsDensityMatrix rho ∧ IsDensityMatrix sigma)) :
    relativeEntropyBits rho sigma = ⊤ := by simp [relativeEntropyBits, h]

example {A : Type} [Fintype A] [DecidableEq A]
    (X : Matrix A A ℂ) (h : X.trace.re = 0) : weightedOutcomeEntropy X = 0 := by
  simp [weightedOutcomeEntropy, h]

example {A B A2 B2 : Type}
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix (A2 × B2) (A2 × B2) ℂ)
    (a a' : A) (b b' : B) (c c' : A2) (d d' : B2) :
    groupedBipartiteProduct rho sigma ((a,c),(b,d)) ((a',c'),(b',d')) =
      rho (a,b) (a',b') * sigma (c,d) (c',d') := by rfl

example (D : ℕ) : markovModulus D (2 / 3) =
    2 * ((2 / 3) * Real.logb 2 D + binEntropy2 (2 / 3)) := by simp [markovModulus]

example (hw : ℝ) : oscillatorEnergyExpectation hw
    (QAlgorithms.Papers.Independent.Claimed50.P19.vacuumKernel 1) = 0 := by
  unfold oscillatorEnergyExpectation
  apply ENNReal.tsum_eq_zero.mpr
  intro i
  by_cases h : i = (fun _ => 0)
  · subst i
    simp [QAlgorithms.Papers.Independent.Claimed50.P19.vacuumKernel]
  · simp [QAlgorithms.Papers.Independent.Claimed50.P19.vacuumKernel, h]

end QAlgorithms.Papers.Independent.Bridge50.P12


