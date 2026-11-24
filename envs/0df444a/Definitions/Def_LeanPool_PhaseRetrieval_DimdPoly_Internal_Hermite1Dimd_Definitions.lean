-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:59:05.983691+00:00
-- url     : https://prove2.me/theorems/3300a440-535f-4c14-9027-40727b2fe6fb
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Hermite1Dimd/Definitions.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate Topology
noncomputable section
namespace Hermite1DimdLEAN
abbrev CSpace (d : ℕ) := Fin d → ℂ
abbrev MultiIndex (d : ℕ) := Fin d → ℕ
abbrev T : ℝ := HermiteLEAN.T
lemma T_pos : 0 < T := HermiteLEAN.T_pos
instance : Fact (0 < T) := ⟨T_pos⟩
abbrev Circle := AddCircle T
def gaussianDensity (d : ℕ) (z : CSpace d) : ℝ :=
  (1 / Real.pi ^ d) * Real.exp (-(∑ q : Fin d, ‖z q‖ ^ 2))
def gaussianMeasure (d : ℕ) : Measure (CSpace d) :=
  volume.withDensity fun z => ENNReal.ofReal (gaussianDensity d z)
noncomputable def oneDimPhi (k n : ℕ) : ℂ → ℂ := fun z =>
  ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
    Finset.sum (Finset.range (min k n + 1)) (fun j =>
      ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
        ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
        z ^ (n - j) * (star z) ^ (k - j))
def PhiKappaAlpha {d : ℕ} (κ α : MultiIndex d) : CSpace d → ℂ :=
  fun z => ∏ q : Fin d, oneDimPhi (κ q) (α q) (z q)
def nuKappa {d : ℕ} (κ : MultiIndex d) : CSpace d → ℂ :=
  PhiKappaAlpha κ 0
def rho (a u : ℂ) : ℝ := |‖a + u‖ - ‖a‖|
def gaussianL2NormSq {d : ℕ} {α : Type*} [Norm α] (F : CSpace d → α) : ℝ :=
  ∫ z, ‖F z‖ ^ 2 ∂ gaussianMeasure d
def gaussianL2Norm {d : ℕ} {α : Type*} [Norm α] (F : CSpace d → α) : ℝ :=
  Real.sqrt (gaussianL2NormSq F)
def gaussianInner {d : ℕ} (F G : CSpace d → ℂ) : ℂ :=
  ∫ z, F z * conj (G z) ∂ gaussianMeasure d
def circleL2NormSq {α : Type*} [Norm α] (F : Circle → α) : ℝ :=
  ∫ t, ‖F t‖ ^ 2 ∂ AddCircle.haarAddCircle
def circleL2Norm {α : Type*} [Norm α] (F : Circle → α) : ℝ :=
  Real.sqrt (circleL2NormSq F)
structure FiniteHermiteSum (d : ℕ) where
  /-- `coeff`: coeff. -/
  coeff : MultiIndex d →₀ ℂ
namespace FiniteHermiteSum
def support {d : ℕ} (G : FiniteHermiteSum d) : Finset (MultiIndex d) :=
  G.coeff.support
end FiniteHermiteSum
def evalHermiteSum {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : CSpace d → ℂ :=
  fun z => Finset.sum G.support fun α => G.coeff α * PhiKappaAlpha κ α z
def hermiteInner {d : ℕ} (κ : MultiIndex d) (G H : FiniteHermiteSum d) : ℂ :=
  gaussianInner (evalHermiteSum κ G) (evalHermiteSum κ H)
def hermiteInnerNu {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℂ :=
  gaussianInner (evalHermiteSum κ G) (nuKappa κ)
def hermiteNormSq {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2NormSq (evalHermiteSum κ G)
def hermiteNorm {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2Norm (evalHermiteSum κ G)
def defectFunction {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : CSpace d → ℝ :=
  fun z => rho (nuKappa κ z) (evalHermiteSum κ G z)
def defectNormSq {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2NormSq (defectFunction κ G)
def defectNorm {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2Norm (defectFunction κ G)
def totalDegree {d : ℕ} (α : MultiIndex d) : ℕ :=
  ∑ q : Fin d, α q
def blockIndexMulti {d : ℕ} (α : MultiIndex d) : MultiIndex d :=
  fun q => HermiteLEAN.blockIndex (α q)
def totalDegreePiece {d : ℕ} (n : ℕ) (G : FiniteHermiteSum d) : FiniteHermiteSum d := by
  classical
  refine ⟨Finsupp.onFinset (G.support.filter fun α => totalDegree α = n)
    (fun α => if totalDegree α = n then G.coeff α else 0) ?_⟩
  intro α hα
  have hdeg : totalDegree α = n := by
    simp_all
  have hsupp : α ∈ G.support := Finsupp.mem_support_iff.mpr (by simpa [hdeg] using hα)
  exact Finset.mem_filter.mpr ⟨hsupp, hdeg⟩
def productAnnulus {d : ℕ} (j : MultiIndex d) : Set (CSpace d) :=
  { z | ∀ q, (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1 }
def indicatorMul {α : Type*} (s : Set α) (f : α → ℂ) : α → ℂ :=
  by
    classical
    exact fun x => if x ∈ s then f x else 0
def annulusInner {d : ℕ} (j : MultiIndex d) (F G : CSpace d → ℂ) : ℂ :=
  by
    classical
    exact ∫ z, if z ∈ productAnnulus j then F z * conj (G z) else 0 ∂ gaussianMeasure d
def annulusMass {d : ℕ} (j : MultiIndex d) (F : CSpace d → ℂ) : ℝ :=
  by
    classical
    exact ∫ z, if z ∈ productAnnulus j then ‖F z‖ ^ 2 else 0 ∂ gaussianMeasure d
def defectAnnulusMass {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d)
    (F : CSpace d → ℂ) : ℝ :=
  by
    classical
    exact
      ∫ z, if z ∈ productAnnulus j then rho (nuKappa κ z) (F z) ^ 2 else 0
        ∂ gaussianMeasure d
def squareBlock {d : ℕ} (ℓ : MultiIndex d) : Set (MultiIndex d) :=
  { α | ∀ q, α q ∈ HermiteLEAN.squareBlock (ℓ q) }
def blockDistance {d : ℕ} (j ℓ : MultiIndex d) : ℕ :=
  (Finset.univ : Finset (Fin d)).sup fun q => Nat.dist (j q) (ℓ q)
def blockPart {d : ℕ} (ℓ : MultiIndex d) (G : FiniteHermiteSum d) : FiniteHermiteSum d := by
  classical
  refine ⟨Finsupp.onFinset (G.support.filter fun α => α ∈ squareBlock ℓ)
    (fun α => if α ∈ squareBlock ℓ then G.coeff α else 0) ?_⟩
  intro α hα
  have hblock : α ∈ squareBlock ℓ := by
    simp_all
  have hsupp : α ∈ G.support := Finsupp.mem_support_iff.mpr (by simpa [hblock] using hα)
  exact Finset.mem_filter.mpr ⟨hsupp, hblock⟩
def localCoeffSet {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    Finset (MultiIndex d) :=
  G.support.filter fun α => blockDistance j (blockIndexMulti α) ≤ M
def farCoeffSet {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    Finset (MultiIndex d) :=
  G.support.filter fun α => M < blockDistance j (blockIndexMulti α)
def localPart {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    FiniteHermiteSum d := by
  classical
  refine ⟨Finsupp.onFinset (localCoeffSet j M G)
    (fun α => if blockDistance j (blockIndexMulti α) ≤ M then G.coeff α else 0) ?_⟩
  intro α hα
  have hlocal : blockDistance j (blockIndexMulti α) ≤ M := by
    simp_all
  have hsupp : α ∈ G.support := Finsupp.mem_support_iff.mpr (by simpa [hlocal] using hα)
  exact Finset.mem_filter.mpr ⟨hsupp, hlocal⟩
def remainderPart {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    FiniteHermiteSum d := by
  classical
  refine ⟨Finsupp.onFinset (farCoeffSet j M G)
    (fun α => if M < blockDistance j (blockIndexMulti α) then G.coeff α else 0) ?_⟩
  intro α hα
  have hfar : M < blockDistance j (blockIndexMulti α) := by
    simp_all
  have hsupp : α ∈ G.support := Finsupp.mem_support_iff.mpr (by simpa [hfar] using hα)
  exact Finset.mem_filter.mpr ⟨hsupp, hfar⟩
def localDegreeSet {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) : Finset ℕ :=
  (localCoeffSet j M G).image totalDegree
def localDegreePiece {d : ℕ} (j : MultiIndex d) (M n : ℕ) (G : FiniteHermiteSum d) :
    FiniteHermiteSum d :=
  totalDegreePiece n (localPart j M G)
def degreeIntervalLower {d : ℕ} (j : MultiIndex d) (M : ℕ) : ℕ :=
  ∑ q, (max (j q) M - M) ^ 2
def degreeIntervalUpper {d : ℕ} (j : MultiIndex d) (M : ℕ) : ℕ :=
  ∑ q, ((j q + M + 1) ^ 2 - 1)
def degreeWidth {d : ℕ} (j : MultiIndex d) (M : ℕ) : ℕ :=
  degreeIntervalUpper j M - degreeIntervalLower j M + 1
def annulusRadius {d : ℕ} (j : MultiIndex d) : ℕ :=
  (Finset.univ : Finset (Fin d)).sup fun q => j q
def degreeThreshold (d M : ℕ) : ℕ := M + 120 * d * (2 * M + 1)
def productAnnulusConstant (d M : ℕ) : ℝ :=
  12 * Real.sqrt d * ((degreeThreshold d M + M : ℕ) : ℝ)
def productAnnulusConstantSq (d M : ℕ) : ℝ :=
  144 * d * ((degreeThreshold d M + M : ℕ) : ℝ) ^ 2
def prodLocalizationConstant {d : ℕ} (κ : MultiIndex d) : ℝ :=
  ∏ q : Fin d, ((κ q + 1 : ℕ) : ℝ)
def prodLocalizationDecay {d : ℕ} (κ : MultiIndex d) : ℝ :=
  (∏ q : Fin d, ((κ q + 1 : ℕ) : ℝ))⁻¹
def prodLocalizationShift {d : ℕ} (κ : MultiIndex d) : ℝ :=
  ∑ q : Fin d, ((κ q + 4 : ℕ) : ℝ)
def shellCardinality (d r : ℕ) : ℕ :=
  (2 * r + 1) ^ d - (2 * r - 1) ^ d
def localizationLeakageCoefficient (C c B : ℝ) (d M : ℕ) : ℝ :=
  C *
    ∑' r : ℕ,
      if M + 1 ≤ r then
        (shellCardinality d r : ℝ) *
          Real.exp
            (-(c) *
              max ((r : ℝ) - B) 0 ^ 2)
      else 0
def leakageCoefficient {d : ℕ} (κ : MultiIndex d) (M : ℕ) : ℝ :=
  prodLocalizationConstant κ *
    ∑' r : ℕ,
      if M + 1 ≤ r then
        (shellCardinality d r : ℝ) *
          Real.exp
            (-(prodLocalizationDecay κ) *
              max ((r : ℝ) - prodLocalizationShift κ) 0 ^ 2)
      else 0
def absorptionPredicate {d : ℕ} (κ : MultiIndex d) (M : ℕ) : Prop :=
  (4 * productAnnulusConstantSq d M + 2) * leakageCoefficient κ M < 1 / 2
def coercivityConstant {d : ℕ} (κ : MultiIndex d) (M : ℕ) : ℝ :=
  2 * productAnnulusConstant d M /
    Real.sqrt (1 - (4 * productAnnulusConstantSq d M + 2) * leakageCoefficient κ M)
def reductionDelta (M : ℝ) : ℝ := 1 / (M + 1)
def reductionMtilde (M : ℝ) : ℝ := 5 * M + 3
def phaseAdjustedDifference {d : ℕ} (κ : MultiIndex d) (w : ℂ) (G : FiniteHermiteSum d) :
    CSpace d → ℂ :=
  fun z => w * (nuKappa κ z + evalHermiteSum κ G z) - nuKappa κ z
def phaseAdjustedNormSq {d : ℕ} (κ : MultiIndex d) (w : ℂ) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2NormSq (phaseAdjustedDifference κ w G)
def phaseAdjustedNorm {d : ℕ} (κ : MultiIndex d) (w : ℂ) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2Norm (phaseAdjustedDifference κ w G)
def positiveFrequencyPolynomial (E : Finset ℕ) (b : ℕ → ℂ) : Circle → ℂ :=
  fun t => Finset.sum E fun n => b n * fourier (n : ℤ) t
def bandLimitedPolynomial (N L : ℕ) (c : Fin L → ℂ) : Circle → ℂ :=
  fun t => ∑ m : Fin L, c m * fourier ((N + m.1 : ℕ) : ℤ) t
def HasPositiveFrequencySupport (P : Circle → ℂ) (E : Finset ℕ) : Prop :=
  ∃ b : ℕ → ℂ, P = positiveFrequencyPolynomial E b
def HasBandlimitedSupport (P : Circle → ℂ) (N L : ℕ) : Prop :=
  ∃ c : Fin L → ℂ, P = bandLimitedPolynomial N L c
end Hermite1DimdLEAN


