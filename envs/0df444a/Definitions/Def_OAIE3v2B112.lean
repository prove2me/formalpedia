-- Prove2me | Definitions.Def_OAIE3v2B112
-- name    : OAIE3v2B112
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:39:58.170813+00:00
-- url     : https://prove2.me/theorems/cadfa64f-1b73-4bbf-96a5-7ecca7c893d3
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 114 of 311
-- statement:
--   Definitions bundle 114 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B087`, `OAIE3v2B088`, `OAIE3v2B090`, `OAIE3v2B092`, `OAIE3v2B298`, `OAIE3v2B095`, `OAIE3v2B096`, `OAIE3v2B097`, `OAIE3v2B098`, `OAIE3v2B099`, `OAIE3v2B100` of this split.
--
--   Modules: `Dynamics/AllocatedFixedScaleCollisionBudget.lean`, `Dynamics/PositiveComparisonDataBudget.lean`, `Dynamics/PreparedSameScaleBadProductBudget.lean`, `Dynamics/SampledFullboxDetectionBudget.lean`, `Dynamics/ScalarCubeProductRiemannBudget.lean`, `Estimates/AllocatedFiberCap.lean`, `Estimates/AllocatedPhysicalLongIdealCap.lean`, `Estimates/AllocatedProfileDimensions.lean`, `Estimates/AllocatedTailProfileIdentity.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/CanonicalCoefficientCoverLift.lean`, `Estimates/CanonicalScalarSourceEnvelope.lean`, `Estimates/CoefficientDeckImageCongruence.lean`, `Estimates/ImageExtensionInverseBounds.lean`, `Estimates/LayeredCoverSiteExtension.lean`, `Estimates/LinearLiftSheetCompatibility.lean`, `Estimates/ModularMultilinearAmbientSublevel.lean`, `Estimates/RowRestrictedDeckSiteMask.lean`, `Estimates/ShiftedSmoothProductAmplitudeTransfer.lean`, `Fourier/AllocatedMaskedCoefficientFourier.lean`, `Fourier/FixedPrincipalCoefficientSpectrum.lean`, `Fourier/QuadraticFrequencyCoordinates.lean`, `Fourier/QuadraticLocalFrequency.lean`, `Geometry/AllocatedMaskedChartProduct.lean`, `Geometry/AllocatedPhysicalChartBounds.lean`, `Geometry/AllocatedSupportedSiteApproximation.lean`, `Geometry/CoefficientDeckChartRecovery.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Geometry/PreparedBadProductSpatialBudget.lean`, `Lattices/AllocatedAffineRadiusLog.lean`, `Lattices/AllocatedAffineScaleEnvelope.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/PartitionedAffineLogEnvelope.lean`, `Lattices/SelectedResidueApproximation.lean`, `Lattices/SharedFreeAffineBudget.lean`, `Lattices/SmoothResidueWindowMass.lean`, `Linear/AllocatedModularRankCongruenceOutput.lean`, `Linear/SpatialMatrixBlockWideProbability.lean`, `Polynomial/PreparedPolynomialPhysicalBadProductSource.lean`, `Probability/AllocatedAmbientDensity.lean`, `Probability/CoefficientDeckDensityLawCongruence.lean`, `Probability/EmptyCoefficientDensity.lean`, `Probability/MixedDensityInterpolation.lean`, `Probability/MixedSelectedCoefficientProbability.lean`, `Probability/ScalarCubeDomainDensity.lean`, `Probability/ScaledArrayLaw.lean`, `Sampling/AllocatedProbabilityGrid.lean`, `Sampling/ForecastInactiveSlicedCappedContinuousSource.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B087
import Definitions.Def_OAIE3v2B088
import Definitions.Def_OAIE3v2B090
import Definitions.Def_OAIE3v2B092
import Definitions.Def_OAIE3v2B298
import Definitions.Def_OAIE3v2B095
import Definitions.Def_OAIE3v2B096
import Definitions.Def_OAIE3v2B097
import Definitions.Def_OAIE3v2B098
import Definitions.Def_OAIE3v2B099
import Definitions.Def_OAIE3v2B100

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem gowersNorm_le_succ (j : ℕ) (f : H → ℂ) :
    gowersNorm (j + 1) f ≤ gowersNorm (j + 2) f := by
  let F (ω : Fin (j + 2) → Bool) : H → ℂ := if ω 0 then (fun _ ↦ 1) else f
  have hm : mixedGowersMoment (j + 2) F = gowersMoment (j + 1) f := by
    change (𝔼 h, mixedGowersMoment (j + 1)
      (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h)) = _
    have hd (h : H) :
        (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h) =
        (fun _ : Fin (j + 1) → Bool ↦ f) := by
      funext ω x
      simp [F, crossDerivative]
    simp only [hd, mixedGowersMoment_const, Fintype.expect_const]
  have hp : (∏ ω, gowersNorm (j + 2) (F ω)) = gowersNorm (j + 2) f ^ (2 ^ (j + 1)) := by
    rw [prod_bool_tuple_succ]
    simp [F, gowersNorm_const_one]
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
    (gowersNorm_nonneg (j + 1) f)
  rw [gowersNorm_pow, ← norm_gowersMoment, ← hm]
  exact (norm_mixedGowersMoment_le (j + 1) F).trans_eq hp

theorem norm_expect_le_gowersNorm (j : ℕ) (f : H → ℂ) :
    ‖𝔼 x, f x‖ ≤ gowersNorm (j + 1) f := by
  induction j with
  | zero => exact (gowersNorm_one f).ge
  | succ j ih => exact ih.trans (gowersNorm_le_succ j f)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem gowersNorm_le_of_mean_norm_le_pow (j : ℕ) (f : H → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hmean : (𝔼 x, ‖f x‖) ≤ ε ^ (2 ^ (j + 1))) : gowersNorm (j + 1) f ≤ ε := by
  exact le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hε
    ((gowersNorm_pow_le_mean_norm j f hf).trans hmean)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [Fintype G]

theorem gowersNorm_le_one (s : ℕ) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    gowersNorm (s + 1) f ≤ 1 := by
  apply gowersNorm_le_of_mean_norm_le_pow s f hf (by norm_num)
  simpa only [one_pow, Fintype.expect_const] using
    Finset.expect_le_expect (s := Finset.univ) (fun x _ => hf x)

theorem exists_many_large_gowers_derivatives (s : ℕ) (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {p : ℝ} (hp : 0 ≤ p)
    (hG : Real.exp (-p) ≤ gowersNorm (s + 2) f) :
    ∃ H : Finset G, H.Nonempty ∧
      Real.exp (-derivativeInverseBudget s p) * Fintype.card G ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Real.exp (-derivativeInverseBudget s p) ≤
        gowersNorm (s + 1) (multiplicativeDerivative f h) := by
  let a := Real.exp (-((2 ^ (s + 2) : ℕ) : ℝ) * p)
  have hmean : a ≤ 𝔼 h, gowersNorm (s + 1) (multiplicativeDerivative f h) ^
      (2 ^ (s + 1)) := by
    rw [← gowersNorm_derivative]
    calc
      a = Real.exp (-p) ^ (2 ^ (s + 2)) := by
        dsimp [a]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hG _
  have hunit (h : G) : gowersNorm (s + 1) (multiplicativeDerivative f h) ≤ 1 :=
    gowersNorm_le_one s _ (multiplicativeDerivative_norm_le_one f hf h)
  obtain ⟨H, hcard, hlarge⟩ := exists_dense_level_set
    (fun h => gowersNorm (s + 1) (multiplicativeDerivative f h) ^ (2 ^ (s + 1)))
    (Real.exp_nonneg _) (fun h => pow_le_one₀ (gowersNorm_nonneg s _) (hunit h)) hmean
  have hsmall : Real.exp (-derivativeInverseBudget s p) ≤ a / 2 := by
    calc
      _ ≤ Real.exp (-((2 ^ (s + 2) : ℕ) : ℝ) * p - 1) := by
        apply Real.exp_le_exp.mpr
        unfold derivativeInverseBudget
        linarith
      _ ≤ _ := exp_sub_one_le_half_exp _
  have hdense : Real.exp (-derivativeInverseBudget s p) * Fintype.card G ≤
      (H.card : ℝ) :=
    (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)).trans hcard
  have hnonempty : H.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    exact_mod_cast (mul_pos (Real.exp_pos _) hpos).trans_le hdense
  refine ⟨H, hnonempty, hdense, fun h hh => ?_⟩
  exact exp_neg_le_of_pow (gowersNorm_nonneg s _)
    (by linarith [derivativeInverseBudget_ge_two s hp])
    (pow_ne_zero _ (by norm_num)) (hsmall.trans (hlarge h hh))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDomainDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomainDensity_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeDomainDensity α := inv_pos.mpr (scalarCubeDomain_volumeReal_pos α)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothProductAmplitudeTransfer
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

theorem shiftedSmoothProductPMF_shift_transfer_amplitude {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (shift : X → I → ℤ) {r β : ℝ}
    (hshift : ∀ u, ‖rectangularLatticePoint 0 S (shift u)‖ ≤ r)
    (f : (I → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ β)
    (F : (I → ℤ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {η : ℝ} (hvariation : ∀ x u, ‖F (x + shift u) - F x‖ ≤ η) :
    ‖∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) * (F x * f x)‖ ≤
      4 * (3 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r + η + β := by
  have hproduct (x) : ‖F x * f x‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hF x) (hf x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hlocalProduct (x) : ‖𝔼 u, F (x + shift u) * f (x + shift u)‖ ≤ η + β :=
    norm_local_average_amplitude_le (fun u => x + shift u) f F x hf (hF x) (hvariation x) (hlocal x)
  simpa only [add_assoc] using shiftedSmoothProductPMF_shift_transfer a S hS hZ hS1
    hδ hδ1 hmesh hsmall shift hshift (fun x => F x * f x) hproduct hlocalProduct

theorem shiftedSmoothProductPMF_shift_transfer_lipschitz_amplitude {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hS1 : ∀ i, 1 ≤ S i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card I *
      ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    (shift : X → I → ℤ) {r β : ℝ}
    (hshift : ∀ u, ‖rectangularLatticePoint 0 S (shift u)‖ ≤ r)
    (f : (I → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ β)
    (F : (I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F) :
    ‖∑' x, ((shiftedSmoothProductPMF a S hS hZ x).toReal : ℂ) *
      (F (rectangularLatticePoint a S x) * f x)‖ ≤
      4 * (3 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) * probabilityProfileLipschitz) * r +
        (Lip : ℝ) * r + β := by
  exact shiftedSmoothProductPMF_shift_transfer_amplitude a S hS hZ hS1 hδ hδ1 hmesh hsmall
    shift hshift f hf hlocal (fun x => F (rectangularLatticePoint a S x)) (fun _ => hF _)
    (fun x u => normalizedSpatialAmplitude_shift_le_of_norm_le F hLip a S x (shift u) (hshift u))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem residue_smooth_row_shift_transfer_lipschitz_amplitude {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] {h : ℕ}
    (N modulus : I → ℕ) (hN : ∀ j, 0 < N j) (hmodulus : ∀ j, 0 < modulus j)
    (rows : Fin h → K → ℤ) (residue : K × I → ℤ)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth modulus V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ z, 1 / residueProfileWidth modulus V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (K × I) *
      ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {C r B : ℝ} (hC : 0 ≤ C) (hrows : ∀ i k, |(rows i k : ℝ)| ≤ C) (hr : 0 ≤ r)
    (hmove : ∀ z, (h : ℝ) * C * ((modulus z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (Φ : (K → I → ℝ) → ℂ) (hΦ : ∀ b, ‖Φ b‖ ≤ 1)
    (hlocal : ∀ b : K → I → ℝ,
      ‖𝔼 x : Fin h → ∀ j, Fin (N j),
        Φ (rowShiftedTuple b rows
          (fun (y : ∀ j, Fin (N j)) j => (modulus j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ B)
    (F : (K × I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F) :
    ‖∑' x, ((residueSmoothIndexPMF residue modulus hmodulus V hV hZ x).toReal : ℂ) *
      (F (fun z => (residueLatticeArray residue modulus x z : ℝ) / V z) *
        Φ (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ)))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (K × I) *
        ((Fintype.card (K × I) : ℝ) * probabilityProfileLipschitz) * r + (Lip : ℝ) * r + B := by
  let : ∀ j, Nonempty (Fin (N j)) := fun j => ⟨⟨0, hN j⟩⟩
  have ht := shiftedSmoothProductPMF_shift_transfer_lipschitz_amplitude
    (residueProfileCenter residue modulus)
    (residueProfileWidth modulus V) (residueProfileWidth_pos modulus V hmodulus hV)
    hZ hV1 hδ hδ1 hmesh hsmall (integerRowShift (N := N) rows (fun _ => 1))
    (fun x => residueRowShift_normalized_bound rows modulus hmodulus x V hV hC hrows hr hmove)
    (fun x => Φ (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ)))
    (fun _ => hΦ _) (fun x => by
      simpa only [residueLatticeArray_rowShift] using
        hlocal (fun k j => (residueLatticeArray residue modulus x (k, j) : ℝ))) F hF hLip
  simpa only [residueSmoothIndexPMF, residueProfile_point residue modulus hmodulus V hV]
    using ht

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass
namespace OAI

section

namespace Erdos3

theorem selectedResidueDensityPMF_toReal {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (x : K × I → ℤ) :
    (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal =
      (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * D x /
        selectedResidueDensityMass modulus G V D := by
  unfold selectedResidueDensityMass at hD ⊢
  simp only [selectedResidueDensityPMF, finiteDensityTiltPMF_toReal, selectedResidueSmoothPMF_toReal]

theorem selectedResidueDensityPMF_error {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (f : (K × I → ℤ) → ℂ)
    {a : ℂ} {E ε B : ℝ} (hlower : 1 / 2 ≤ selectedResidueDensityMass modulus G V D)
    (herror : ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
      ((D x : ℂ) * f x)) - a‖ ≤ E)
    (hmass : |selectedResidueDensityMass modulus G V D - 1| ≤ ε) (hcap : ‖a‖ ≤ B) :
    ‖(∑' x, ((selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal : ℂ) * f x) - a‖ ≤
      2 * E + 2 * B * ε := by
  rw [selectedResidueDensityPMF_complexMean]
  exact complex_normalization_error hlower herror hmass hcap

end Erdos3

end

section

namespace Erdos3

theorem selectedResidueDensityPMF_zero_of_density_zero {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (x : K × I → ℤ) (hx : D x = 0) :
    (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal = 0 := by
  rw [selectedResidueDensityPMF_toReal, hx, mul_zero, zero_div]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueDensityPMF_mean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (f : (K × I → ℤ) → ℝ) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal * f x) =
      (∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * (D x * f x)) /
        selectedResidueDensityMass modulus G V D := by
  simp only [selectedResidueDensityPMF_toReal, div_mul_eq_mul_div, mul_assoc, tsum_div_const]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageExtensionInverseBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]

theorem exp_le_gowers_imageExtension (j : ℕ) (φ : A →+ B) (Q : Finset A)
    (hφ : ReflectsPairSums φ (Q : Set A)) (f : A → ℂ) {p q : ℝ}
    (hQ : Real.exp (-q) ≤ (Q.card : ℝ) / Fintype.card B)
    (hf : Real.exp (-p) ≤ finiteSupportGowersNorm (j + 1) Q f) :
    Real.exp (-(p + q)) ≤ gowersNorm (j + 1) (imageExtension φ Q f) := by
  classical
  have hm := norm_expect_le_gowersNorm j (restrictTo (Q.image φ) (fun _ => (1 : ℂ)))
  rw [norm_expect_restrict_one, Finset.card_image_of_injOn hφ.injOn] at hm
  have hd := hQ.trans hm
  have hdpos := lt_of_lt_of_le (Real.exp_pos (-q)) hd
  rw [finiteSupportGowersNorm_eq_restricted hφ, restrictedGowersNorm, restrictTo_imageExtension] at hf
  have hprod := (le_div_iff₀ hdpos).mp hf
  calc
    _ = Real.exp (-p) * Real.exp (-q) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-p) * gowersNorm (j + 1) (restrictTo (Q.image φ) (fun _ => (1 : ℂ))) :=
      mul_le_mul_of_nonneg_left hd (Real.exp_nonneg _)
    _ ≤ _ := hprod

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearLiftSheetCompatibility
namespace OAI

section

namespace Erdos3

open Module Submodule

theorem standardLatticeIntegerLift_sheet {D J : Type*} [Fintype D] [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (bP : Basis J ℝ Wᗮ)
    (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (z : J → ℤ) (u : W) :
    latticeSheetQuotient (standardEuclideanLattice D) W
      (latticeBasisEquiv (projectedIntegerLattice W) bP hP z) u =
      QuotientAddGroup.mk (u - W.orthogonalProjectionOnto (standardLatticeIntegerLift W bP hP z).val) := by
  apply latticeSheetQuotient_eq_of_lift
  exact (standardLatticeIntegerLift_projection W bP hP z).trans
    (latticeBasisEquiv_synthesis (projectedIntegerLattice W) bP hP z).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped ContDiff

theorem normalizedIntegerPMF_cap (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) (k : ℤ) :
    K * (normalizedIntegerPMF K c δ hK hδ hlarge k).toReal ≤ 2 / δ := by
  have hb := shiftedSmoothCoefficientPMF_le (c * K) hlarge k
  calc
    _ ≤ K * (2 / (δ * K)) := mul_le_mul_of_nonneg_left hb hK.le
    _ = 2 / δ := by field_simp

end Erdos3

end

section

namespace Erdos3

theorem constantIntegerPMF_cap (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) (k : ℤ) :
    K * (constantIntegerPMF K δ hK hδ k).toReal ≤
      8 * (probabilityProfileLipschitz : ℝ) / δ := by
  by_cases hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K
  · rw [constantIntegerPMF_large K δ hK hδ hlarge]
    refine (normalizedIntegerPMF_cap K 0 δ hK hδ hlarge k).trans ?_
    apply div_le_div_of_nonneg_right _ hδ.le
    have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
    linarith
  · have hKbound := (constantIntegerPMF_small K δ hK hδ (lt_of_not_ge hlarge)).2
    have hp : (constantIntegerPMF K δ hK hδ k).toReal ≤ 1 := by
      simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top ((constantIntegerPMF K δ hK hδ).coe_le_one k)
    exact (mul_le_mul_of_nonneg_left hp hK.le).trans (by simpa only [mul_one] using hKbound.le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedDensityInterpolation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem constantCoefficientDensity_cap {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (K δ : J → ℝ)
    (hK : ∀ j, 0 < K j) (hδ : ∀ j, 0 < δ j) {v B : ℝ}
    (hB : 0 ≤ B) (hvolume : v ≤ B * ∏ j, K j) (x : (I → ℝ) × (J → ℤ)) :
    v * constantCoefficientDensity w K δ hK hδ x ≤
      B * profileWidthFactor w * ∏ j, (8 * (probabilityProfileLipschitz : ℝ) / δ j) := by
  let p : J → PMF ℤ := fun j => constantIntegerPMF (K j) (δ j) (hK j) (hδ j)
  let f := affineProductProfile (fun _ => 0) w x.1
  have hf0 : 0 ≤ f := affineProductProfile_nonneg _ w hw x.1
  have hfcap : f ≤ profileWidthFactor w := by
    exact (le_abs_self f).trans (affineProductProfile_norm_le (fun _ => 0) w hw x.1)
  have hg0 : 0 ≤ ∏ j, (p j (x.2 j)).toReal :=
    Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hscaled0 : 0 ≤ ∏ j, K j * (p j (x.2 j)).toReal :=
    Finset.prod_nonneg (fun j _ => mul_nonneg (hK j).le ENNReal.toReal_nonneg)
  have hscaled : (∏ j, K j * (p j (x.2 j)).toReal) ≤
      ∏ j, (8 * (probabilityProfileLipschitz : ℝ) / δ j) :=
    Finset.prod_le_prod (fun j _ => mul_nonneg (hK j).le ENNReal.toReal_nonneg)
      (fun j _ => constantIntegerPMF_cap (K j) (δ j) (hK j) (hδ j) (x.2 j))
  change v * (f * ∏ j, (p j (x.2 j)).toReal) ≤ _
  calc
    _ ≤ (B * ∏ j, K j) * (f * ∏ j, (p j (x.2 j)).toReal) :=
      mul_le_mul_of_nonneg_right hvolume (mul_nonneg hf0 hg0)
    _ = B * (f * ∏ j, K j * (p j (x.2 j)).toReal) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ ≤ B * (profileWidthFactor w * ∏ j, (8 * (probabilityProfileLipschitz : ℝ) / δ j)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hfcap hscaled hscaled0 (profileWidthFactor_pos w hw).le) hB
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedLatticeQuotient_linear_lift (x : W × (Fin n → ℤ)) :
    normalizedLatticeQuotient W b hb x =
      QuotientAddGroup.mk (x.1 - W.orthogonalProjectionOnto
        (standardLatticeIntegerLift W b hb x.2).val) :=
  standardLatticeIntegerLift_sheet W b hb x.2 x.1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledArrayLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

theorem canonicalMixedDensity_recover (c w : I → ℝ) (p : Fin n → PMF ℤ)
    {y : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup}
    (hy : canonicalMixedDensity W b hb o c w p y ≠ 0) :
    ∃ x : (I → ℝ) × (Fin n → ℤ),
      normalizedLatticePoint W b (orthonormalMixedChart o x) ∈ standardLatticeSmallBox D ∧
      normalizedLatticeQuotient W b hb (orthonormalMixedChart o x) = y ∧
      mixedCoefficientDensity c w p x ≠ 0 := by
  obtain ⟨x, hx, hq, hf⟩ := normalizedQuotientDensity_recover W b hb (Subset.rfl)
    (orthonormalMixedDensity o c w p) hy
  refine ⟨(orthonormalMixedChart o).symm x, ?_, ?_, hf⟩
  · simpa only [MeasurableEquiv.apply_symm_apply] using hx
  · simpa only [MeasurableEquiv.apply_symm_apply] using hq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EmptyCoefficientDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

theorem canonicalArrayDensity_recover (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ)
    {y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup}
    (hy : canonicalArrayDensity W b hb o c w p y ≠ 0) :
    ∃ x : (I → J → ℝ) × (Fin n → J → ℤ),
      mixedArrayQuotient W b hb o x = y ∧ mixedArrayInChart W b o x ∧ mixedArraySupported c w p x := by
  classical
  have hs (j : J) := canonicalMixedDensity_recover W b hb o (fun i => c i j)
    (fun i => w i j) (fun i => p i j) ((Finset.prod_ne_zero_iff.mp hy) j (Finset.mem_univ j))
  choose a hac haq has using hs
  let x := (mixedArrayRegroup I (Fin n) J).symm a
  have hx : mixedArrayRegroup I (Fin n) J x = a := (mixedArrayRegroup I (Fin n) J).apply_symm_apply a
  refine ⟨x, ?_, ?_, ?_⟩
  · funext j
    change normalizedLatticeQuotient W b hb (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j)) = y j
    rw [hx]
    exact haq j
  · intro j
    change normalizedLatticePoint W b (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j)) ∈ _
    rw [hx]
    exact hac j
  · intro j
    rw [hx]
    exact has j

theorem canonicalArrayDensity_recover_unique (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ)
    {y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup}
    (hy : canonicalArrayDensity W b hb o c w p y ≠ 0) :
    ∃! x : (I → J → ℝ) × (Fin n → J → ℤ),
      mixedArrayQuotient W b hb o x = y ∧ mixedArrayInChart W b o x ∧ mixedArraySupported c w p x := by
  obtain ⟨x, hx⟩ := canonicalArrayDensity_recover W b hb o c w p hy
  refine ⟨x, hx, ?_⟩
  intro z hz
  exact mixedArrayQuotient_injOn_chart W b hb o hz.2.1 hx.2.1 (hz.1.trans hx.1.symm)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

theorem canonicalCoefficientDensity_recover_unique
    {y : CoefficientTorus (K := K) U} (hy : canonicalCoefficientDensity U b hb o c w p y ≠ 0) :
    ∃! a : CoefficientSamplerArrays (K := K) I n,
      canonicalCoefficientSample U b hb o a = y ∧
        ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (a j) ∧
          mixedArraySupported (c j) (w j) (p j) (a j) := by
  classical
  have hs (j : Fin m) := canonicalArrayDensity_recover_unique
    (euclideanSubspace (U j)) (b j) (hb j) (o j) (c j) (w j) (p j)
    ((Finset.prod_ne_zero_iff.mp hy) j (Finset.mem_univ j))
  choose a ha hu using hs
  refine ⟨a, ⟨?_, fun j => (ha j).2⟩, ?_⟩
  · apply (euclideanCoefficientEquiv U).injective
    rw [canonicalCoefficientSample, AddEquiv.apply_symm_apply]
    exact funext (fun j => (ha j).1)
  · intro z hz
    have hq := congrArg (euclideanCoefficientEquiv U) hz.1
    rw [canonicalCoefficientSample, AddEquiv.apply_symm_apply] at hq
    exact funext (fun j => hu j (z j) ⟨congrFun hq j, hz.2 j⟩)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeProductRiemannBudget
namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem scalarCubeRiemannBoundary_le_exp (α : Type*) [Fintype α] [DecidableEq α]
    {D : ℝ} (_hD : 0 ≤ D) (hcard : (Fintype.card α : ℝ) ≤ D) :
    scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) ≤
      Real.exp (scalarCubeRiemannLog D) := by
  let q := Fintype.card α
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h2q : (2 : ℝ) ^ q ≤ Real.exp q := by
    simpa only [← Real.exp_nat_mul, mul_one] using pow_le_pow_left₀ (by norm_num) h2 q
  have h4q : (4 : ℝ) ^ q ≤ Real.exp (2 * q) := by
    simpa only [← Real.exp_nat_mul, mul_comm] using pow_le_pow_left₀ (by norm_num) h4 q
  have hb : scalarCubeGridBoundaryConstant α ≤ Real.exp (4 * q + 2) := by
    simp only [scalarCubeGridBoundaryConstant, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_finset, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    calc
      _ ≤ (Real.exp 1 * Real.exp q) * Real.exp (2 * q) * Real.exp 1 * Real.exp q := by
        gcongr
        exact Real.add_one_le_exp _
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  calc
    _ = scalarCubeGridBoundaryConstant α * scalarCubeDomainDensity α := by
      rw [div_eq_mul_inv]; rfl
    _ ≤ Real.exp (4 * q + 2) * Real.exp (((q : ℝ) + 1) ^ 2) :=
      mul_le_mul hb (scalarCubeDomainDensity_le_exp α)
        (scalarCubeDomainDensity_pos α).le (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp only [scalarCubeRiemannLog]
      have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
      change (q : ℝ) ≤ D at hcard
      nlinarith [sq_nonneg (D - q)]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

theorem progressionSlice_scale_bounds
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    {D E F T δ : ℝ} {S modulus : ℕ} (H step : ι → ℕ) (c : ι → ℤ)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (_hF : 0 ≤ F) (hT : 0 ≤ T)
    (hcard : (Fintype.card ι : ℝ) ≤ D) (hq : (Fintype.card α : ℝ) ≤ D)
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (hm : 0 < modulus) (hmT : (modulus : ℝ) ≤ Real.exp T)
    (hS : Real.exp (progressionSliceLengthLog D E F T) ≤ S)
    (hstep : ∀ j, 0 < step j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ))
    (hdense : ∀ j, δ * S ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ)) :
    (∀ j, 2 ≤ H j) ∧
    (∀ j, (Fintype.card α + 1) * modulus ≤ H j) ∧
    (∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α)) ∧
    (∑ j, (modulus : ℝ) / H j) ≤ Real.exp (-E) ∧
    (∀ j, (step j : ℝ) / S ≤ Real.exp (-E)) := by
  let B := scalarCubeRiemannLog D
  have hB : 0 ≤ B := by dsimp [B, scalarCubeRiemannLog]; positivity
  have hS0 : (0 : ℝ) < S := (Real.exp_pos _).trans_le hS
  have hSpos : 0 < S := by exact_mod_cast hS0
  have hδlow : Real.exp (-F) ≤ δ := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos F) hδ).mpr hδF
  have hHlow (j : ι) : Real.exp (E + T + D + B + 5) ≤ (H j : ℝ) := by
    calc
      _ = Real.exp (-F) * Real.exp (progressionSliceLengthLog D E F T) := by
        rw [← Real.exp_add]; dsimp [progressionSliceLengthLog, B]; congr 1; ring
      _ ≤ δ * S := mul_le_mul hδlow hS (Real.exp_nonneg _) hδ.le
      _ ≤ _ := by simpa only [card_integerProgressionSupport _ _ _ (hstep j)] using hdense j
  have hH2 (j : ι) : 2 ≤ H j := by
    have he : (2 : ℝ) ≤ Real.exp (E + T + D + B + 5) := by
      linarith [Real.add_one_le_exp (E + T + D + B + 5)]
    exact_mod_cast he.trans (hHlow j)
  have hHp (j : ι) : (0 : ℝ) < H j := (Real.exp_pos _).trans_le (hHlow j)
  have hr (j : ι) : (modulus : ℝ) / H j ≤ Real.exp (-(E + D + B + 5)) := by
    calc
      _ ≤ Real.exp T / Real.exp (E + T + D + B + 5) :=
        div_le_div₀ (Real.exp_nonneg _) hmT (Real.exp_pos _) (hHlow j)
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  have hcancel (a : ℝ) : Real.exp a * Real.exp (-(E + D + B + 5)) =
      Real.exp (a - (E + D + B + 5)) := by rw [← Real.exp_add]; rfl
  refine ⟨hH2, ?_, ?_, ?_, ?_⟩
  · intro j
    have hc : (Fintype.card α : ℝ) + 1 ≤ Real.exp D :=
      by linarith [Real.add_one_le_exp D]
    have hratio : ((Fintype.card α : ℝ) + 1) * ((modulus : ℝ) / H j) ≤ 1 := by
      calc
        _ ≤ Real.exp D * Real.exp (-(E + D + B + 5)) :=
          mul_le_mul hc (hr j) (div_nonneg (Nat.cast_nonneg _) (hHp j).le) (Real.exp_nonneg _)
        _ ≤ 1 := by rw [hcancel]; apply Real.exp_le_one_iff.mpr; linarith
    rw [← mul_div_assoc] at hratio
    have hn := (div_le_one (hHp j)).mp hratio
    exact_mod_cast hn
  · intro j
    have hb := scalarCubeRiemannBoundary_le_exp α hD hq
    have hx : (scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α)) *
        ((modulus : ℝ) / H j) < 1 := by
      calc
        _ ≤ Real.exp B * Real.exp (-(E + D + B + 5)) :=
          mul_le_mul hb (hr j) (div_nonneg (Nat.cast_nonneg _) (hHp j).le) (Real.exp_nonneg _)
        _ < 1 := by rw [hcancel]; apply Real.exp_lt_one_iff.mpr; linarith
    apply (div_lt_one (scalarCubeDomain_volumeReal_pos α)).mp
    simpa only [div_mul_eq_mul_div] using hx
  · calc
      _ ≤ ∑ _j : ι, Real.exp (-(E + D + B + 5)) := Finset.sum_le_sum (fun j _ => hr j)
      _ = (Fintype.card ι : ℝ) * Real.exp (-(E + D + B + 5)) := by simp
      _ ≤ Real.exp D * Real.exp (-(E + D + B + 5)) := by
        gcongr
        exact hcard.trans (by linarith [Real.add_one_le_exp D])
      _ ≤ _ := by rw [hcancel]; apply Real.exp_le_exp.mpr; linarith
  · intro j
    have hg := progression_slice_endpoint_geometry (c j) hSpos (hstep j) (hH2 j) hδ
      (hsubset j) (hdense j)
    have hHreal : (2 : ℝ) ≤ H j := by exact_mod_cast hH2 j
    have hmesh : (step j : ℝ) / S ≤ 4 * ((modulus : ℝ) / H j) := by
      apply hg.2.2.2.trans
      apply (div_le_iff₀ (by linarith : 0 < (H j : ℝ) - 1)).mpr
      rw [show 4 * ((modulus : ℝ) / H j) * ((H j : ℝ) - 1) =
        (4 * modulus * ((H j : ℝ) - 1)) / H j by ring]
      apply (le_div_iff₀ (hHp j)).mpr
      have hm1 : (1 : ℝ) ≤ modulus := by exact_mod_cast hm
      have hprod := mul_le_mul_of_nonneg_right hm1 (by linarith : 0 ≤ (H j : ℝ) - 1)
      nlinarith
    calc
      _ ≤ 4 * ((modulus : ℝ) / H j) := hmesh
      _ ≤ Real.exp 3 * Real.exp (-(E + D + B + 5)) := by
        gcongr
        · linarith [Real.add_one_le_exp (3 : ℝ)]
        · exact hr j
      _ ≤ _ := by rw [hcancel]; apply Real.exp_le_exp.mpr; linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

theorem principalIntervalWeight_grid (k : ℤ) :
    principalIntervalWeight K T γ (fun _ => (k : ℝ) / principalIntervalLength K T γ) =
      (principalIntervalLength K T γ : ℝ) *
        (principalIntegerPMF K T γ hK hT hγ hlarge k).toReal := by
  have hL : (principalIntervalLength K T γ : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.ne_of_gt (principalIntervalLength_pos hK hT hγ))
  have hQ := (div_pos hK hT).ne'
  unfold principalIntervalWeight
  rw [show (principalIntervalLength K T γ : ℝ) / (K / T) *
      ((k : ℝ) / principalIntervalLength K T γ) = (k : ℝ) / (K / T) by field_simp]
  rw [normalizedIntegerInterpolation_grid (K / T) (3 * γ / 2) (γ / 2)
    (div_pos hK hT) (by positivity) hlarge k]
  change _ = (principalIntervalLength K T γ : ℝ) *
    (normalizedIntegerPMF (K / T) (3 * γ / 2) (γ / 2) _ _ _ k).toReal
  field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedAmbientDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedCoefficientAmbientDensity :
    (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → UnitAddCircle) → ℝ :=
  coefficientAmbientDensity U b o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerInterpolation B U b S)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedMaskedCoefficientFourier
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem allocatedCoefficientAmbientDensity_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) :
    let A := allocatedAmbientFactorCap (G := G) B R σ S.value V
    let L := allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V
    let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    (∀ x, 0 ≤ allocatedCoefficientAmbientDensity B U b o S x ∧
      allocatedCoefficientAmbientDensity B U b o S x ≤ (A : ℝ)^N) ∧
    LipschitzWith (N * L * A^N) (allocatedCoefficientAmbientDensity B U b o S) := by
  have h := allocatedAmbientFactor_bounds B U b S o C V hC hV hR hσ
  exact coefficientAmbientDensity_bounds U b o _ _ _
    (allocatedAmbientFactorCap_one_le (G := G) B R σ S.value V)
    (fun s x => (h s).1 x) (fun s => (h s).2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem allocatedMaskedFourierBudget_bounds (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    let Q := allocatedFourierLogBudget m P
    let Ps := allocatedMaskedFourierBudget m P
    0 ≤ Ps ∧ P ≤ Ps ∧ (4 * Q + 2) ^ 4 ≤ Ps ∧
      4 * Q * (4 * Q + 2) ^ 4 + Q ≤ Ps := by
  have hQ := allocatedFourierLogBudget_nonneg m hP
  have hF : 0 ≤ (4 * allocatedFourierLogBudget m P + 2) ^ 4 := by positivity
  have hM : 0 ≤ 4 * allocatedFourierLogBudget m P *
      (4 * allocatedFourierLogBudget m P + 2) ^ 4 + allocatedFourierLogBudget m P := by positivity
  dsimp only [allocatedMaskedFourierBudget]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem exists_allocatedMaskedFourierBudget_bound (m A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      allocatedMaskedFourierBudget m P ≤ (P + C) ^ C ∧
      (allocatedMaskedFourierBudget m P + A) ^ A ≤ (P + C) ^ C := by
  obtain ⟨b, _, hb⟩ := exists_allocatedFourierLogBudget_bound m
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C b) ^ b
  let f : Polynomial ℕ := Polynomial.X + (4 * q + 2) ^ 4 + (4 * q * (4 * q + 2) ^ 4 + q)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (f + (f + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro P hP
  let F : ℝ := P + (4 * (P + b) ^ b + 2) ^ 4 +
    (4 * (P + b) ^ b * (4 * (P + b) ^ b + 2) ^ 4 + (P + b) ^ b)
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hPs0 := (allocatedMaskedFourierBudget_bounds m hP).1
  have hPs : allocatedMaskedFourierBudget m P ≤ F := by
    have hQ := allocatedFourierLogBudget_nonneg m hP
    have hQB := hb P hP
    dsimp only [allocatedMaskedFourierBudget, F]
    gcongr
  have hpow : (allocatedMaskedFourierBudget m P + A) ^ A ≤ (F + A) ^ A := by gcongr
  have hpow0 : 0 ≤ (F + A) ^ A := by positivity
  have htotal : F + (F + A) ^ A ≤ (P + C) ^ C := by
    simpa [F, f, q, Polynomial.eval₂_pow] using hbound P hP
  exact ⟨by linarith, by linarith⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCoefficientCoverLift
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedLatticeRepresentative_mk (x : W × (Fin n → ℤ)) :
    (QuotientAddGroup.mk (normalizedLatticeRepresentative W b hb x) :
      W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
      normalizedLatticeQuotient W b hb x :=
  (normalizedLatticeQuotient_linear_lift W b hb x).symm

theorem normalizedCoverLift_projection (d : ℕ) (hd : 0 < d) (x : W × (Fin n → ℤ)) :
    quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d
        (normalizedCoverLift W b hb d x) = normalizedLatticeQuotient W b hb x := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  change quotientIntegerCover _ d (QuotientAddGroup.mk' _
    ((d : ℝ)⁻¹ • normalizedLatticeRepresentative W b hb x)) = _
  rw [quotientIntegerCover_mk, smul_smul, mul_inv_cancel₀ hd0, one_smul]
  exact normalizedLatticeRepresentative_mk W b hb x

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [Fintype K] in
theorem canonicalCoefficientCoverLift_projection (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) :
    quotientIntegerCover (coefficientIntegerLattice U) d
        (canonicalCoefficientCoverLift U b hb o d x) = canonicalCoefficientSample U b hb o x := by
  apply (euclideanCoefficientEquiv U).injective
  change euclideanCoefficientEquiv U (d • canonicalCoefficientCoverLift U b hb o d x) = _
  rw [map_nsmul, canonicalCoefficientCoverLift, AddEquiv.apply_symm_apply,
    canonicalCoefficientSample, AddEquiv.apply_symm_apply]
  funext j e
  exact normalizedCoverLift_projection (euclideanSubspace (U j)) (b j) (hb j) d hd _

theorem canonicalCoefficientCoverLift_measurable
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (d : ℕ) : Measurable (canonicalCoefficientCoverLift (K := K) U b hb o d) := by
  apply (euclideanCoefficientMeasurableEquiv U).symm.measurable.comp
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro e
  exact (normalizedCoverLift_continuous (euclideanSubspace (U j)) (b j) (hb j) d).measurable.comp
    ((orthonormalMixedChart (o j)).measurable.comp ((measurable_pi_apply e).comp
      ((mixedArrayRegroup _ _ _).measurable.comp (measurable_pi_apply j))))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiberCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientConstantCenter_continuous :
    Continuous (coefficientConstantCenter (K := K) U) :=
  (constantCoefficientTorusMap_continuous U).comp (coefficientEvaluationTorus_continuous U 0)

omit [∀ j, Fintype (J j)] in
theorem coefficientConstantCenter_add_constant
    (x : CoefficientTorus (K := K) U) (y : CoefficientTorus (K := Empty) U) :
    coefficientConstantCenter U (x + constantCoefficientTorusMap U y) =
      coefficientConstantCenter U x + constantCoefficientTorusMap U y := by
  simp only [coefficientConstantCenter, AddMonoidHom.comp_apply, map_add,
    coefficientEvaluationTorus_constant]

omit [∀ j, Fintype (J j)] in
theorem coefficientConstantCenter_integral_add_constant
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant]
    (D : CoefficientTorus (K := K) U → ℝ) (y : CoefficientTorus (K := Empty) U) :
    (∫ c, D (coefficientConstantCenter U c + constantCoefficientTorusMap U y) ∂μ) =
      ∫ c, D (coefficientConstantCenter U c) ∂μ := by
  simpa only [add_comm (constantCoefficientTorusMap U y), coefficientConstantCenter_add_constant] using
    integral_add_left_eq_self (μ := μ) (fun c => D (coefficientConstantCenter U c))
      (constantCoefficientTorusMap U y)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))

omit [∀ j, Fintype (J j)] in
theorem exists_subtractive_constant_center (x : CoefficientTorus (K := K) U) :
    ∃ c : ∀ j, U j, coefficientConstantCenter U x =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray (K := K) U (fun s => c s.1))) := by
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U)
    (-(coefficientEvaluationTorus U 0 x))
  let c := fun j => v ⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩
  have hc : (fun s : CoefficientSlot Empty m => c s.1) = v := by
    funext s
    rcases s with ⟨j,d⟩
    rw [emptyCoefficientExponent_eq (j.val + 1) d]
  refine ⟨c, ?_⟩
  rw [← constantCoefficientTorusMap_mk, hc, hv, map_neg, neg_neg]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientDeckImageCongruence
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [Fintype K] in
theorem canonicalCoefficientDeckSample_projection (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d) :
    quotientIntegerCover (coefficientIntegerLattice (K := K) U) d
        (canonicalCoefficientDeckSample U bW b hb o d hd x r) = canonicalCoefficientSample U b hb o x := by
  rw [canonicalCoefficientDeckSample, map_add, canonicalCoefficientCoverLift_projection U b hb o d hd,
    (coefficientDeckKernelEquiv U bW d hd r).property, add_zero]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientDeckDensityLawCongruence
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

noncomputable def coefficientDeckJetDensity (d : ℕ) [NeZero d]
    (r : ∀ j, O j → B j → ZMod d) : ℝ :=
  (Fintype.card (∀ j, O j → B j → ZMod d) : ℝ) *
    (((PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
      (coefficientDeckJetMap root A rows d)) r).toReal

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical
attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientDeckSample_injOn_chart (q : ℕ) (hq : 0 < q) :
    Set.InjOn (fun z : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) E q =>
      canonicalCoefficientDeckSample U bW b hb o q hq z.1 z.2)
      {z | ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (z.1 j)} := by
  rintro ⟨x, r⟩ hx ⟨y, s⟩ hy h
  have hp := congrArg (quotientIntegerCover (coefficientIntegerLattice (K := K) U) q) h
  simp only [canonicalCoefficientDeckSample_projection] at hp
  have hxy := canonicalCoefficientSample_injOn_chart U b hb o hx hy hp
  change x = y at hxy
  subst y
  have hrs := canonicalCoefficientDeckSample_residue_injective U bW b hb o q hq x h
  change r = s at hrs
  subst s
  rfl

theorem canonicalCoefficientDeckSample_injOn_smallAmbient (q : ℕ) (hq : 0 < q) :
    Set.InjOn (fun z : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) E q =>
      canonicalCoefficientDeckSample U bW b hb o q hq z.1 z.2)
      {z | ∀ a, |coefficientSamplerAmbientPoint U b o z.1 a| < 1/2} := by
  intro x hx y hy h
  apply canonicalCoefficientDeckSample_injOn_chart U bW b hb o q hq _ _ h
  · intro j e i
    exact hx ⟨⟨j, e⟩, i⟩
  · intro j e i
    exact hy ⟨⟨j, e⟩, i⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LayeredCoverSiteExtension
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix NNReal Classical

variable {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (q : ℕ) [NeZero q]

omit [DecidableEq D] in
theorem exists_normalized_representative_offset (u : W) (x : W × (Fin n → ℤ))
    (hu : (QuotientAddGroup.mk u : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
      normalizedLatticeQuotient W b hb x) :
    ∃ w : I → ℤ, normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val = u := by
  have hmem : u - normalizedLatticeRepresentative W b hb x ∈
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
    QuotientAddGroup.eq_iff_sub_mem.mp (hu.trans (normalizedLatticeRepresentative_mk W b hb x).symm)
  let c : latticeSection (standardEuclideanLattice D) W := ⟨u - normalizedLatticeRepresentative W b hb x, hmem⟩
  refine ⟨bW.equivFun c, ?_⟩
  rw [LinearEquiv.symm_apply_apply]
  change _ + (u - _) = u
  abel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredRowsSiteValue (y : EuclideanJetLayers U rows) (s : Finset α) :
    EuclideanJetLayers U (fun _ => Unit) :=
  fun j _ => ∑ t, rowRestrictedSiteMatrix (rowSets j) s t • y j t

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget
namespace OAI

section

namespace Erdos3

open CyclicCrootSisask

theorem exists_quadratic_affine_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let P := 1024 * (p + 1)
      P + properAffineRecoveryLogLoss P 1 ≤ (p + C) ^ C ∧
        properAffineRankBound P 1 ≤ (p + C) ^ C ∧ P ≤ (p + C) ^ C := by
  let c := ⌈max quarticBogolyubovProgressionConstant quarticBogolyubovConstant⌉₊
  have hc₀ : quarticBogolyubovProgressionConstant ≤ (c : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hc₁ : quarticBogolyubovConstant ≤ (c : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  let PB : Polynomial ℕ := 1024 * (Polynomial.X + 1)
  let PZ : Polynomial ℕ := 736 + 96 * PB + 1504
  let PR : Polynomial ℕ := 2 + Polynomial.C c * (PZ + 1) ^ 4
  let PA : Polynomial ℕ := Polynomial.C c * (PZ + 1) ^ 8 + (PB + 13) + 64
  let PV : Polynomial ℕ := 2 + 16 * (44 + 6 * PB + 94)
  let PT : Polynomial ℕ := 2 * PR + PV + PA + 2
  let PL : Polynomial ℕ := PA + (4 + PT) * PR
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (PB + PL + PR)
  refine ⟨C, hC, ?_⟩
  intro p hp B
  let Z := 736 + 96 * B + 1504
  let R := 2 + (c : ℝ) * (Z + 1) ^ 4
  let A := (c : ℝ) * (Z + 1) ^ 8 + (B + 13) + 64
  let V := 2 + 16 * (44 + 6 * B + 94)
  let T := 2 * R + V + A + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hz : roundedModelLogBudget B 1 = Z := by
    simp [roundedModelLogBudget, max_eq_left hB, Z]
  have hrank : properAffineRankBound B 1 ≤ R := by
    unfold properAffineRankBound
    rw [hz]
    dsimp [R]
    gcongr
  have hloss : affineRecoveryLogLoss B 1 ≤ A := by
    unfold affineRecoveryLogLoss
    rw [hz]
    dsimp [A]
    norm_num
    gcongr
  have hvolume : properAffineVolumeLog B 1 = V := by
    simp [properAffineVolumeLog, max_eq_left hB, V]
  have hscale : properAffineScaleLog B 1 ≤ T := by
    unfold properAffineScaleLog
    rw [hvolume]
    dsimp [T]
    linarith
  have hrank0 : 0 ≤ properAffineRankBound B 1 := by
    have hc := quarticBogolyubovConstant_pos.le
    unfold properAffineRankBound
    positivity
  have hproper : properAffineRecoveryLogLoss B 1 ≤ A + (4 + T) * R := by
    unfold properAffineRecoveryLogLoss
    exact add_le_add hloss (mul_le_mul (by linarith) hrank hrank0 (by linarith))
  have htotal : B + (A + (4 + T) * R) + R ≤ (p + C) ^ C := by
    simpa [PB, PL, PR, PA, PZ, PV, PT, B, Z, R, A, V, T, Polynomial.eval₂_pow]
      using hbound p hp
  have hproper0 : 0 ≤ A + (4 + T) * R := by positivity
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_fourier_of_gowers_two {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ χ : AddChar G ℂ, gowersNorm 2 f ^ 2 ≤ ‖finiteFourierCoeff f χ‖ := by
  classical
  obtain ⟨χ, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun χ : AddChar G ℂ => ‖finiteFourierCoeff f χ‖) Finset.univ_nonempty
  have hmass : (∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2) ≤ 1 := by
    rw [finiteFourier_parseval]
    apply Finset.expect_le Finset.univ_nonempty
    intro x _
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg (f x)) (hf x) 2
  have hfourth : gowersNorm 2 f ^ 4 ≤ ‖finiteFourierCoeff f χ‖ ^ 2 := by
    rw [gowersNorm_two_fourier]
    calc
      _ ≤ ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ ^ 2 * ‖finiteFourierCoeff f ψ‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro ψ _
        have h := pow_le_pow_left₀ (norm_nonneg (finiteFourierCoeff f ψ))
          (hmax ψ (Finset.mem_univ ψ)) 2
        nlinarith [sq_nonneg (‖finiteFourierCoeff f ψ‖)]
      _ = ‖finiteFourierCoeff f χ‖ ^ 2 * ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ ‖finiteFourierCoeff f χ‖ ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass (sq_nonneg ‖finiteFourierCoeff f χ‖)
  refine ⟨χ, (sq_le_sq₀ (sq_nonneg (gowersNorm 2 f)) (norm_nonneg (finiteFourierCoeff f χ))).mp ?_⟩
  simpa only [← pow_mul, show 2 * 2 = 4 by norm_num] using hfourth

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem exists_quadratic_frequency_graph {p : ℝ} (hp : 0 ≤ p)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hG : Real.exp (-p) ≤ gowersNorm 3 f) :
    ∃ H : Finset G, H.Nonempty ∧
      Real.exp (-(128 * (p + 1))) * Fintype.card G ≤ (H.card : ℝ) ∧
      ∃ χ : G → AddChar G ℂ,
        (∀ h ∈ H, Real.exp (-(128 * (p + 1))) ≤
          ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖) ∧
        Real.exp (-(128 * (p + 1))) * (Fintype.card G : ℝ) ^ 3 ≤
          (Finset.addEnergy (additiveGraph H χ) (additiveGraph H χ) : ℝ) := by
  classical
  obtain ⟨H, hH, hdense, hderivative⟩ := exists_many_large_gowers_derivatives 1 f hf hp hG
  choose χ hχ using fun h =>
    exists_large_fourier_of_gowers_two (multiplicativeDerivative f h)
      (multiplicativeDerivative_norm_le_one f hf h)
  let d := derivativeInverseBudget 1 p
  have hd : d = 8 * p + 2 := by norm_num [d, derivativeInverseBudget]
  have hcorr (h : G) (hh : h ∈ H) : Real.exp (-(2 * d)) ≤
      ‖finiteFourierCoeff (multiplicativeDerivative f h) (χ h)‖ := by
    calc
      _ = Real.exp (-d) ^ 2 := by rw [pow_two, ← Real.exp_add]; congr 1; ring
      _ ≤ gowersNorm 2 (multiplicativeDerivative f h) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_nonneg _) (hderivative h hh) 2
      _ ≤ _ := hχ h
  have hdP : d ≤ 128 * (p + 1) := by rw [hd]; linarith
  have h2dP : 2 * d ≤ 128 * (p + 1) := by rw [hd]; linarith
  have henergy := derivative_character_graph_energy f H χ hf
    (Real.exp_pos (-d)) (Real.exp_pos (-(2 * d))) hdense hcorr
  have hthreshold : Real.exp (-(128 * (p + 1))) ≤
      (Real.exp (-d) * Real.exp (-(2 * d))) ^ 4 / 2 := by
    rw [derivative_quadruple_exp_threshold]
    calc
      _ ≤ Real.exp (-(12 * d) - 1) := Real.exp_le_exp.mpr (by rw [hd]; linarith)
      _ ≤ _ := exp_sub_one_le_half_exp _
  refine ⟨H, hH, ?_, χ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hdP))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg h2dP)).trans (hcorr h hh)
  · exact (mul_le_mul_of_nonneg_right hthreshold (by positivity)).trans henergy

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticLocalFrequency
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem exists_local_affine_scalar_chart
    {r N : ℕ} [NeZero N] {p : ℝ} (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p)
    (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (hdense : Real.exp (-p) * N ≤ (J.card : ℝ)) (x : ZMod N → Fin r → ℤ)
    (hx : ∀ h ∈ J, ∀ i, |x h i| ≤ (R i : ℤ))
    (hrep : ∀ h ∈ J, h = h₀ + η (x h)) (a : ℝ) (b : Fin r → ℝ) :
    ∃ K ⊆ J, K.Nonempty ∧ Real.exp (-((p + 4) ^ 7)) * N ≤ (K.card : ℝ) ∧
      ∃ (t c : Fin r → ℝ) (a' : ℝ) (b' : Fin r → ℝ),
        (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
        (∀ i, |c i| ≤ properCyclicCoordinateBound r (Real.exp (-p)) + 1 / 16) ∧
        ∀ h ∈ K, (∀ i, |affineCyclicTorusLocalLift t c h₀ h i| ≤ 1 / 16) ∧
          a + ∑ i, (x h i : ℝ) * b i =
            a' + ∑ i, affineCyclicTorusLocalLift t c h₀ h i * b' i := by
  obtain ⟨basis, _, t, ht, hperiod, K, hKJ, hK, hcard, c, hc, hdata⟩ :=
    exists_localized_cyclic_torus_chart η R hinj h₀ J hJ (Real.exp (-p))
      (Real.exp_pos _) hdense x hx hrep 8 (by norm_num)
  let B := basis.ofZLatticeBasis ℝ (cyclicIntegerKernel η)
  let a' := affineBasisConstant B (fun _ : Unit => a) (fun i _ => b i) c ()
  let b' (i : Fin r) := affineBasisCoefficient B (fun j (_ : Unit) => b j) i ()
  refine ⟨K, hKJ, hK, local_cyclic_torus_density hp hr J K hdense hcard,
    t, c, a', b', ht, hperiod, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, div_div, show (2 : ℝ) * 8 = 16 by norm_num] using hc
  · intro h hh
    obtain ⟨_, hsmall, hcoord⟩ := hdata h hh
    refine ⟨by norm_num at hsmall ⊢; exact hsmall, ?_⟩
    change a + ∑ i, integerVectorRealMap (x h) i * b i = _
    rw [hcoord]
    exact affine_basis_change B (fun _ : Unit => a) (fun i _ => b i) c
      (affineCyclicTorusLocalLift t c h₀ h) ()

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PositiveComparisonDataBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def positiveComparisonDataBudget (m q : ℕ) (p : ℝ) : ℝ :=
  (2 * p + 4) + allocatedFourierOutputBudget m (2 * p + 4) +
    allocatedFourierLogBudget m (2 * p + 4) + 3 * p + (q + 1) * (4 * p + 5) + 4

theorem positiveComparisonDataBudget_bounds (m q : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let Q := positiveComparisonDataBudget m q p
    0 ≤ Q ∧ p ≤ Q ∧ 2 * p + 4 ≤ Q ∧
      allocatedFourierOutputBudget m (2 * p + 4) ≤ Q ∧
      allocatedFourierLogBudget m (2 * p + 4) + 3 * p + (q + 1) * (4 * p + 5) + 4 ≤ Q := by
  have hB := allocatedFourierLogBudget_nonneg m (by linarith : 0 ≤ 2 * p + 4)
  have hF : 0 ≤ allocatedFourierOutputBudget m (2 * p + 4) := by
    unfold allocatedFourierOutputBudget
    positivity
  have hL : 0 ≤ ((q : ℝ) + 1) * (4 * p + 5) := by positivity
  dsimp only [positiveComparisonDataBudget]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedPhysicalChartBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedPhysicalRootAllowance (c : LayerSamplerVariables G I n B → ℤ) : ℝ :=
  1 + ∑ k, |(c k : ℝ)| / layerSamplerBox B U b S k

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def positiveModerateSpectrumCardBudget (n j t : ℕ) (U V W ε : ℝ) : ℝ :=
  positiveModerateSpectrumConstant n j U V /
      positiveModerateRetainedBias n j t U V W ε ^ positiveModerateSpectrumExponent n j +
    W * positiveModerateLengthConstant n U ^ t /
      positiveModerateRetainedBias n j t U V W ε ^ (positiveModerateLengthExponent n * t)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSiteApproximation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedNaturalConstantRadius (j : Fin m) (i : Fin (n j)) : ℝ :=
  2 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1)

noncomputable def allocatedNaturalSupportRadius (α : Type*) [Fintype α]
    (j : Fin m) (i : Fin (n j)) : ℝ :=
  blockJetScaleBound (Fintype.card α) (j.val + 1) (Fintype.card (B ⟨j, Sum.inr i⟩)) 4 +
    1 / 4 + allocatedNaturalConstantRadius (G := G) B j i

omit [Fintype G] [∀ j, Fintype (I j)] in
theorem allocatedNaturalSupportRadius_nonneg (α : Type*) [Fintype α]
    (j : Fin m) (i : Fin (n j)) : 0 ≤ allocatedNaturalSupportRadius (G := G) B α j i := by
  have h := blockJetScaleBound_nonneg (Fintype.card α) (j.val + 1)
    (Fintype.card (B ⟨j, Sum.inr i⟩)) (by norm_num : (0 : ℝ) ≤ 4)
  unfold allocatedNaturalSupportRadius allocatedNaturalConstantRadius
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def allocatedNaturalSiteRadius (j : Fin m) (i : Fin (n j))
    (rows : Finset (Finset α)) : ℝ :=
  rows.card * allocatedNaturalSupportRadius (G := G) B α j i

omit [Fintype G] [∀ j, Fintype (I j)] [DecidableEq α] in
theorem allocatedNaturalSiteRadius_nonneg (j : Fin m) (i : Fin (n j))
    (rows : Finset (Finset α)) : 0 ≤ allocatedNaturalSiteRadius (G := G) B j i rows :=
  mul_nonneg (Nat.cast_nonneg _) (allocatedNaturalSupportRadius_nonneg B α j i)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedGridAxisScale : {a // grid a} → ℝ≥0
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => basisAxisScale (b j) i

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAxes_card_le {p : ℝ}
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ ((2*m : ℕ) : ℝ)*p := by
  calc
    _ = ∑ j : Fin m, ((Fintype.card (I j) : ℝ)+(n j : ℝ)) := by
      simp only [LayerSamplerAxis, Fintype.card_sigma, Fintype.card_sum, Fintype.card_fin,
        Nat.cast_sum, Nat.cast_add]
    _ ≤ ∑ _ : Fin m, (p+p) := Finset.sum_le_sum (fun j _ => add_le_add (hI j) (hn j))
    _ = _ := by simp; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include U b o

theorem allocatedAmbientDimension_eq (j : Fin m) :
    Fintype.card (I j) + n j = Fintype.card (J j) := by
  have h := (euclideanSubspace (U j)).finrank_add_finrank_orthogonal
  rw [finrank_eq_card_basis (o j).toBasis, finrank_eq_card_basis (b j), finrank_euclideanSpace] at h
  simpa only [Fintype.card_fin] using h

theorem allocatedAmbientDimension_le_axes (j : Fin m) :
    Fintype.card (J j) ≤ Fintype.card (LayerSamplerAxis I n) := by
  rw [← allocatedAmbientDimension_eq U b o j]
  have h := Finset.single_le_sum (f := fun i : Fin m => Fintype.card (I i ⊕ Fin (n i)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  simpa only [LayerSamplerAxis, Fintype.card_sigma, Fintype.card_sum, Fintype.card_fin] using h

theorem allocatedLatticeDimension_eq
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (j : Fin m) : Fintype.card (Q j) = Fintype.card (I j) := by
  have h := standardLatticeCoordinates_card (euclideanSubspace (U j)) (bW j) (b j) (hb j)
  rw [Fintype.card_sum, Fintype.card_fin, ← allocatedAmbientDimension_eq U b o j] at h
  omega

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTailProfileIdentity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {D G : Type*} [Fintype D] [Fintype G]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (P : D → Prop)

noncomputable def activeTailRescale (τ : D → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ)
    (j : ActiveProfileCoefficientIndex G B h P) : ℝ :=
  nonprincipalDilation Subtype.val (canonicalPrincipalExponent h j.1.val) (τ j.1.val) j.2 * r j

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "degree" => layerSamplerDegree I n
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

noncomputable def allocatedProfileFrozenNoise :
    PartitionedProfileNoiseIndex G (G × Option α) α B degree grid → ℝ :=
  Sum.elim fixedReal (fun _ => 0)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedScaleCollisionBudget
namespace OAI

section

namespace Erdos3

theorem exists_allocatedFixedScaleCollisionLog_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P → allocatedFixedScaleCollisionLog m P ≤ (P+A)^A := by
  obtain ⟨b, _, hb⟩ := VectorPolynomial.exists_allocatedFourierLogBudget_bound m
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C b)^b +
    2*Polynomial.X*(Polynomial.X+5) + (4*Polynomial.X+128) + 2*Polynomial.X + 4
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget q
  refine ⟨A, hA, ?_⟩
  intro P hP
  have hpoly : (P+b)^b + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4 ≤ (P+A)^A := by
    simpa [q, spatialSamplingBudget, Polynomial.eval₂_pow] using hbound P hP
  apply le_trans _ hpoly
  unfold allocatedFixedScaleCollisionLog
  gcongr
  exact hb P hP

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongIdealCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedSiteCoefficientRadius (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  max (allocatedNaturalSupportRadius (G := G) B α a.1 a.2)
    ((2 : ℝ) ^ (a.1.val + 1) *
      (allocatedNaturalSiteRadius (G := G) B a.1 a.2 (rowSets a.1) + 1 / 4))

theorem allocatedSiteCoefficientRadius_nonneg (a : Σ j : Fin m, Fin (n j)) :
    0 ≤ allocatedSiteCoefficientRadius (G := G) B rowSets a :=
  (allocatedNaturalSupportRadius_nonneg (G := G) B α a.1 a.2).trans (le_max_left _ _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SampledFullboxDetectionBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem natPolynomial_eval_mono_nonneg (P : Polynomial ℕ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    P.eval₂ (Nat.castRingHom ℝ) p ≤ P.eval₂ (Nat.castRingHom ℝ) q := by
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  exact Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hp hpq n) (Nat.cast_nonneg _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedMaskedChartProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ)

local notation "single" => (fun _ : Fin m => Unit)

noncomputable def mixedCoveredSiteResidue (w : MixedCoveredJetSource I single E n d) :
    (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period) :=
  (fun j i => ((w.1 j).2 i () : ZMod period), fun j i => ((w.2 j () i).val : ZMod period))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedCappedContinuousSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

def slicedFixedUniformSiteLog (m : ℕ) (p E : ℝ) : ℝ :=
  p + E + 1 + ∑ j : Fin m, slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p E

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

noncomputable def allocatedAffineScale (D P Prho Pk target F T : ℝ) :
    LayerSamplerScale (G := G) B U basis R σ :=
  selectedLayerSamplerScale B U basis R σ hR hσ
    ⌈Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T)⌉₊

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularMultilinearAmbientSublevel
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical BigOperators

variable {I J R : Type*} [CommRing R]

theorem top_coeff_polynomialTranslate (P : MvPolynomial I R) (v : I → R)
    (a : I →₀ ℕ) (hP : P.totalDegree ≤ a.degree) :
    (polynomialTranslate v P).coeff a = P.coeff a := by
  have ht := polynomialTranslate_sub_mem_weightedSupportLT v (1 : I → ℕ)
    (fun _ => by simp) ((mem_weightedSupportLE_one_iff P a.degree).mpr hP)
  have hz : (polynomialTranslate v P - P).coeff a = 0 := by
    by_contra hn
    have hh : Finsupp.weight (1 : I → ℕ) a < a.degree := ht (mem_support_iff.mpr hn)
    have he : Finsupp.weight (1 : I → ℕ) a = a.degree := by
      simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]
    rw [he] at hh
    exact (lt_irrefl _) hh
  simpa only [coeff_sub, sub_eq_zero] using hz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

section TopPart

variable {I J R : Type*} [CommRing R]

theorem homogeneousComponent_polynomialTranslate_top (P : MvPolynomial I R)
    (v : I → R) (r : ℕ) (hP : P.totalDegree ≤ r) :
    homogeneousComponent r (polynomialTranslate v P) = homogeneousComponent r P := by
  ext a
  simp only [coeff_homogeneousComponent]
  split_ifs with ha
  · exact top_coeff_polynomialTranslate P v a (ha.symm ▸ hP)
  · rfl

theorem homogeneousComponent_restricted_translate_top (f : J → I)
    (hf : Function.Injective f) (P : MvPolynomial I R) (v : I → R)
    (r : ℕ) (hP : P.totalDegree ≤ r) :
    homogeneousComponent r (killCompl hf (polynomialTranslate v P)) =
      killCompl hf (homogeneousComponent r P) := by
  rw [homogeneousComponent_killCompl, homogeneousComponent_polynomialTranslate_top P v r hP]

theorem homogeneousComponent_conditionPolynomial_top (f : J → I)
    (hf : Function.Injective f) (P : MvPolynomial I R) (v : I → R)
    (r : ℕ) (hP : P.totalDegree ≤ r) :
    homogeneousComponent r (conditionPolynomial f hf v P) =
      killCompl hf (homogeneousComponent r P) :=
  homogeneousComponent_restricted_translate_top f hf P _ r hP

end TopPart

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {K J R : Type*} [Fintype K] [CommRing R]

theorem spatialRankPolynomial_conditioned_top_congr (e : J ↪ K)
    (f g : Option K → R) (hfg : ∀ k, f (some k) = g (some k))
    (v w : K → R) :
    homogeneousComponent 1 (conditionPolynomial e e.injective v (spatialRankPolynomial f)) =
      homogeneousComponent 1 (conditionPolynomial e e.injective w (spatialRankPolynomial g)) := by
  rw [homogeneousComponent_conditionPolynomial_top e e.injective _ v 1
      (spatialRankPolynomial_degree f),
    homogeneousComponent_conditionPolynomial_top e e.injective _ w 1
      (spatialRankPolynomial_degree g),
    spatialRankPolynomial_top_congr f g hfg]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedSelectedCoefficientProbability
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem supportedPMF_event_eq_map_true {X : Type*} (p : PMF X) (T : Finset X)
    (hT : ∀ x ∉ T, (p x).toReal = 0) (bad : X → Prop) :
    (ofSupportedPMF p T hT).eventProbability (fun x => bad x.val) =
      ((p.map (fun x => decide (bad x))) true).toReal := by
  have h := ofSupportedPMF_map_event p T hT (fun x => decide (bad x)) (fun b : Bool => b = true)
  simpa [eventProbability, mean] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedBadProductSpatialBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedBadProductSpatialBudget (m A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ B : ℝ, 0 ≤ B →
      let P := (B + A) ^ A
      let Ps := (B + C) ^ C
      let Q := allocatedFourierLogBudget m P
      P ≤ Ps ∧ 2 * P + 7 * B + 24 ≤ Ps ∧
        allocatedMaskedFourierBudget m P ≤ Ps ∧
        (4 * Q + 2) ^ 4 ≤ Ps ∧ 4 * Q * (4 * Q + 2) ^ 4 + Q ≤ Ps := by
  obtain ⟨a, _, ha⟩ := exists_allocatedMaskedFourierBudget_bound m 2
  let p : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget
    (2 * p + 7 * Polynomial.X + 24 + (p + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro B hB P Ps Q
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hF : 0 ≤ (P + a) ^ a := by positivity
  have htotal : 2 * P + 7 * B + 24 + (P + a) ^ a ≤ Ps := by
    simpa [p, P, Ps, Polynomial.eval₂_pow] using hbound B hB
  have hmask : allocatedMaskedFourierBudget m P ≤ Ps :=
    (ha P hP).1.trans (by linarith)
  have hcomponents := allocatedMaskedFourierBudget_bounds m hP
  exact ⟨by linarith, by linarith, hmask,
    hcomponents.2.2.1.trans hmask, hcomponents.2.2.2.trans hmask⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedSameScaleBadProductBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedBadProductFinalBudget (m : ℕ) :
    ∃ C1 C2 : ℕ, 2 ≤ C1 ∧ 2 ≤ C2 ∧ ∀ {B P0 E V : ℝ} {M nX : ℕ},
      1 ≤ B → (M : ℝ) ≤ B → (nX : ℝ) ≤ B →
      P0 ∈ Set.Icc 0 B → E ∈ Set.Icc 0 B → V ∈ Set.Icc 0 B →
      let Jalloc := modularInitialBlockCount m (nX + m * M)
      let pnum := enlargedPreparedCommonSamplerDimension m M Jalloc
      let ncoeff := (m + 1) * (pnum + 1) ^ m
      let P := (B + C1) ^ C1
      let Ps := (B + C2) ^ C2
      let Qf := allocatedFourierLogBudget m P
      1 ≤ P ∧ 1 ≤ Ps ∧ B ≤ P ∧ P0 ≤ P ∧
        (ncoeff : ℝ) + pnum ≤ P ∧
        allocatedWitnessScaleLog P0 (2 * P0 + 2 * V + 5 * E + 24) ≤ P ∧
        V + 3 * E + 16 ≤ P ∧ ((pnum + 1) * nX : ℕ) ≤ Ps ∧
        P ≤ Ps ∧ 2 * P + 2 * V + 5 * E + 24 ≤ Ps ∧
        (4 * Qf + 2) ^ 4 ≤ Ps ∧ 4 * Qf * (4 * Qf + 2) ^ 4 + Qf ≤ Ps := by
  obtain ⟨C1, hC1, hsource⟩ := exists_preparedBadProductSourceBudget m
  obtain ⟨C2, hC2, hspatial⟩ := exists_preparedBadProductSpatialBudget m C1
  refine ⟨C1, C2, hC1, hC2, ?_⟩
  intro B P0 E V M nX hB hM hnX hP0 hE hV Jalloc pnum ncoeff P Ps Qf
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨hBP, hP0P, hprimitive, hscale, haccuracy, hframe⟩ := hsource hB0 hM hnX hP0 hE hV
  obtain ⟨hPPS, hwidth, _, hfreq, hmass⟩ := hspatial B hB0
  refine ⟨hB.trans hBP, hB.trans (hBP.trans hPPS), hBP, hP0P, hprimitive, hscale,
    haccuracy, hframe.trans hPPS, hPPS, ?_, hfreq, hmass⟩
  have hEhi := hE.2
  have hVhi := hV.2
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3
open scoped NNReal Classical

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]

noncomputable def partitionedAffineSourceTolerance (A T : ℝ≥0) (degree : ℕ) (δ E : ℝ) : ℝ :=
  jointAffineCoefficientTolerance (Z := PartitionedProfileNoiseIndex G Z α B h P)
    (B := fun d : {d // ¬P d} => B d.val) (O := O) (α := α)
    (fun d => h d.val) (fun d => unitProfilePrincipalSize (B := B) d.val)
    (fun d => 2 * unitProfilePrincipalSize (B := B) d.val) A T degree 1 1 δ E

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineRadiusLog
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

noncomputable def allocatedAffineSourceTolerance (A T : ℝ≥0) (δ ε : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun P : LayerSamplerAxis I n → Prop =>
    partitionedAffineSourceTolerance (G := G) (Z := G × Option α) (B := B)
      (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T m δ ε)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

noncomputable def allocatedAffinePartitionRadiusLog (A T : ℝ≥0) (E F : ℝ)
    (P : LayerSamplerAxis I n → Prop) : ℝ :=
  2 * jointAffineSourceInputLog (B := fun a : {a // ¬P a} => B a.val)
    (O := fun a : {a // ¬P a} => O a.val.1) (α := α)
    (fun a => layerSamplerDegree I n a.val) (unitProfileCoefficientLog (B := B) A T)
    (E + Fintype.card {a // ¬P a} + 4) F + 2

noncomputable def allocatedAffineRadiusLog (A T : ℝ≥0) (E F : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (allocatedAffinePartitionRadiusLog (O := O) (α := α) B A T E F)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialPhysicalBadProductSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def preparedBadProductSpatialExponent (m : ℕ) : ℕ :=
  (exists_preparedBadProductFinalBudget m).choose_spec.choose

end Erdos3.VectorPolynomial

end

end OAI
end


