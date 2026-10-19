-- Prove2me | Definitions.Def_OAIE3v2B000
-- name    : OAIE3v2B000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:57:30.444283+00:00
-- url     : https://prove2.me/theorems/0efe5507-cc00-405f-9749-c8e6be0a28a9
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 1 of 311
-- statement:
--   Definitions bundle 1 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/CoefficientProfileBudget.lean`, `Estimates/AllocatedScalarLogBounds.lean`, `Estimates/AllocatedShortAxis.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/CoefficientScaleGap.lean`, `Estimates/CompactIntervalIntegral.lean`, `Estimates/DependentPatchValue.lean`, `Estimates/FreePrimitiveCriterion.lean`, `Estimates/InactiveAxisScale.lean`, `Estimates/PartialComplexScaledQuadrature.lean`, `Estimates/PrincipalBlockExponent.lean`, `Estimates/PrincipalCoefficientMarginal.lean`, `Estimates/ProgressionPartitionComposition.lean`, `Estimates/RationalHeight.lean`, `Estimates/RationalRowReduction.lean`, `Estimates/RealWeightPMF.lean`, `FixedDensity/OrderedPatternPartition.lean`, `Fourier/CommonCoveredSiteCharacter.lean`, `Fourier/EuclideanJetTorus.lean`, `Geometry/BoxBlockBudget.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Lattices/CompactLatticeApproximation.lean`, `Lattices/IntegerAxisPrincipalLaw.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/IntervalIntegerVectorAPFree.lean`, `Lattices/RectangularLatticeCells.lean`, `Lattices/ResidueSliceNormalizedCell.lean`, `Linear/BasisAxisNormalization.lean`, `Model.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Polynomial/PolynomialIntegerInputs.lean`, `Polynomial/PolynomialPatchProductBudget.lean`, `Polynomial/VectorPolynomialReconstruction.lean`, `Probability/EmptyCoefficientDensity.lean`, `Probability/InactivePrincipalLaw.lean`, `Probability/PrincipalCoefficientLaw.lean`, `Probability/RelativeSourceDensityParameter.lean`, `Probability/SmoothProbabilityProfile.lean`, `Results/Basic.lean`, `Sampling/CanonicalSamplerTuple.lean`, `Sampling/LayerSamplerWitnessScale.lean`, `Sampling/PrincipalSamplingScale.lean`, `Sampling/SmoothSplitSampling.lean`, `lean/OAI/Compat.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CoefficientProfileBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def coefficientProfileCenter {J : Type*} (P : Finset J) (γ : ℝ) (j : J) : ℝ := by
  classical
  exact if j ∈ P then 3 * γ / 2 else 0

noncomputable def principalProfileSize (R : ℝ) (b : ℕ) : ℝ := R / (8 * ((b : ℝ) + 1))

noncomputable def tailProfileSize (R σ : ℝ) (m : ℕ) : ℝ := σ * R / (4 * ((m : ℝ) + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RectangularLatticeCells
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def latticeSample (a S x : ℝ) : ℝ := (⌊a + S * x⌋ - a) / S

def latticeSamplingCell (a S : ℝ) (k : ℤ) : Set ℝ :=
  Set.Ico (((k : ℝ) - a) / S) (((k : ℝ) + 1 - a) / S)

theorem latticeSamplingCell_measurable (a S : ℝ) (k : ℤ) :
    MeasurableSet (latticeSamplingCell a S k) := measurableSet_Ico

theorem latticeSamplingCell_iff {a S x : ℝ} (hS : 0 < S) (k : ℤ) :
    x ∈ latticeSamplingCell a S k ↔ ⌊a + S * x⌋ = k := by
  rw [Int.floor_eq_iff]
  change (((k : ℝ) - a) / S ≤ x ∧ x < ((k : ℝ) + 1 - a) / S) ↔ _
  rw [div_le_iff₀ hS, lt_div_iff₀ hS]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

theorem latticeSamplingCell_volume {a S : ℝ} (hS : 0 < S) (k : ℤ) :
    volume.real (latticeSamplingCell a S k) = 1 / S := by
  rw [measureReal_def, latticeSamplingCell, Real.volume_Ico]
  have he : (((k : ℝ) + 1 - a) / S - ((k : ℝ) - a) / S) = 1 / S := by ring
  rw [he, ENNReal.toReal_ofReal (div_nonneg zero_le_one hS.le)]

theorem latticeSample_error {a S : ℝ} (hS : 0 < S) (x : ℝ) :
    |latticeSample a S x - x| ≤ 1 / S := by
  have hlo := Int.floor_le (a + S * x)
  have hhi := Int.lt_floor_add_one (a + S * x)
  have he : latticeSample a S x - x =
      (((⌊a + S * x⌋ : ℤ) : ℝ) - (a + S * x)) / S := by
    unfold latticeSample
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hS]
  apply div_le_div_of_nonneg_right _ hS.le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def finiteLatticeHistogram (s : Finset ℤ) (w : ℤ → ℝ) (a S x : ℝ) : ℝ :=
  ∑ k ∈ s, (latticeSamplingCell a S k).indicator (fun _ => w k) x

theorem latticeSamplingCell_indicator_integrable (a S : ℝ) (k : ℤ) (v : ℝ) :
    Integrable ((latticeSamplingCell a S k).indicator (fun _ => v)) := by
  apply (integrable_indicator_iff (latticeSamplingCell_measurable a S k)).mpr
  exact integrableOn_const (by simp [latticeSamplingCell, Real.volume_Ico])

theorem finiteLatticeHistogram_integrable (s : Finset ℤ) (w : ℤ → ℝ) (a S : ℝ) :
    Integrable (finiteLatticeHistogram s w a S) := by
  apply integrable_finsetSum
  intro k _
  exact latticeSamplingCell_indicator_integrable a S k (w k)

theorem finiteLatticeHistogram_integral (s : Finset ℤ) (w : ℤ → ℝ) (a : ℝ)
    {S : ℝ} (hS : 0 < S) :
    (∫ x, finiteLatticeHistogram s w a S x) = (∑ k ∈ s, w k) / S := by
  unfold finiteLatticeHistogram
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ (latticeSamplingCell_measurable a S _),
      latticeSamplingCell_volume hS, smul_eq_mul, one_div]
    rw [← Finset.mul_sum]
    ring
  · intro k _
    exact latticeSamplingCell_indicator_integrable a S k (w k)

theorem finiteLatticeHistogram_eq_floor (s : Finset ℤ) (w : ℤ → ℝ)
    (hw : ∀ k, k ∉ s → w k = 0) (a : ℝ) {S : ℝ} (hS : 0 < S) (x : ℝ) :
    finiteLatticeHistogram s w a S x = w ⌊a + S * x⌋ := by
  classical
  unfold finiteLatticeHistogram
  rw [Finset.sum_eq_single ⌊a + S * x⌋]
  · exact Set.indicator_of_mem ((latticeSamplingCell_iff hS _).mpr rfl) _
  · intro k _ hne
    apply Set.indicator_of_notMem
    intro hk
    exact hne ((latticeSamplingCell_iff hS k).mp hk).symm
  · intro hn
    rw [hw _ hn]
    simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CompactIntervalIntegral
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem compactInterval_integrable (f : ℝ → ℝ) (hf : Continuous f) (R : ℝ)
    (hsupport : ∀ x, R < |x| → f x = 0) : Integrable f := by
  apply hf.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
  intro x hx
  apply abs_le.mp
  by_contra! h
  exact hx (hsupport x h)

theorem integral_norm_le_interval (f : ℝ → ℝ) {u v C : ℝ} (huv : u ≤ v)
    (hzero : ∀ x, x ∉ Set.Icc u v → f x = 0)
    (hbound : ∀ x ∈ Set.Icc u v, ‖f x‖ ≤ C) :
    (∫ x, ‖f x‖) ≤ C * (v - u) := by
  have hi : Integrable ((Set.Icc u v).indicator (fun _ : ℝ => C)) :=
    (integrableOn_const (by simp : volume (Set.Icc u v) ≠ ⊤)).integrable_indicator measurableSet_Icc
  have hb : ∀ x, ‖f x‖ ≤ (Set.Icc u v).indicator (fun _ : ℝ => C) x := by
    intro x
    by_cases hx : x ∈ Set.Icc u v
    · simpa only [Set.indicator_of_mem hx] using hbound x hx
    · simp only [hzero x hx, norm_zero, Set.indicator_of_notMem hx, le_refl]
  calc
    _ ≤ ∫ x, (Set.Icc u v).indicator (fun _ : ℝ => C) x :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg (f x))) hi
        (Filter.Eventually.of_forall hb)
    _ = C * (v - u) := by
      rw [integral_indicator_const C measurableSet_Icc, Real.volume_real_Icc_of_le huv, smul_eq_mul]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Model
namespace OAI

namespace Erdos3

def APFree (A : Set ℕ) (k : ℕ) : Prop := ¬ HasAP A k

end Erdos3

open scoped BigOperators

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Results.Basic
namespace OAI

section

namespace Erdos3

theorem HasAP.mono {A B : Set ℕ} {k : ℕ} (h : HasAP A k) (hAB : A ⊆ B) :
    HasAP B k := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi ↦ hAB (h i hi)⟩

theorem APFree.mono {A B : Set ℕ} {k : ℕ} (h : APFree B k) (hAB : A ⊆ B) :
    APFree A k := fun hA ↦ h (hA.mono hAB)

theorem HasAP.affine_image {A : Set ℕ} {k : ℕ} (h : HasAP A k)
    (u v : ℕ) (hv : 0 < v) : HasAP ((fun n ↦ u + v * n) '' A) k := by
  obtain ⟨a, d, hd, h⟩ := h
  refine ⟨u + v * a, v * d, Nat.mul_pos hv hd, fun i hi ↦ ?_⟩
  exact ⟨a + i * d, h i hi, by ring⟩

theorem APFree.affine_preimage {A : Set ℕ} {k : ℕ} (h : APFree A k)
    (u v : ℕ) (hv : 0 < v) : APFree ((fun n ↦ u + v * n) ⁻¹' A) k := by
  intro hpre
  exact h ((hpre.affine_image u v hv).mono (Set.image_preimage_subset _ _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def sampledWeightIndices (a S R : ℝ) : Finset ℤ :=
  Finset.Icc ⌈a - S * R⌉ ⌊a + S * R⌋

noncomputable def sampledWeight (ψ : ℝ → ℝ) (a S : ℝ) (k : ℤ) : ℝ :=
  ψ (((k : ℝ) - a) / S)

noncomputable def sampledWeightSum (ψ : ℝ → ℝ) (a S R : ℝ) : ℝ :=
  ∑ k ∈ sampledWeightIndices a S R, sampledWeight ψ a S k

noncomputable def sampledWeightHistogram (ψ : ℝ → ℝ) (a S R : ℝ) : ℝ → ℝ :=
  finiteLatticeHistogram (sampledWeightIndices a S R) (sampledWeight ψ a S) a S

theorem sampledWeight_zero_off_indices (ψ : ℝ → ℝ) {a S R : ℝ} (hS : 0 < S)
    (hsupport : ∀ x, R < |x| → ψ x = 0) (k : ℤ)
    (hk : k ∉ sampledWeightIndices a S R) : sampledWeight ψ a S k = 0 := by
  by_contra hn
  have hb : |((k : ℝ) - a) / S| ≤ R := by
    by_contra! hb
    exact hn (hsupport _ hb)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb
  have hlo' := (le_div_iff₀ hS).mp hlo
  have hhi' := (div_le_iff₀ hS).mp hhi
  apply hk
  apply Finset.mem_Icc.mpr
  exact ⟨Int.ceil_le.mpr (by nlinarith), Int.le_floor.mpr (by nlinarith)⟩

theorem sampledWeightSum_eq_tsum (ψ : ℝ → ℝ) {a S R : ℝ} (hS : 0 < S)
    (hsupport : ∀ x, R < |x| → ψ x = 0) :
    sampledWeightSum ψ a S R = ∑' k : ℤ, ψ (((k : ℝ) - a) / S) :=
  (hasSum_sum_of_ne_finset_zero (sampledWeight_zero_off_indices ψ hS hsupport)).tsum_eq.symm

theorem sampledWeightHistogram_eq (ψ : ℝ → ℝ) {a S R : ℝ} (hS : 0 < S)
    (hsupport : ∀ x, R < |x| → ψ x = 0) (x : ℝ) :
    sampledWeightHistogram ψ a S R x = ψ (latticeSample a S x) :=
  finiteLatticeHistogram_eq_floor _ _ (sampledWeight_zero_off_indices ψ hS hsupport) a hS x

theorem sampledWeightHistogram_integrable (ψ : ℝ → ℝ) (a S R : ℝ) :
    Integrable (sampledWeightHistogram ψ a S R) := finiteLatticeHistogram_integrable _ _ _ _

theorem sampledWeightHistogram_integral (ψ : ℝ → ℝ) (a : ℝ) {S : ℝ} (hS : 0 < S) (R : ℝ) :
    (∫ x, sampledWeightHistogram ψ a S R x) = sampledWeightSum ψ a S R / S :=
  finiteLatticeHistogram_integral _ _ a hS

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CompactLatticeApproximation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem sampledWeightHistogram_error (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hS : 0 < S) (hsupport : ∀ x, R < |x| → ψ x = 0) (x : ℝ) :
    ‖sampledWeightHistogram ψ a S R x - ψ x‖ ≤ (L : ℝ) / S := by
  rw [sampledWeightHistogram_eq ψ hS hsupport]
  calc
    _ ≤ (L : ℝ) * ‖latticeSample a S x - x‖ := hLip.norm_sub_le _ _
    _ ≤ (L : ℝ) * (1 / S) :=
      mul_le_mul_of_nonneg_left (latticeSample_error hS x) L.coe_nonneg
    _ = _ := by ring

theorem sampledWeightHistogram_zero_outside (ψ : ℝ → ℝ) {a S R : ℝ}
    (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0) (x : ℝ) (hx : R + 1 < |x|) :
    sampledWeightHistogram ψ a S R x = 0 := by
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have he : |latticeSample a S x - x| ≤ 1 :=
    (latticeSample_error hSp x).trans ((div_le_one hSp).mpr hS)
  have ht : |x| ≤ |latticeSample a S x| + |latticeSample a S x - x| := by
    have h := abs_sub_le x (latticeSample a S x) 0
    simpa only [sub_zero, abs_sub_comm x (latticeSample a S x), add_comm] using h
  rw [sampledWeightHistogram_eq ψ hSp hsupport]
  exact hsupport _ (by linarith)

theorem sampledWeightHistogram_l1_error (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hR : 0 ≤ R) (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0) :
    (∫ x, ‖sampledWeightHistogram ψ a S R x - ψ x‖) ≤ (2 * R + 2) * (L : ℝ) / S := by
  have hz : ∀ x, x ∉ Set.Icc (-(R + 1)) (R + 1) →
      sampledWeightHistogram ψ a S R x - ψ x = 0 := by
    intro x hx
    have hx' : R + 1 < |x| := lt_of_not_ge (fun h => hx (abs_le.mp h))
    rw [sampledWeightHistogram_zero_outside ψ hS hsupport x hx', hsupport x (by linarith), sub_self]
  have he := integral_norm_le_interval (fun x => sampledWeightHistogram ψ a S R x - ψ x)
    (u := -(R + 1)) (v := R + 1) (C := (L : ℝ) / S) (by linarith)
    hz (fun x _ => sampledWeightHistogram_error ψ hLip
      (lt_of_lt_of_le zero_lt_one hS) hsupport x)
  exact he.trans_eq (by ring)

theorem sampledWeightSum_error (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hR : 0 ≤ R) (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0) :
    |sampledWeightSum ψ a S R / S - ∫ x, ψ x| ≤ (2 * R + 2) * (L : ℝ) / S := by
  rw [← sampledWeightHistogram_integral ψ a (lt_of_lt_of_le zero_lt_one hS) R,
    ← integral_sub (sampledWeightHistogram_integrable ψ a S R)
      (compactInterval_integrable ψ hLip.continuous R hsupport)]
  exact (norm_integral_le_integral_norm _).trans
    (sampledWeightHistogram_l1_error ψ hLip hR hS hsupport)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalHeight
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def RationalHeightLE (q : ℚ) (H : ℕ) : Prop :=
  q.num.natAbs ≤ H ∧ q.den ≤ H

theorem rational_fraction_entries_le (a b : ℤ) (hb : b ≠ 0) :
    ((a : ℚ) / b).num.natAbs ≤ a.natAbs ∧
      ((a : ℚ) / b).den ≤ b.natAbs := by
  obtain ⟨c, ha, hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a hb
  have hc : c ≠ 0 := by
    intro h
    exact hb (by simpa [h] using hd)
  have hcpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  constructor
  · calc
      _ ≤ c.natAbs * ((a : ℚ) / b).num.natAbs := Nat.le_mul_of_pos_left _ hcpos
      _ = a.natAbs := by simpa only [Int.natAbs_mul] using congrArg Int.natAbs ha.symm
  · calc
      _ ≤ c.natAbs * ((a : ℚ) / b).den := Nat.le_mul_of_pos_left _ hcpos
      _ = b.natAbs := by
        simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hd.symm

theorem rationalHeightLE_fraction (a b : ℤ) (hb : b ≠ 0)
    {H : ℕ} (haH : a.natAbs ≤ H) (hbH : b.natAbs ≤ H) :
    RationalHeightLE ((a : ℚ) / b) H :=
  ⟨(rational_fraction_entries_le a b hb).1.trans haH,
    (rational_fraction_entries_le a b hb).2.trans hbH⟩

section Array

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def arrayDenominator (q : ι → ℚ) : ℕ := ∏ i, (q i).den

def clearedArray (q : ι → ℚ) (i : ι) : ℤ :=
  (q i).num * (∏ j ∈ Finset.univ.erase i, (q j).den : ℕ)

omit [DecidableEq ι] in
theorem arrayDenominator_pos (q : ι → ℚ) : 0 < arrayDenominator q :=
  Finset.prod_pos fun i _ => (q i).den_pos

omit [DecidableEq ι] in
theorem arrayDenominator_le (q : ι → ℚ) {H : ℕ}
    (hq : ∀ i, (q i).den ≤ H) :
    arrayDenominator q ≤ H ^ Fintype.card ι := by
  exact (Finset.prod_le_prod' fun i _ => hq i).trans_eq (by simp)

theorem arrayDenominator_eq (q : ι → ℚ) (i : ι) :
    arrayDenominator q = (q i).den * ∏ j ∈ Finset.univ.erase i, (q j).den := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

theorem clearedArray_cast (q : ι → ℚ) (i : ι) :
    (clearedArray q i : ℚ) = (arrayDenominator q : ℚ) * q i := by
  rw [arrayDenominator_eq q i]
  have hq := Rat.num_div_den (q i)
  have hd : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
  dsimp only [clearedArray]
  push_cast
  conv_rhs => rhs; rw [← hq]
  field_simp

theorem clearedArray_natAbs_le (q : ι → ℚ) {H : ℕ}
    (hq : ∀ i, RationalHeightLE (q i) H) (i : ι) :
    (clearedArray q i).natAbs ≤ H ^ Fintype.card ι := by
  have hprod : (∏ j ∈ Finset.univ.erase i, (q j).den) ≤
      H ^ (Finset.univ.erase i).card := by
    exact (Finset.prod_le_prod' fun j _ => (hq j).2).trans_eq (by simp)
  have hcard : (Finset.univ.erase i).card + 1 = Fintype.card ι := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ i)
  calc
    (clearedArray q i).natAbs =
        (q i).num.natAbs * ∏ j ∈ Finset.univ.erase i, (q j).den := by
      simp only [clearedArray, Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ H * H ^ (Finset.univ.erase i).card := Nat.mul_le_mul (hq i).1 hprod
    _ = H ^ Fintype.card ι := by rw [← hcard, pow_succ, mul_comm]

theorem exists_bounded_integer_array (q : ι → ℚ) {H : ℕ}
    (hq : ∀ i, RationalHeightLE (q i) H) :
    ∃ D : ℕ, 0 < D ∧ D ≤ H ^ Fintype.card ι ∧
      ∃ a : ι → ℤ, (∀ i, (a i : ℚ) = (D : ℚ) * q i) ∧
        ∀ i, (a i).natAbs ≤ H ^ Fintype.card ι :=
  ⟨arrayDenominator q, arrayDenominator_pos q,
    arrayDenominator_le q (fun i => (hq i).2), clearedArray q,
    clearedArray_cast q, clearedArray_natAbs_le q hq⟩

end Array

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalRowReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem rationalHeightLE_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℚ) {H : ℕ} (hq : ∀ i, RationalHeightLE (q i) H) :
    RationalHeightLE (∑ i, q i) ((Fintype.card ι + 1) * H ^ Fintype.card ι) := by
  obtain ⟨D, hDpos, hD, a, ha, hbound⟩ := exists_bounded_integer_array q hq
  have hsum : ((∑ i, a i : ℤ) : ℚ) = (D : ℚ) * ∑ i, q i := by
    push_cast
    simp_rw [ha]
    rw [Finset.mul_sum]
  have heq : (∑ i, q i) = ((∑ i, a i : ℤ) : ℚ) / (D : ℤ) := by
    apply (eq_div_iff (by exact_mod_cast hDpos.ne')).mpr
    simpa only [Int.cast_natCast, mul_comm] using hsum.symm
  rw [heq]
  apply rationalHeightLE_fraction _ _ (by exact_mod_cast hDpos.ne')
  · calc
      _ ≤ ∑ i, (a i).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _ : ι, H ^ Fintype.card ι := Finset.sum_le_sum fun i _ => hbound i
      _ = Fintype.card ι * H ^ Fintype.card ι := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)
  · simp only [Int.natAbs_natCast]
    exact hD.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SmoothProbabilityProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff

noncomputable def probabilityProfileBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩

noncomputable def smoothProbabilityProfile : ℝ → ℝ :=
  probabilityProfileBump.normed volume

theorem smoothProbabilityProfile_contDiff : ContDiff ℝ ∞ smoothProbabilityProfile :=
  probabilityProfileBump.contDiff_normed

theorem smoothProbabilityProfile_compact : HasCompactSupport smoothProbabilityProfile :=
  probabilityProfileBump.hasCompactSupport_normed

theorem smoothProbabilityProfile_range (x : ℝ) :
    0 ≤ smoothProbabilityProfile x ∧ smoothProbabilityProfile x ≤ 1 := by
  refine ⟨probabilityProfileBump.nonneg_normed x, ?_⟩
  have h := probabilityProfileBump.normed_le_div_measure_closedBall_rIn volume x
  norm_num [probabilityProfileBump] at h
  exact h

theorem smoothProbabilityProfile_zero (x : ℝ) (hx : 3 / 4 ≤ |x|) :
    smoothProbabilityProfile x = 0 := by
  have h : probabilityProfileBump x = 0 := probabilityProfileBump.zero_of_le_dist
    (by simpa only [probabilityProfileBump, Real.dist_eq, sub_zero] using hx)
  simp only [smoothProbabilityProfile, ContDiffBump.normed_def, h, zero_div]

theorem smoothProbabilityProfile_zero_outside (x : ℝ) (hx : 1 < |x|) :
    smoothProbabilityProfile x = 0 :=
  smoothProbabilityProfile_zero x (by linarith)

theorem smoothProbabilityProfile_integral : (∫ x, smoothProbabilityProfile x) = 1 :=
  probabilityProfileBump.integral_normed

theorem exists_smoothProbabilityProfile_lipschitz :
    ∃ A : ℝ≥0, 1 ≤ A ∧ LipschitzWith A smoothProbabilityProfile := by
  obtain ⟨A, hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    smoothProbabilityProfile_compact (smoothProbabilityProfile_contDiff.of_le (by simp) :
      ContDiff ℝ 1 smoothProbabilityProfile) one_ne_zero
  exact ⟨A + 1, by simp, hA.weaken (by simp)⟩

noncomputable def probabilityProfileLipschitz : ℝ≥0 :=
  exists_smoothProbabilityProfile_lipschitz.choose

theorem probabilityProfileLipschitz_one_le : 1 ≤ probabilityProfileLipschitz :=
  exists_smoothProbabilityProfile_lipschitz.choose_spec.1

theorem smoothProbabilityProfile_lipschitz :
    LipschitzWith probabilityProfileLipschitz smoothProbabilityProfile :=
  exists_smoothProbabilityProfile_lipschitz.choose_spec.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H]

def cubeShift {j : ℕ} (hs : Fin j → H) (ω : Fin j → Bool) : H :=
  ∑ i, if ω i then hs i else 0

@[simp] theorem cubeShift_cons_false {j : ℕ} (h : H) (hs : Fin j → H)
    (ω : Fin j → Bool) : cubeShift (Fin.cons h hs) (Fin.cons false ω) = cubeShift hs ω := by
  simp [cubeShift, Fin.sum_univ_succ]

@[simp] theorem cubeShift_cons_true {j : ℕ} (h : H) (hs : Fin j → H)
    (ω : Fin j → Bool) : cubeShift (Fin.cons h hs) (Fin.cons true ω) = h + cubeShift hs ω := by
  simp [cubeShift, Fin.sum_univ_succ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

@[simp] theorem cubeShift_false {j : ℕ} (hs : Fin j → A) :
    cubeShift hs (fun _ ↦ false) = 0 := by simp [cubeShift]

def cubeAxis {j : ℕ} (i : Fin j) : Fin j → Bool := fun k ↦ decide (k = i)

@[simp] theorem cubeShift_axis {j : ℕ} (hs : Fin j → A) (i : Fin j) :
    cubeShift hs (cubeAxis i) = hs i := by simp [cubeShift, cubeAxis]

abbrev SupportedCube (j : ℕ) (Q : Set A) :=
  {p : (Fin j → A) × A // ∀ ω : Fin j → Bool, p.2 + cubeShift p.1 ω ∈ Q}

theorem SupportedCube.base_mem {j : ℕ} {Q : Set A} (p : SupportedCube j Q) : p.val.2 ∈ Q := by
  simpa using p.property (fun _ ↦ false)

theorem SupportedCube.axis_mem {j : ℕ} {Q : Set A} (p : SupportedCube j Q) (i : Fin j) :
    p.val.2 + p.val.1 i ∈ Q := by
  simpa using p.property (cubeAxis i)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A]

def SupportedCube.points {j : ℕ} {Q : Set A} (p : SupportedCube j Q) : Q × (Fin j → Q) :=
  (⟨p.val.2, p.base_mem⟩, fun i ↦ ⟨p.val.2 + p.val.1 i, p.axis_mem i⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def truncatedProgressionLength (N a q H : ℕ) : ℕ :=
  if a < N then min H ((N - 1 - a) / q + 1) else 0

theorem lt_truncatedProgressionLength_iff {N a q H j : ℕ} (hq : 0 < q) :
    j < truncatedProgressionLength N a q H ↔ j < H ∧ a + q * j < N := by
  by_cases ha : a < N
  · simp only [truncatedProgressionLength, if_pos ha, lt_min_iff]
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hq, Nat.mul_comm j q]
    omega
  · simp only [truncatedProgressionLength, if_neg ha, Nat.not_lt_zero, false_iff,
      not_and]
    omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

structure FiniteProgressionPartition (N : ℕ) where
  Label : Type
  labelFintype : Fintype Label
  start : Label → ℕ
  step : Label → ℕ
  length : Label → ℕ
  step_pos : ∀ i, 0 < step i
  equiv : (Σ i : Label, Fin (length i)) ≃ Fin N
  equiv_val : ∀ i (j : Fin (length i)), (equiv ⟨i, j⟩).val = start i + step i * j.val

attribute [instance] FiniteProgressionPartition.labelFintype

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

def point (i : P.Label) (j : Fin (P.length i)) : Fin N := P.equiv ⟨i, j⟩

@[simp] theorem point_val (i : P.Label) (j : Fin (P.length i)) :
    (P.point i j).val = P.start i + P.step i * j.val := P.equiv_val i j

def cell (n : Fin N) : P.Label := (P.equiv.symm n).1

def offset (n : Fin N) : Fin (P.length (P.cell n)) := (P.equiv.symm n).2

@[simp] theorem cell_point (i : P.Label) (j : Fin (P.length i)) :
    P.cell (P.point i j) = i := by simp [cell, point]

@[simp] theorem point_cell_offset (n : Fin N) : P.point (P.cell n) (P.offset n) = n := by
  exact P.equiv.apply_symm_apply n

end FiniteProgressionPartition
end Erdos3

end

section

namespace Erdos3

def mergedIntervalLength (N H k : ℕ) : ℕ :=
  if k + 1 = N / H then N - H * k else H

theorem mergedInterval_start_le {N H k : ℕ} (hk : k < N / H) : H * k ≤ N := by
  have hq : H * (N / H) ≤ N := by simpa only [mul_comm] using Nat.div_mul_le_self N H
  exact (Nat.mul_le_mul_left H hk.le).trans hq

theorem mergedInterval_point_lt {N H k j : ℕ} (hk : k < N / H)
    (hj : j < mergedIntervalLength N H k) : H * k + j < N := by
  by_cases hlast : k + 1 = N / H
  · have hstart := mergedInterval_start_le hk
    simp only [mergedIntervalLength, hlast, ite_true] at hj
    omega
  · have hjH : j < H := by simpa only [mergedIntervalLength, hlast, ite_false] using hj
    have hstep := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hk)
    have hq : H * (N / H) ≤ N := by simpa only [mul_comm] using Nat.div_mul_le_self N H
    nlinarith

theorem mergedInterval_index_unique {N H k l j t : ℕ}
    (hk : k < N / H) (hl : l < N / H)
    (hj : j < mergedIntervalLength N H k) (ht : t < mergedIntervalLength N H l)
    (heq : H * k + j = H * l + t) : k = l := by
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · have hlast : k + 1 ≠ N / H := by omega
    have hjH : j < H := by simpa only [mergedIntervalLength, hlast, ite_false] using hj
    have hstep := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hkl)
    nlinarith
  · exact hkl
  · have hlast : l + 1 ≠ N / H := by omega
    have htH : t < H := by simpa only [mergedIntervalLength, hlast, ite_false] using ht
    have hstep := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hlk)
    nlinarith

theorem exists_mergedInterval_coordinate {N H y : ℕ} (hH : 0 < H) (hHN : H ≤ N) (hy : y < N) :
    ∃ k < N / H, ∃ j < mergedIntervalLength N H k, H * k + j = y := by
  have hq : 0 < N / H := Nat.div_pos hHN hH
  let k := min (y / H) (N / H - 1)
  have hkleft : k ≤ y / H := Nat.min_le_left _ _
  have hkright : k ≤ N / H - 1 := Nat.min_le_right _ _
  have hk : k < N / H := by omega
  have hdivy : H * (y / H) ≤ y := by simpa only [mul_comm] using Nat.div_mul_le_self y H
  have hstart : H * k ≤ y := (Nat.mul_le_mul_left H hkleft).trans hdivy
  have hj : y - H * k < mergedIntervalLength N H k := by
    by_cases hlast : k + 1 = N / H
    · simp only [mergedIntervalLength, hlast, ite_true]
      omega
    · have hkeq : k = y / H := by
        by_cases hle : y / H ≤ N / H - 1
        · exact min_eq_left hle
        · have heq : k = N / H - 1 := min_eq_right (le_of_not_ge hle)
          omega
      have hdiv := Nat.mod_add_div y H
      have hrem := Nat.mod_lt y hH
      rw [← hkeq] at hdiv
      simp only [mergedIntervalLength, hlast, ite_false]
      omega
  exact ⟨k, hk, y - H * k, hj, by omega⟩

end Erdos3

end

section

namespace Erdos3

theorem truncatedProgressionLength_le (N a q H : ℕ) :
    truncatedProgressionLength N a q H ≤ H := by
  unfold truncatedProgressionLength
  split_ifs
  · exact min_le_left _ _
  · exact Nat.zero_le _

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

noncomputable def restrict (M : ℕ) (hMN : M ≤ N) : FiniteProgressionPartition M := by
  let len (i : P.Label) := truncatedProgressionLength M (P.start i) (P.step i) (P.length i)
  have hlen (i : P.Label) : len i ≤ P.length i := truncatedProgressionLength_le _ _ _ _
  let emb : (Σ i : P.Label, Fin (len i)) → Σ i : P.Label, Fin (P.length i) :=
    Sigma.map id (fun i j => ⟨j.val, j.isLt.trans_le (hlen i)⟩)
  have hemb : Function.Injective emb := by
    apply Function.injective_id.sigma_map
    intro i x y h
    apply Fin.ext
    exact congrArg (fun z : Fin (P.length i) => z.val) h
  let f (x : Σ i : P.Label, Fin (len i)) : Fin M :=
    ⟨P.start x.1 + P.step x.1 * x.2.val,
      ((lt_truncatedProgressionLength_iff (P.step_pos x.1)).mp x.2.isLt).2⟩
  have hrel (x : Σ i : P.Label, Fin (len i)) : (P.equiv (emb x)).val = (f x).val :=
    P.equiv_val x.1 _
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply hemb
      apply P.equiv.injective
      apply Fin.ext
      rw [hrel, hrel, h]
    · intro n
      let y := P.equiv.symm ⟨n.val, n.isLt.trans_le hMN⟩
      have hy : P.start y.1 + P.step y.1 * y.2.val = n.val := by
        rw [← P.equiv_val]
        exact congrArg Fin.val (P.equiv.apply_symm_apply _)
      have hj : y.2.val < len y.1 :=
        (lt_truncatedProgressionLength_iff (P.step_pos y.1)).mpr ⟨y.2.isLt, by rw [hy]; exact n.isLt⟩
      exact ⟨⟨y.1, ⟨y.2.val, hj⟩⟩, Fin.ext hy⟩
  exact {
    Label := P.Label
    labelFintype := P.labelFintype
    start := P.start
    step := P.step
    length := len
    step_pos := P.step_pos
    equiv := Equiv.ofBijective f hf
    equiv_val := fun _ _ => rfl }

@[simp] theorem restrict_start (M : ℕ) (hMN : M ≤ N) (i : P.Label) :
    (P.restrict M hMN).start i = P.start i := rfl

@[simp] theorem restrict_step (M : ℕ) (hMN : M ≤ N) (i : P.Label) :
    (P.restrict M hMN).step i = P.step i := rfl

@[simp] theorem restrict_card (M : ℕ) (hMN : M ≤ N) :
    Fintype.card (P.restrict M hMN).Label = Fintype.card P.Label := rfl

end FiniteProgressionPartition
end Erdos3

end

section

namespace Erdos3.FiniteProgressionPartition

noncomputable def mergedIntervals (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N) :
    FiniteProgressionPartition N := by
  let len : Fin (N / H) → ℕ := fun k => mergedIntervalLength N H k.val
  let f : (Σ k : Fin (N / H), Fin (len k)) → Fin N := fun x =>
    ⟨H * x.1.val + x.2.val, mergedInterval_point_lt x.1.isLt x.2.isLt⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨k, j⟩ ⟨l, t⟩ heq
      have he : H * k.val + j.val = H * l.val + t.val := congrArg Fin.val heq
      have hkl : k = l := Fin.ext (mergedInterval_index_unique k.isLt l.isLt j.isLt t.isLt he)
      cases hkl
      have hjt : j = t := Fin.ext (Nat.add_left_cancel he)
      cases hjt
      rfl
    · intro y
      obtain ⟨k, hk, j, hj, heq⟩ := exists_mergedInterval_coordinate hH hHN y.isLt
      exact ⟨⟨⟨k, hk⟩, ⟨j, hj⟩⟩, Fin.ext heq⟩
  exact {
    Label := Fin (N / H)
    labelFintype := inferInstance
    start := fun k => H * k.val
    step := fun _ => 1
    length := len
    step_pos := fun _ => Nat.zero_lt_one
    equiv := Equiv.ofBijective f hf
    equiv_val := fun _ _ => by simp only [Equiv.ofBijective_apply, f, one_mul] }

@[simp] theorem mergedIntervals_start (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (k : (mergedIntervals N H hH hHN).Label) :
    (mergedIntervals N H hH hHN).start k = H * k.val := rfl

@[simp] theorem mergedIntervals_step (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (k : (mergedIntervals N H hH hHN).Label) :
    (mergedIntervals N H hH hHN).step k = 1 := rfl

@[simp] theorem mergedIntervals_card (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N) :
    Fintype.card (mergedIntervals N H hH hHN).Label = N / H := Fintype.card_fin _

end Erdos3.FiniteProgressionPartition

end

section

namespace Erdos3.FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

noncomputable def bind (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i)) :
    FiniteProgressionPartition N where
  Label := Σ i : P.Label, (Q i).Label
  labelFintype := inferInstance
  start := fun x => P.start x.1 + P.step x.1 * (Q x.1).start x.2
  step := fun x => P.step x.1 * (Q x.1).step x.2
  length := fun x => (Q x.1).length x.2
  step_pos := fun x => Nat.mul_pos (P.step_pos x.1) ((Q x.1).step_pos x.2)
  equiv := (Equiv.sigmaAssoc (fun i j => Fin ((Q i).length j))).trans
    ((Equiv.sigmaCongrRight (fun i => (Q i).equiv)).trans P.equiv)
  equiv_val := by
    intro x j
    change (P.equiv ⟨x.1, (Q x.1).equiv ⟨x.2, j⟩⟩).val = _
    rw [P.equiv_val, (Q x.1).equiv_val]
    ring

@[simp] theorem bind_start (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i))
    (i : P.Label) (j : (Q i).Label) :
    (P.bind Q).start ⟨i, j⟩ = P.start i + P.step i * (Q i).start j := rfl

@[simp] theorem bind_step (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i))
    (i : P.Label) (j : (Q i).Label) :
    (P.bind Q).step ⟨i, j⟩ = P.step i * (Q i).step j := rfl

@[simp] theorem bind_length (Q : ∀ i : P.Label, FiniteProgressionPartition (P.length i))
    (i : P.Label) (j : (Q i).Label) : (P.bind Q).length ⟨i, j⟩ = (Q i).length j := rfl

end Erdos3.FiniteProgressionPartition

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxBlockBudget
namespace OAI

section

namespace Erdos3.BoxProgressionPartition

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

def cell (x : ∀ i, Fin (N i)) : ∀ i, (P i).Label := fun i => (P i).cell (x i)

end Erdos3.BoxProgressionPartition

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3

open scoped NNReal

structure TriangularSlots (d : ℕ) where
  center : (Fin d → ℝ) → Fin d → ℝ
  lower : ∀ i x y, (∀ j, j < i → x j = y j) → center x i = center y i

namespace TriangularSlots

variable {d : ℕ}

def residual (A : TriangularSlots d) (b : Fin d → ℤ) : Fin d → ℝ :=
  fun i => (b i : ℝ) - A.center (fun j => (b j : ℝ)) i

end TriangularSlots

structure PatchKernel (d : ℕ) where
  value : (Fin d → ℝ) → ℝ
  nonneg : ∀ x, 0 ≤ value x
  le_one : ∀ x, value x ≤ 1
  support : ∀ x, value x ≠ 0 → ∀ i, |x i| ≤ 1 / 4
  lip : ℝ≥0
  lipschitz : LipschitzWith lip value

namespace TriangularSlots

variable {d : ℕ} (A : TriangularSlots d) (Φ : PatchKernel d)

noncomputable def patchValue : ℝ := ∑' b : Fin d → ℤ, Φ.value (A.residual b)

end TriangularSlots

end Erdos3

end

section

namespace Erdos3

variable {D E : ℕ}

def slotPrefix {R : Type*} (x : Fin (D + E) → R) : Fin D → R :=
  fun i => x (i.castAdd E)

def slotSuffix {R : Type*} (x : Fin (D + E) → R) : Fin E → R :=
  fun i => x (i.natAdd D)

@[simp] theorem slotPrefix_append {R : Type*} (b : Fin D → R) (c : Fin E → R) :
    slotPrefix (Fin.append b c) = b := by ext i; simp [slotPrefix]

@[simp] theorem slotSuffix_append {R : Type*} (b : Fin D → R) (c : Fin E → R) :
    slotSuffix (Fin.append b c) = c := by ext i; simp [slotSuffix]

namespace TriangularSlots

def append (A : TriangularSlots D) (B : (Fin D → ℝ) → TriangularSlots E) :
    TriangularSlots (D + E) where
  center x := Fin.append (A.center (slotPrefix x)) ((B (slotPrefix x)).center (slotSuffix x))
  lower i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · intro x y hxy
      simp only [Fin.append_left]
      apply A.lower
      intro k hkj
      exact hxy (k.castAdd E) (by simpa only [Fin.lt_def, Fin.val_castAdd] using hkj)
    · intro x y hxy
      simp only [Fin.append_right]
      have hp : slotPrefix x = slotPrefix y := by
        ext k
        exact hxy (k.castAdd E) (by simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; omega)
      rw [hp]
      apply (B (slotPrefix y)).lower
      intro k hkj
      exact hxy (k.natAdd D) (by simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hkj)

end TriangularSlots

end Erdos3

end

section

namespace Erdos3

theorem stable_sort_symm_lt {n : ℕ} (w : Fin n → ℕ) {i j : Fin n}
    (hij : i < j) (hw : w i ≤ w j) :
    (Tuple.sort w).symm i < (Tuple.sort w).symm j := by
  by_contra h
  have hji : (Tuple.sort w).symm j < (Tuple.sort w).symm i :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hij.ne ((Tuple.sort w).symm.injective he.symm))
  have hwji := Tuple.monotone_sort w hji.le
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hwji
  have htie := (Tuple.eq_sort_iff.mp (rfl : Tuple.sort w = Tuple.sort w)).2
    _ _ hji (by simpa only [Equiv.apply_symm_apply] using le_antisymm hwji hw)
  simp only [Equiv.apply_symm_apply] at htie
  exact (lt_asymm hij htie)

structure SlotInterleaving (D E : ℕ) where
  perm : Equiv.Perm (Fin (D + E))
  left_strictMono : StrictMono (fun i : Fin D => perm.symm (i.castAdd E))
  right_strictMono : StrictMono (fun i : Fin E => perm.symm (i.natAdd D))

namespace SlotInterleaving

variable {D E : ℕ}

def left (I : SlotInterleaving D E) (i : Fin D) : Fin (D + E) :=
  I.perm.symm (i.castAdd E)

def right (I : SlotInterleaving D E) (i : Fin E) : Fin (D + E) :=
  I.perm.symm (i.natAdd D)

def fill (I : SlotInterleaving D E) {R : Type*} (x : Fin D → R) (y : Fin E → R) :
    Fin (D + E) → R := fun k => Fin.append x y (I.perm k)

@[simp] theorem fill_left (I : SlotInterleaving D E) {R : Type*}
    (x : Fin D → R) (y : Fin E → R) (i : Fin D) : I.fill x y (I.left i) = x i := by
  simp [fill, left]

@[simp] theorem fill_right (I : SlotInterleaving D E) {R : Type*}
    (x : Fin D → R) (y : Fin E → R) (i : Fin E) : I.fill x y (I.right i) = y i := by
  simp [fill, right]

theorem cases (I : SlotInterleaving D E) {p : Fin (D + E) → Prop}
    (hl : ∀ i, p (I.left i)) (hr : ∀ i, p (I.right i)) (k : Fin (D + E)) : p k := by
  rw [← I.perm.symm_apply_apply k]
  exact Fin.addCases hl hr (I.perm k)

def sorted (w : Fin D → ℕ) (v : Fin E → ℕ) (hw : Monotone w) (hv : Monotone v) :
    SlotInterleaving D E where
  perm := Tuple.sort (Fin.append w v)
  left_strictMono i j hij := stable_sort_symm_lt _
    (by simpa only [Fin.lt_def, Fin.val_castAdd] using hij)
    (by simpa using hw hij.le)
  right_strictMono i j hij := stable_sort_symm_lt _ (by simpa using hij)
    (by simpa using hv hij.le)

theorem sorted_weight_mono (w : Fin D → ℕ) (v : Fin E → ℕ)
    (hw : Monotone w) (hv : Monotone v) :
    Monotone ((sorted w v hw hv).fill w v) := Tuple.monotone_sort _

end SlotInterleaving

theorem dist_restrict_coordinates_le {d n : ℕ} (f : Fin d → Fin n)
    (x y : Fin n → ℝ) : dist (fun i => x (f i)) (fun i => y (f i)) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact dist_le_pi_dist x y (f i)

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {D E d : ℕ}

@[ext] theorem ext {A B : TriangularSlots d}
    (h : ∀ x i, A.center x i = B.center x i) : A = B := by
  have hc : A.center = B.center := funext (fun x => funext (h x))
  cases A
  cases B
  cases hc
  rfl

end Erdos3.TriangularSlots

end

section

namespace Erdos3

variable {D E : ℕ}

namespace TriangularSlots

def interleave (A : TriangularSlots D) (B : TriangularSlots E)
    (I : SlotInterleaving D E) : TriangularSlots (D + E) where
  center x := I.fill (A.center (fun i => x (I.left i)))
    (B.center (fun i => x (I.right i)))
  lower k x y h := by
    apply I.cases (p := fun k =>
      (∀ j, j < k → x j = y j) →
      I.fill (A.center (fun i => x (I.left i))) (B.center (fun i => x (I.right i))) k =
      I.fill (A.center (fun i => y (I.left i))) (B.center (fun i => y (I.right i))) k) _ _ k h
    · intro i hi
      simp only [SlotInterleaving.fill_left]
      exact A.lower i _ _ (fun j hj => hi _ (I.left_strictMono hj))
    · intro i hi
      simp only [SlotInterleaving.fill_right]
      exact B.lower i _ _ (fun j hj => hi _ (I.right_strictMono hj))

@[simp] theorem interleave_residual_left (A : TriangularSlots D) (B : TriangularSlots E)
    (I : SlotInterleaving D E) (z : Fin (D + E) → ℤ) (i : Fin D) :
    (A.interleave B I).residual z (I.left i) = A.residual (fun j => z (I.left j)) i := by
  simp [residual, interleave]

@[simp] theorem interleave_residual_right (A : TriangularSlots D) (B : TriangularSlots E)
    (I : SlotInterleaving D E) (z : Fin (D + E) → ℤ) (i : Fin E) :
    (A.interleave B I).residual z (I.right i) = B.residual (fun j => z (I.right j)) i := by
  simp [residual, interleave]

end TriangularSlots

namespace PatchKernel

def product (Φ : PatchKernel D) (Ψ : PatchKernel E) (I : SlotInterleaving D E) :
    PatchKernel (D + E) where
  value x := Φ.value (fun i => x (I.left i)) * Ψ.value (fun i => x (I.right i))
  nonneg x := mul_nonneg (Φ.nonneg _) (Ψ.nonneg _)
  le_one x := (mul_le_of_le_one_left (Ψ.nonneg _) (Φ.le_one _)).trans (Ψ.le_one _)
  support x hx := by
    have hl := Φ.support _ (mul_ne_zero_iff.mp hx).1
    have hr := Ψ.support _ (mul_ne_zero_iff.mp hx).2
    exact I.cases hl hr
  lip := Φ.lip + Ψ.lip
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    let x₁ := fun i => x (I.left i)
    let x₂ := fun i => x (I.right i)
    let y₁ := fun i => y (I.left i)
    let y₂ := fun i => y (I.right i)
    have hl : dist (Φ.value x₁) (Φ.value y₁) ≤ Φ.lip * dist x y :=
      (Φ.lipschitz.dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left (dist_restrict_coordinates_le I.left x y) Φ.lip.coe_nonneg)
    have hr : dist (Ψ.value x₂) (Ψ.value y₂) ≤ Ψ.lip * dist x y :=
      (Ψ.lipschitz.dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left (dist_restrict_coordinates_le I.right x y) Ψ.lip.coe_nonneg)
    have h₁ : dist (Φ.value x₁ * Ψ.value x₂) (Φ.value y₁ * Ψ.value x₂) ≤
        dist (Φ.value x₁) (Φ.value y₁) := by
      rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_nonneg (Ψ.nonneg _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (Ψ.le_one _)
    have h₂ : dist (Φ.value y₁ * Ψ.value x₂) (Φ.value y₁ * Ψ.value y₂) ≤
        dist (Ψ.value x₂) (Ψ.value y₂) := by
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (Φ.nonneg _)]
      exact mul_le_of_le_one_left (abs_nonneg _) (Φ.le_one _)
    exact (dist_triangle _ (Φ.value y₁ * Ψ.value x₂) _).trans
      ((add_le_add (h₁.trans hl) (h₂.trans hr)).trans_eq (by simp [add_mul]))

@[simp] theorem product_lip (Φ : PatchKernel D) (Ψ : PatchKernel E)
    (I : SlotInterleaving D E) : (Φ.product Ψ I).lip = Φ.lip + Ψ.lip := rfl

@[simp] theorem product_value_fill (Φ : PatchKernel D) (Ψ : PatchKernel E)
    (I : SlotInterleaving D E) (x : Fin D → ℝ) (y : Fin E → ℝ) :
    (Φ.product Ψ I).value (I.fill x y) = Φ.value x * Ψ.value y := by
  simp [product]

end PatchKernel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
namespace OAI

section

open scoped BigOperators

namespace Erdos3

noncomputable def monomialScale {σ : Type*} (T : σ → ℝ) (α : σ →₀ ℕ) : ℝ :=
  α.prod (fun i n => T i ^ n)

@[simp] theorem monomialScale_zero {σ : Type*} (T : σ → ℝ) : monomialScale T 0 = 1 := by
  simp [monomialScale]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Pointwise

variable {σ R : Type*} [CommRing R]

noncomputable def weightedSupportLE (w : σ → ℕ) (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {α | Finsupp.weight w α ≤ d}

theorem weightedSupportLE_monomial (w : σ → ℕ) (α : σ →₀ ℕ) (r : R) :
    monomial α r ∈ weightedSupportLE w (Finsupp.weight w α) := by
  apply (monomial_mem_restrictSupport R).mpr
  left
  change Finsupp.weight w α ≤ Finsupp.weight w α
  exact le_rfl

theorem weightedSupportLE_mul {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (hq : q ∈ weightedSupportLE w e) :
    p * q ∈ weightedSupportLE w (d + e) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hα)
  exact (map_add (Finsupp.weight w) β γ).trans_le (Nat.add_le_add (hp hβ) (hq hγ))

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem weightedSupportLE_mono {w : σ → ℕ} {d e : ℕ} {p : MvPolynomial σ R}
    (hde : d ≤ e) (hp : p ∈ weightedSupportLE w d) : p ∈ weightedSupportLE w e :=
  fun _ h => (hp h).trans hde

theorem weightedSupportLE_C (w : σ → ℕ) (d : ℕ) (r : R) :
    C r ∈ weightedSupportLE w d := by
  exact (monomial_mem_restrictSupport R).mpr (Or.inl (by simp))

theorem weightedSupportLE_X (w : σ → ℕ) (i : σ) :
    (X i : MvPolynomial σ R) ∈ weightedSupportLE w (w i) := by
  simpa only [X, Finsupp.weight_single, one_smul] using
    weightedSupportLE_monomial w (Finsupp.single i 1) (1 : R)

theorem weightedSupportLE_pow {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (n : ℕ) :
    p ^ n ∈ weightedSupportLE w (n * d) := by
  induction n with
  | zero => simpa using weightedSupportLE_C w 0 (1 : R)
  | succ n ih =>
    simpa only [pow_succ, Nat.succ_mul] using weightedSupportLE_mul ih hp

theorem weightedSupportLE_prod {ι : Type*} (s : Finset ι) (w : σ → ℕ)
    (f : ι → MvPolynomial σ R) (d : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ weightedSupportLE w (d i)) :
    (∏ i ∈ s, f i) ∈ weightedSupportLE w (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weightedSupportLE_C w 0 (1 : R)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact weightedSupportLE_mul (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem weightedSupportLE_aeval_monomial (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ R) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    (α : σ →₀ ℕ) (r : R) :
    aeval (R := R) f (monomial α r) ∈ weightedSupportLE v (Finsupp.weight w α) := by
  classical
  rw [aeval_monomial]
  have hprod := weightedSupportLE_prod α.support v (fun i => f i ^ α i)
    (fun i => α i * w i) (fun i _ => weightedSupportLE_pow (hf i) (α i))
  have hweight : (∑ i ∈ α.support, α i * w i) = Finsupp.weight w α := by
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id]
  rw [hweight] at hprod
  simpa only [zero_add, MvPolynomial.algebraMap_eq, Finsupp.prod] using
    weightedSupportLE_mul (weightedSupportLE_C v 0 r) hprod

theorem weightedSupportLE_aeval (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ R) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    aeval (R := R) f p ∈ weightedSupportLE v d := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportLE v d).sum_mem
  intro α hα
  exact weightedSupportLE_mono (hp hα) (weightedSupportLE_aeval_monomial w v f hf α _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

def earlierSlot {d : ℕ} (i : Fin d) (j : Fin i.val) : Fin d :=
  ⟨j.val, lt_trans j.isLt i.isLt⟩

def patchVariableWeight {σ : Type*} {d : ℕ} (w : Fin d → ℕ) (i : Fin d) :
    σ ⊕ Fin i.val → ℕ := Sum.elim (fun _ => 1) (fun j => w (earlierSlot i j))

structure PolynomialSlots (σ : Type*) (d : ℕ) (w : Fin d → ℕ) where
  center : (i : Fin d) → MvPolynomial (σ ⊕ Fin i.val) ℝ
  degree : ∀ i, center i ∈ weightedSupportLE (patchVariableWeight w i) (w i)

namespace PolynomialSlots

variable {σ : Type*} {d D E : ℕ} {w : Fin d → ℕ}

noncomputable def slots (A : PolynomialSlots σ d w) (t : σ → ℝ) : TriangularSlots d where
  center x i := aeval (Sum.elim t (fun j => x (earlierSlot i j))) (A.center i)
  lower i x y hxy := by
    apply congrArg (fun f : σ ⊕ Fin i.val → ℝ => aeval f (A.center i))
    funext v
    cases v with
    | inl a => rfl
    | inr j => exact hxy (earlierSlot i j) (by simpa only [Fin.lt_def, earlierSlot] using j.isLt)

end PolynomialSlots

structure PolynomialPatch (σ : Type*) (s d : ℕ) where
  weight : Fin d → ℕ
  weight_pos : ∀ i, 1 ≤ weight i
  weight_le : ∀ i, weight i ≤ s
  weight_mono : Monotone weight
  form : PolynomialSlots σ d weight
  kernel : PatchKernel d

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

noncomputable def value (A : PolynomialPatch σ s d) (t : σ → ℝ) : ℝ :=
  (A.form.slots t).patchValue A.kernel

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def parameterSubstitution (f : σ → MvPolynomial τ ℝ) (i : Fin d) :
    σ ⊕ Fin i.val → MvPolynomial (τ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => aeval (fun b => X (Sum.inl b)) (f a)) (fun j => X (Sum.inr j))

theorem parameterSubstitution_degree (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (i : Fin d)
    (v : σ ⊕ Fin i.val) :
    parameterSubstitution f i v ∈
      weightedSupportLE (patchVariableWeight (σ := τ) w i)
        (patchVariableWeight (σ := σ) w i v) := by
  cases v with
  | inl a =>
    apply weightedSupportLE_aeval (fun _ : τ => 1) (patchVariableWeight w i)
    · intro b
      exact weightedSupportLE_X _ (Sum.inl b)
    · exact hf a
  | inr j => exact weightedSupportLE_X _ (Sum.inr j)

noncomputable def reparam (A : PolynomialSlots σ d w) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) : PolynomialSlots τ d w where
  center i := aeval (parameterSubstitution f i) (A.center i)
  degree i := weightedSupportLE_aeval _ _ _ (parameterSubstitution_degree f hf i) (A.degree i)

end PolynomialSlots

namespace PolynomialPatch

variable {σ τ : Type*} {s d : ℕ}

noncomputable def reparam (A : PolynomialPatch σ s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) : PolynomialPatch τ s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := A.form.reparam f hf
  kernel := A.kernel

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d n D E : ℕ}

noncomputable def placementSubstitution (f : Fin d → Fin n) (k : Fin n) (i : Fin d) :
    σ ⊕ Fin i.val → MvPolynomial (σ ⊕ Fin k.val) ℝ :=
  Sum.elim (fun a => X (Sum.inl a)) (fun j =>
    if h : (f (earlierSlot i j)).val < k.val then X (Sum.inr ⟨_, h⟩) else 0)

theorem placementSubstitution_degree {w : Fin d → ℕ} {v : Fin n → ℕ}
    (f : Fin d → Fin n) (hweight : ∀ i, v (f i) = w i) (k : Fin n) (i : Fin d)
    (a : σ ⊕ Fin i.val) :
    placementSubstitution f k i a ∈
      weightedSupportLE (patchVariableWeight v k) (patchVariableWeight w i a) := by
  cases a with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
    simp only [placementSubstitution, Sum.elim_inr]
    split_ifs with h
    · have hX := weightedSupportLE_X (R := ℝ) (patchVariableWeight (σ := σ) v k)
        (Sum.inr (⟨(f (earlierSlot i j)).val, h⟩ : Fin k.val))
      change _ ∈ weightedSupportLE _ (v (f (earlierSlot i j))) at hX
      rw [hweight] at hX
      exact hX
    · exact (weightedSupportLE _ _).zero_mem

noncomputable def placeCenter {w : Fin d → ℕ} (A : PolynomialSlots σ d w)
    (f : Fin d → Fin n) (k : Fin n) (i : Fin d) :
    MvPolynomial (σ ⊕ Fin k.val) ℝ := aeval (placementSubstitution f k i) (A.center i)

theorem placeCenter_degree {w : Fin d → ℕ} {v : Fin n → ℕ}
    (A : PolynomialSlots σ d w) (f : Fin d → Fin n)
    (hweight : ∀ i, v (f i) = w i) (k : Fin n) (i : Fin d) :
    A.placeCenter f k i ∈ weightedSupportLE (patchVariableWeight v k) (w i) :=
  weightedSupportLE_aeval _ _ _ (placementSubstitution_degree f hweight k i) (A.degree i)

noncomputable def interleave {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : PolynomialSlots σ D w) (B : PolynomialSlots σ E v) (I : SlotInterleaving D E) :
    PolynomialSlots σ (D + E) (I.fill w v) where
  center k := Fin.addCases (A.placeCenter I.left k) (B.placeCenter I.right k) (I.perm k)
  degree k := by
    change Fin.addCases (A.placeCenter I.left k) (B.placeCenter I.right k) (I.perm k) ∈
      weightedSupportLE (patchVariableWeight (I.fill w v) k) (Fin.append w v (I.perm k))
    generalize I.perm k = z
    refine Fin.addCases (fun i => ?_) (fun i => ?_) z
    · simpa only [Fin.addCases_left, Fin.append_left] using
        A.placeCenter_degree I.left (fun j => I.fill_left w v j) k i
    · simpa only [Fin.addCases_right, Fin.append_right] using
        B.placeCenter_degree I.right (fun j => I.fill_right w v j) k i

@[simp] theorem interleave_center_left {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : PolynomialSlots σ D w) (B : PolynomialSlots σ E v) (I : SlotInterleaving D E)
    (i : Fin D) : (A.interleave B I).center (I.left i) = A.placeCenter I.left (I.left i) i := by
  simp [interleave, SlotInterleaving.left]

@[simp] theorem interleave_center_right {w : Fin D → ℕ} {v : Fin E → ℕ}
    (A : PolynomialSlots σ D w) (B : PolynomialSlots σ E v) (I : SlotInterleaving D E)
    (i : Fin E) : (A.interleave B I).center (I.right i) = B.placeCenter I.right (I.right i) i := by
  simp [interleave, SlotInterleaving.right]

end PolynomialSlots

end Erdos3

end

section

namespace Erdos3

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

def constant (σ : Type*) (s : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    PolynomialPatch σ s 0 where
  weight := Fin.elim0
  weight_pos := fun i => Fin.elim0 i
  weight_le := fun i => Fin.elim0 i
  weight_mono i := Fin.elim0 i
  form := { center := fun i => Fin.elim0 i, degree := fun i => Fin.elim0 i }
  kernel := {
    value := fun _ => c
    nonneg := fun _ => hc.1
    le_one := fun _ => hc.2
    support := fun _ _ i => Fin.elim0 i
    lip := 0
    lipschitz := LipschitzWith.const c }

@[simp] theorem constant_lip (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (constant σ s c hc).kernel.lip = 0 := rfl

noncomputable def product (A : PolynomialPatch σ s D) (B : PolynomialPatch σ s E) :
    PolynomialPatch σ s (D + E) :=
  let I := SlotInterleaving.sorted A.weight B.weight A.weight_mono B.weight_mono
  { weight := I.fill A.weight B.weight
    weight_pos := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_pos i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_pos i)
    weight_le := I.cases (fun i => by simpa only [SlotInterleaving.fill_left] using A.weight_le i)
      (fun i => by simpa only [SlotInterleaving.fill_right] using B.weight_le i)
    weight_mono := SlotInterleaving.sorted_weight_mono _ _ _ _
    form := A.form.interleave B.form I
    kernel := A.kernel.product B.kernel I }

@[simp] theorem product_lip (A : PolynomialPatch σ s D) (B : PolynomialPatch σ s E) :
    (A.product B).kernel.lip = A.kernel.lip + B.kernel.lip := rfl

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
namespace OAI

section

namespace Erdos3

structure ResidueBoxSlice {ι : Type*} (N : ι → ℕ) (q : ℕ) where
  start : ι → ℕ
  length : ι → ℕ
  inside : ∀ i j, j < length i → start i + q * j < N i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple
namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev PrincipalTupleIndex {D : Type*} (B : D → Type*) (h : D → ℕ) :=
  Σ d, B d × Fin (h d)

abbrev SamplerTupleIndex {D : Type*} (G : Type*) (B : D → Type*) (h : D → ℕ) :=
  G ⊕ PrincipalTupleIndex B h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealWeightPMF
namespace OAI

section

namespace Erdos3

open scoped ENNReal

noncomputable def realWeightPMF {X : Type*} (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : Summable w) (hZ : 0 < ∑' x, w x) : PMF X :=
  ⟨fun x => ENNReal.ofReal (w x / ∑' y, w y), ENNReal.summable.hasSum_iff.mpr (by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => div_nonneg (hw x) hZ.le) (hs.div_const _),
      tsum_div_const, div_self hZ.ne', ENNReal.ofReal_one])⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalBlockExponent
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def productBlockExponent {K : Type*} {h : ℕ} (principal : Fin h → K) : K →₀ ℕ :=
  ∑ v, Finsupp.single (principal v) 1

noncomputable def canonicalPrincipalExponent {D G : Type*} {B : D → Type*} (h : D → ℕ)
    (d : D) (b : B d) : SamplerTupleIndex G B h →₀ ℕ :=
  productBlockExponent (fun v => .inr ⟨d, b, v⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveAxisScale
namespace OAI

section

namespace Erdos3

noncomputable def inactiveSideLength (h K q : ℕ) : ℕ :=
  if 2 * q ≤ K then Nat.nthRoot h (K / q) else 1

def inactivePrincipalCoefficient (K q : ℕ) : ℤ := if 2 * q ≤ K then 1 else 0

theorem inactiveSideLength_pos {h K q : ℕ} (hh : 0 < h) (hq : 0 < q) :
    0 < inactiveSideLength h K q := by
  by_cases hlarge : 2 * q ≤ K
  · have hdiv : 2 ≤ K / q := (Nat.le_div_iff_mul_le hq).mpr hlarge
    have hroot : 1 ≤ Nat.nthRoot h (K / q) :=
      (Nat.le_nthRoot_iff hh.ne').mpr (by simpa only [one_pow] using (by omega : 1 ≤ K / q))
    simpa [inactiveSideLength, hlarge, Nat.succ_le_iff] using hroot
  · simp [inactiveSideLength, hlarge]

theorem inactiveSideLength_power {h K q : ℕ} (hh : 0 < h) (hlarge : 2 * q ≤ K) :
    inactiveSideLength h K q ^ h ≤ K / q := by
  simpa [inactiveSideLength, hlarge] using (Nat.pow_nthRoot_le (.inl hh.ne') : Nat.nthRoot h (K / q) ^ h ≤ K / q)

theorem inactiveSideLength_le {h K q L : ℕ} (hh : 0 < h) (hL : 0 < L)
    (hK : K ≤ L ^ h) : inactiveSideLength h K q ≤ L := by
  by_cases hlarge : 2 * q ≤ K
  · apply (Nat.pow_left_strictMono hh.ne').le_iff_le.mp
    exact (inactiveSideLength_power hh hlarge).trans ((Nat.div_le_self K q).trans hK)
  · simpa [inactiveSideLength, hlarge] using (show 1 ≤ L by omega)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.InactivePrincipalLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def inactivePrincipalPMF (K q : ℕ) : PMF ℤ :=
  PMF.pure (inactivePrincipalCoefficient K q)

noncomputable def inactiveDenominator (γ : ℝ) : ℕ := max 1 ⌈γ⁻¹⌉₊

theorem inactiveDenominator_pos (γ : ℝ) : 0 < inactiveDenominator γ :=
  Nat.zero_lt_one.trans_le (le_max_left _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothSplitSampling
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def shiftedSmoothSampleSum (a S : ℝ) : ℝ :=
  ∑' k : ℤ, smoothProbabilityProfile (((k : ℝ) - a) / S)

theorem shiftedSmoothSamples_summable (a : ℝ) {S : ℝ} (hS : 0 < S) :
    Summable (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - a) / S)) :=
  (hasSum_sum_of_ne_finset_zero (sampledWeight_zero_off_indices smoothProbabilityProfile
    (a := a) hS smoothProbabilityProfile_zero_outside)).summable

theorem shiftedSmoothSampleSum_error (a : ℝ) {S : ℝ} (hS : 1 ≤ S) :
    |shiftedSmoothSampleSum a S / S - 1| ≤ 4 * (probabilityProfileLipschitz : ℝ) / S := by
  have he := sampledWeightSum_error smoothProbabilityProfile smoothProbabilityProfile_lipschitz
    (a := a) zero_le_one hS smoothProbabilityProfile_zero_outside
  rw [sampledWeightSum_eq_tsum _ (zero_lt_one.trans_le hS) smoothProbabilityProfile_zero_outside] at he
  simpa only [shiftedSmoothSampleSum, smoothProbabilityProfile_integral,
    show (2 : ℝ) * 1 + 2 = 4 by norm_num] using he

theorem shiftedSmoothSampleSum_pos (a : ℝ) {S : ℝ}
    (hS : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) : 0 < shiftedSmoothSampleSum a S := by
  have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hS1 : 1 ≤ S := by linarith
  have he := shiftedSmoothSampleSum_error a hS1
  have hsmall : 4 * (probabilityProfileLipschitz : ℝ) / S ≤ 1 / 2 :=
    (div_le_iff₀ (zero_lt_one.trans_le hS1)).mpr (by linarith)
  have hlo := (abs_le.mp (he.trans hsmall)).1
  have hpos : 0 < shiftedSmoothSampleSum a S / S := by linarith
  rcases div_pos_iff.mp hpos with h | h
  · exact h.1
  · linarith [h.2]

noncomputable def shiftedSmoothCoefficientPMF (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) : PMF ℤ :=
  realWeightPMF (fun k => smoothProbabilityProfile (((k : ℝ) - a) / S))
    (fun _ => (smoothProbabilityProfile_range _).1) (shiftedSmoothSamples_summable a hS) hZ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientScaleGap
namespace OAI

section

namespace Erdos3

theorem coefficient_gap_principal_width {K L A γ : ℝ} {h : ℕ}
    (hL : 0 < L) (hA : 1 ≤ A) (hγ : 0 < γ) (hh : 1 ≤ h)
    (hgap : (A * L) ^ h ≤ K)
    (hwidth : 16 * (probabilityProfileLipschitz : ℝ) ≤ γ * A) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / L ^ h) := by
  have hpow : A ≤ A ^ h := by simpa only [pow_one] using pow_le_pow_right₀ hA hh
  have hratio : A ≤ K / L ^ h := (le_div_iff₀ (pow_pos hL h)).mpr (by
    calc
      A * L ^ h ≤ A ^ h * L ^ h := mul_le_mul_of_nonneg_right hpow (pow_pos hL h).le
      _ = (A * L) ^ h := (mul_pow A L h).symm
      _ ≤ K := hgap)
  have hm := mul_le_mul_of_nonneg_left hratio hγ.le
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreePrimitiveCriterion
namespace OAI

section

namespace Erdos3
variable {X : Type*}

noncomputable def freeWord : FreeMonoid X →* FreeAlgebra ℚ X :=
  FreeMonoid.lift (FreeAlgebra.ι ℚ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialIntegerInputs
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

def RationalPolynomialHeightLE {σ : Type*} (p : MvPolynomial σ ℚ) (H : ℕ) : Prop :=
  ∀ m, RationalHeightLE (p.coeff m) H

namespace RationalPolynomialHeightLE

variable {σ : Type*} {p : MvPolynomial σ ℚ} {H K : ℕ}

theorem sum {ι : Type*} [Fintype ι] (p : ι → MvPolynomial σ ℚ)
    (hp : ∀ i, RationalPolynomialHeightLE (p i) H) :
    RationalPolynomialHeightLE (∑ i, p i) ((Fintype.card ι + 1) * H ^ Fintype.card ι) := by
  classical
  intro m
  rw [coeff_sum]
  exact rationalHeightLE_sum (fun i => (p i).coeff m) (fun i => hp i m)

end RationalPolynomialHeightLE

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

abbrev BoundedCoefficientExponent (K : Type*) (h : ℕ) :=
  {d : K →₀ ℕ // d.degree ≤ h}

noncomputable instance boundedCoefficientExponentFintype (K : Type*) [Fintype K] (h : ℕ) :
    Fintype (BoundedCoefficientExponent K h) := (Finsupp.finite_of_degree_le h).fintype

abbrev CoefficientSlot (K : Type*) (m : ℕ) :=
  Σ j : Fin m, BoundedCoefficientExponent K (j.val + 1)

abbrev CoefficientArray {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) := ∀ s : CoefficientSlot K m, U s.1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem productBlockExponent_degree {K : Type*} {h : ℕ} (principal : Fin h → K) :
    (productBlockExponent principal).degree = h := by
  simp [productBlockExponent, map_sum, Finsupp.degree_single]

theorem canonicalPrincipalExponent_degree {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (b : B d) :
    (canonicalPrincipalExponent (G := G) h d b).degree = h d :=
  productBlockExponent_degree _

def constantCoefficientSlot (K : Type*) (h : ℕ) : BoundedCoefficientExponent K h :=
  ⟨0, by simp⟩

noncomputable def principalCoefficientSlot {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (b : B d) :
    BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) :=
  ⟨canonicalPrincipalExponent h d b, (canonicalPrincipalExponent_degree h d b).le⟩

noncomputable def principalCoefficientSlots {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [Fintype (B d)] :
    Finset (BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) := by
  classical
  exact Finset.univ.image (principalCoefficientSlot h d)

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

noncomputable def normalizedIntegerPMF (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) : PMF ℤ :=
  shiftedSmoothCoefficientPMF (c * K) (δ * K) (mul_pos hδ hK)
    (shiftedSmoothSampleSum_pos (c * K) hlarge)

end Erdos3

end

section

namespace Erdos3

noncomputable def constantIntegerPMF (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) : PMF ℤ :=
  if h : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K then
    normalizedIntegerPMF K 0 δ hK hδ h
  else PMF.pure 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PrincipalCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def principalIntegerPMF (K T γ : ℝ) (hK : 0 < K) (hT : 0 < T)
    (hγ : 0 < γ) (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) : PMF ℤ :=
  normalizedIntegerPMF (K / T) (3 * γ / 2) (γ / 2) (div_pos hK hT) (by positivity) hlarge

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PrincipalSamplingScale
namespace OAI

section

namespace Erdos3

noncomputable def principalSamplingGapRatio (γ : ℝ) : ℕ :=
  ⌈max 1 (16 * (probabilityProfileLipschitz : ℝ) / γ)⌉₊

theorem principalSamplingGapRatio_one_le (γ : ℝ) : 1 ≤ principalSamplingGapRatio γ := by
  have h : (1 : ℝ) ≤ (principalSamplingGapRatio γ : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  exact_mod_cast h

theorem principalSamplingGapRatio_width {γ : ℝ} (hγ : 0 < γ) :
    16 * (probabilityProfileLipschitz : ℝ) ≤ γ * principalSamplingGapRatio γ := by
  have h : 16 * (probabilityProfileLipschitz : ℝ) / γ ≤ (principalSamplingGapRatio γ : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  have hb := (div_le_iff₀ hγ).mp h
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAxisPrincipalLaw
namespace OAI

section

namespace Erdos3

noncomputable def integerAxisSideLength (h K L : ℕ) (γ : ℝ) : ℕ :=
  if L ^ h < K then L else inactiveSideLength h K (inactiveDenominator γ)

theorem integerAxisSideLength_pos {h K L : ℕ} (hh : 0 < h) (hL : 0 < L) (γ : ℝ) :
    0 < integerAxisSideLength h K L γ := by
  unfold integerAxisSideLength
  split_ifs
  · exact hL
  · exact inactiveSideLength_pos hh (inactiveDenominator_pos γ)

theorem integerAxisSideLength_le {h K L : ℕ} (hh : 0 < h) (hL : 0 < L) (γ : ℝ) :
    integerAxisSideLength h K L γ ≤ L := by
  unfold integerAxisSideLength
  split_ifs with ha
  · exact le_rfl
  · exact inactiveSideLength_le hh hL (Nat.le_of_not_gt ha)

theorem integerAxisPrincipal_width {h K L : ℕ} (hh : 0 < h) (hL : 0 < L)
    {γ : ℝ} (hγ : 0 < γ)
    (hgap : (principalSamplingGapRatio γ * L) ^ h ≤ K) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * ((K : ℝ) / (L : ℝ) ^ h) := by
  apply coefficient_gap_principal_width (A := (principalSamplingGapRatio γ : ℝ)) (by exact_mod_cast hL)
    (by exact_mod_cast principalSamplingGapRatio_one_le γ) hγ hh
  · exact_mod_cast hgap
  · exact principalSamplingGapRatio_width hγ

noncomputable def integerAxisPrincipalPMF (h K L : ℕ) (hh : 0 < h) (hK : 0 < K)
    (hL : 0 < L) (γ : ℝ) (hγ : 0 < γ)
    (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K) : PMF ℤ :=
  if ha : L ^ h < K then
    principalIntegerPMF K ((L : ℝ) ^ h) γ (by exact_mod_cast hK)
      (pow_pos (by exact_mod_cast hL) _) hγ (integerAxisPrincipal_width hh hL hγ (hgap ha))
  else inactivePrincipalPMF K (inactiveDenominator γ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Compat
/-!
Backports of Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to Mathlib 0df444a, with
the same names and statements and Mathlib's own proofs (Apache-2.0).
-/

namespace Finset

/-- Backport (Mathlib d13f23b), additive form of `prod_le_prod_of_injOn`. -/
theorem sum_le_sum_of_injOn {ι α N : Type*} [AddCommMonoid N] [PartialOrder N]
    [IsOrderedAddMonoid N] [DecidableEq α]
    {f : ι → N} {g : α → N} {s : Finset ι} {t : Finset α} (e : ι → α) (he : Set.InjOn e s)
    (ht : image e s ⊆ t) (h : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ a ∈ t, a ∉ image e s → 0 ≤ g a) :
    ∑ i ∈ s, f i ≤ ∑ a ∈ t, g a := by
  refine le_trans ?_ <| sum_le_sum_of_subset_of_nonneg ht hg
  rw [sum_image he]
  exact sum_le_sum h

end Finset
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisAxisNormalization
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def basisAxisScale (b : Basis I ℝ E) (i : I) : ℕ := ⌈‖b i‖⁻¹⌉₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))

noncomputable def euclideanSubspace : Submodule ℝ (EuclideanSpace ℝ D) :=
  U.comap (PiLp.continuousLinearEquiv 2 ℝ (fun _ : D => ℝ)).toLinearMap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

def coefficientIntegerLattice {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) : AddSubgroup (CoefficientArray (K := K) U) where
  carrier := {x | ∀ s a, ∃ n : ℤ, (x s).val a = n}
  zero_mem' s a := ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy s a
    obtain ⟨n, hn⟩ := hx s a
    obtain ⟨m, hm⟩ := hy s a
    refine ⟨n + m, ?_⟩
    change (x s).val a + (y s).val a = ((n + m : ℤ) : ℝ)
    rw [hn, hm, Int.cast_add]
  neg_mem' := by
    intro x hx s a
    obtain ⟨n, hn⟩ := hx s a
    refine ⟨-n, ?_⟩
    change -(x s).val a = ((-n : ℤ) : ℝ)
    rw [hn, Int.cast_neg]

abbrev CoefficientTorus {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :=
  CoefficientArray (K := K) U ⧸ coefficientIntegerLattice U

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EmptyCoefficientDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

abbrev CoefficientSamplerArrays (I : Fin m → Type*) (n : Fin m → ℕ) :=
  ∀ j : Fin m,
    (I j → BoundedCoefficientExponent K (j.val + 1) → ℝ) ×
      (Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℤ)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale
namespace OAI

section

namespace Erdos3

noncomputable def heterogeneousSamplerSides {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (K : D → Option ℕ) (L : ℕ) (γ : D → ℝ) : SamplerTupleIndex G B h → ℕ
  | .inl _ => L
  | .inr ⟨d, _, _⟩ => match K d with
    | none => L
    | some k => integerAxisSideLength (h d) k L (γ d)

theorem heterogeneousSamplerSides_pos {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (K : D → Option ℕ) {L : ℕ} (hL : 0 < L) (γ : D → ℝ)
    (v : SamplerTupleIndex G B h) : 0 < heterogeneousSamplerSides h K L γ v := by
  rcases v with g | ⟨d, b, v⟩
  · exact hL
  · simp only [heterogeneousSamplerSides]
    cases K d with
    | none => exact hL
    | some k => exact integerAxisSideLength_pos (hh d) hL (γ d)

theorem heterogeneousSamplerSides_le {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (K : D → Option ℕ) {L : ℕ} (hL : 0 < L) (γ : D → ℝ)
    (v : SamplerTupleIndex G B h) : heterogeneousSamplerSides h K L γ v ≤ L := by
  rcases v with g | ⟨d, b, v⟩
  · exact le_rfl
  · simp only [heterogeneousSamplerSides]
    cases K d with
    | none => exact le_rfl
    | some k => exact integerAxisSideLength_le (hh d) hL (γ d)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ}

abbrev LayerSamplerAxis (I : Fin m → Type*) (n : Fin m → ℕ) :=
  Σ j : Fin m, I j ⊕ Fin (n j)

def layerSamplerDegree (I : Fin m → Type*) (n : Fin m → ℕ) : LayerSamplerAxis I n → ℕ :=
  fun a => a.1.val + 1

abbrev LayerSamplerVariables (G : Type*) (I : Fin m → Type*) (n : Fin m → ℕ)
    (B : LayerSamplerAxis I n → Type*) := SamplerTupleIndex G B (layerSamplerDegree I n)

variable {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def layerContinuousPrincipalSlots (j : Fin m) (i : I j) :
    Finset (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :=
  principalCoefficientSlots (layerSamplerDegree I n) ⟨j, Sum.inl i⟩

noncomputable def layerIntegerPrincipalSlots (j : Fin m) (i : Fin (n j)) :
    Finset (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :=
  principalCoefficientSlots (layerSamplerDegree I n) ⟨j, Sum.inr i⟩

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable def layerSamplerDenominators : LayerSamplerAxis I n → Option ℕ :=
  fun a => Sum.elim (fun _ => none) (fun i => some (basisAxisScale (b a.1) i)) a.2

noncomputable def layerSamplerWidths (R : Fin m → ℝ) : LayerSamplerAxis I n → ℝ :=
  fun a => principalProfileSize (R a.1) (Fintype.card (B a))

noncomputable def layerSamplerSides (R : Fin m → ℝ) (L : ℕ) : LayerSamplerVariables G I n B → ℕ :=
  heterogeneousSamplerSides (layerSamplerDegree I n) (layerSamplerDenominators U b) L
    (layerSamplerWidths B R)

theorem layerSamplerSides_pos (R : Fin m → ℝ) {L : ℕ} (hL : 0 < L)
    (v : LayerSamplerVariables G I n B) : 0 < layerSamplerSides B U b R L v :=
  heterogeneousSamplerSides_pos _ (fun _ => Nat.zero_lt_succ _) _ hL _ v

theorem layerSamplerSides_le (R : Fin m → ℝ) {L : ℕ} (hL : 0 < L)
    (v : LayerSamplerVariables G I n B) : layerSamplerSides B U b R L v ≤ L :=
  heterogeneousSamplerSides_le _ (fun _ => Nat.zero_lt_succ _) _ hL _ v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable def layerSamplerTailWidth (R σ : Fin m → ℝ) (j : Fin m) : ℝ :=
  tailProfileSize (R j) (σ j)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)))

noncomputable def layerSamplerGapWidth (R : Fin m → ℝ) (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  principalProfileSize (R a.1) (layerIntegerPrincipalSlots (G := G) B a.1 a.2).card

structure LayerSamplerScale (R σ : Fin m → ℝ) where
  value : ℕ
  positive : 0 < value
  width : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤ layerSamplerTailWidth (G := G) B R σ j * value
  gap : ∀ j i, value ^ (j.val + 1) < basisAxisScale (b j) i →
    (principalSamplingGapRatio (layerSamplerGapWidth (G := G) B R ⟨j, i⟩) * value) ^ (j.val + 1) ≤
      basisAxisScale (b j) i

noncomputable def layerSamplerBox {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (v : LayerSamplerVariables G I n B) : ℝ := layerSamplerSides B U b R S.value v

theorem layerSamplerBox_one_le {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (v : LayerSamplerVariables G I n B) : 1 ≤ layerSamplerBox B U b S v := by
  have h : 1 ≤ layerSamplerSides B U b R S.value v :=
    Nat.succ_le_of_lt (layerSamplerSides_pos B U b R S.positive v)
  unfold layerSamplerBox
  exact_mod_cast h

theorem layerSamplerBox_le {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (v : LayerSamplerVariables G I n B) : layerSamplerBox B U b S v ≤ S.value := by
  unfold layerSamplerBox
  exact_mod_cast layerSamplerSides_le B U b R S.positive v

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def allocatedArrayCenters {I J V : Type*} (e : J → V →₀ ℕ) (T : V → ℝ)
    (Pc : I → Finset J) (R : ℝ) (i : I) (j : J) : ℝ :=
  coefficientProfileCenter (Pc i) (principalProfileSize R (Pc i).card) j / monomialScale T (e j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedLayerCenters (j : Fin m) :
    I j → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ :=
  allocatedArrayCenters Subtype.val (layerSamplerBox B U b S) (layerContinuousPrincipalSlots B j) (R j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedPatternPartition
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev OrderedRegularityStepSchedule (r : ℕ) := Fin r → ℕ

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSourceDensityParameter
namespace OAI

section

namespace Erdos3

noncomputable def densityParameter (α : ℝ) : ℝ := max 2 (Real.log (2 / α))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def intervalIndicator (S : Finset ℕ) (n : ℕ) : ℝ := if n ∈ S then 1 else 0

noncomputable def intervalDensity (N : ℕ) (S : Finset ℕ) : ℝ := S.card / (N : ℝ)

theorem intervalDensity_pos {N : ℕ} {S : Finset ℕ} (hN : 0 < N) (hS : S.Nonempty) :
    0 < intervalDensity N S :=
  div_pos (by exact_mod_cast Finset.card_pos.mpr hS) (by exact_mod_cast hN)

def progressionPreimage (S : Finset ℕ) (a q M : ℕ) : Finset ℕ :=
  (Finset.range M).filter fun n => a + q * n ∈ S

theorem progressionPreimage_subset (S : Finset ℕ) (a q M : ℕ) :
    progressionPreimage S a q M ⊆ Finset.range M := Finset.filter_subset _ _

theorem APFree.progressionPreimage {S : Finset ℕ} {k : ℕ} (hS : APFree (S : Set ℕ) k)
    (a q M : ℕ) (hq : 0 < q) : APFree (progressionPreimage S a q M : Set ℕ) k := by
  apply (hS.affine_preimage a q hq).mono
  intro n hn
  exact (Finset.mem_filter.mp hn).2

theorem intervalDensity_pos_iff {N : ℕ} {S : Finset ℕ} (hN : 0 < N) :
    0 < intervalDensity N S ↔ S.Nonempty := by
  constructor
  · intro h
    by_contra hn
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he, intervalDensity] at h
  · exact intervalDensity_pos hN

end Erdos3

end

section

namespace Erdos3

structure APFreeInterval (k : ℕ) where
  length : ℕ
  length_gt_one : 1 < length
  points : Finset ℕ
  subset : points ⊆ Finset.range length
  nonempty : points.Nonempty
  free : APFree (points : Set ℕ) k

namespace APFreeInterval

variable {k : ℕ}

noncomputable def density (S : APFreeInterval k) : ℝ := intervalDensity S.length S.points

noncomputable def parameter (S : APFreeInterval k) : ℝ := densityParameter S.density

def reindex (S : APFreeInterval k) (a q len : ℕ) (hq : 0 < q) (hlen : 1 < len)
    (hpos : 0 < intervalDensity len (progressionPreimage S.points a q len)) : APFreeInterval k where
  length := len
  length_gt_one := hlen
  points := progressionPreimage S.points a q len
  subset := progressionPreimage_subset _ _ _ _
  nonempty := (intervalDensity_pos_iff (by omega)).mp hpos
  free := S.free.progressionPreimage a q len hq

end APFreeInterval

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntervalIntegerVectorAPFree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace APFreeInterval

noncomputable def integerIndicator {k : ℕ} (S : APFreeInterval k) (x : Unit → ℤ) : ℝ :=
  intervalIndicator S.points (x ()).toNat

@[simp] theorem integerIndicator_nat {k : ℕ} (S : APFreeInterval k) (n : ℕ) :
    S.integerIndicator (fun _ => (n : ℤ)) = intervalIndicator S.points n := by
  simp [integerIndicator]

end APFreeInterval

end Erdos3

end

end OAI
end


