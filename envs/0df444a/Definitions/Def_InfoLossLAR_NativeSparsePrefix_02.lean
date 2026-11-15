-- Prove2me | Definitions.Def_InfoLossLAR_NativeSparsePrefix_02
-- name    : InfoLossLAR_NativeSparsePrefix_02
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T13:21:19.326058+00:00
-- url     : https://prove2.me/theorems/a785735f-c724-4988-85ac-de528a2f7776
-- title:
--   Trimmed palettes, Gaussian windows, and finite quantization
-- statement:
--   This package defines trimmed palette and charge objects, finite source windows, Gaussian reflection and convolution interfaces, dyadic quantization and fair-bit sampling, rational elementary-function programs, and anchored primary calibration data.
--
--   These interfaces retain ideal Gaussian source laws separate from their finite rational approximations and keep protected-window and palette constraints explicit. They expose mathematical data and the supporting constructor APIs; the subsequent response, approximation, and transport bounds are stated as separate theorems. Recorded native operation charges are not by themselves platform machine-time certificates.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; Lean source modules AFT/TrimmedSlice.lean, AFT/PrimaryCalibration.lean, AFT/Charge.lean, AFT/TrimmedPalette.lean, AFT/SignCalibration.lean, AFT/SignCalibrationParameters.lean, AFT/BetaPrimaryCalibration.lean, AFT/V7PrimaryCalibration.lean, AFT/BackgroundMeanBounds.lean, AFT/RootMarginal.lean, AFT/RootWindow.lean, AFT/GaussianReflection.lean, AFT/ClippedConvolution.lean, AFT/RootErrorParameters.lean, AFT/BodyBlur.lean, AFT/FiniteRetype.lean, AFT/FiniteExpectationAlgebra.lean, AFT/FiniteTicketSampler.lean, AFT/FiniteQuantization.lean, AFT/QuantizedSampling.lean, AFT/FairBitSampling.lean, AFT/RationalFiniteQuantization.lean, AFT/RationalPiProgram.lean, AFT/RationalExpProgram.lean, AFT/RationalGaussianProgram.lean, AFT/FiniteConvolutionProgram.lean, AFT/RootConvolutionProgram.lean, AFT/SignedConditioning.lean, AFT/RationalWindowGaussian.lean, AFT/RationalWindowTickets.lean, AFT/ActualAuxiliaryGaussianProgram.lean, AFT/BodyBlurParameters.lean, AFT/V7ActualMeans.lean, AFT/InverseMixedActivity.lean, AFT/V7PrimaryInverse.lean, AFT/AnchorMean.lean, AFT/V7SafeProjection.lean, AFT/AnchorSeed.lean, AFT/ActualBodyCenter.lean. Source bodies and declaration spans are recorded in native_sparse_prefix/manifest.json; SHA256 b780ca7b56cdaa3d058f736cff0c750f5c222937d0a969ff4ecab1caa688150f. Repackaging of identical data declarations, with 4163 public types matched to native source and 7722 origin declarations recursively audited for standard logical axioms only.

import Definitions.Def_InfoLossLAR_NativeSparsePrefix_01

section




/-!
# Actual trimmed pair slices and averaging over the public interval

The slice is the intersection of the two endpoint safety inequalities.
Its cardinality and its counting probability law are computed exactly.
-/

namespace AFT.TrimmedSlice

open scoped BigOperators symmDiff

/-- Both endpoint colors must avoid the boundary strip. -/
noncomputable def slice (modulus boundary shift : ℤ) : Finset ℤ :=
  Finset.Ico (boundary + max shift 0) (modulus - boundary + min shift 0)

theorem mem_slice (modulus boundary shift color : ℤ) :
    color ∈ slice modulus boundary shift ↔
      boundary ≤ color ∧ color ≤ modulus - 1 - boundary ∧
      boundary ≤ modulus - 1 + shift - color ∧
      modulus - 1 + shift - color ≤ modulus - 1 - boundary := by
  simp only [slice, Finset.mem_Ico]
  omega

/-- The exact cardinality printed in the chart construction. -/
theorem slice_card (modulus boundary shift : ℤ) :
    (slice modulus boundary shift).card = (modulus - 2 * boundary - |shift|).toNat := by
  rw [slice, Int.card_Ico]
  congr 1
  by_cases hs : 0 ≤ shift
  · rw [abs_of_nonneg hs]
    omega
  · rw [abs_of_neg (lt_of_not_ge hs)]
    omega

noncomputable def law (modulus boundary shift color : ℤ) : ℝ :=
  if color ∈ slice modulus boundary shift then ((slice modulus boundary shift).card : ℝ)⁻¹ else 0

theorem law_nonneg (modulus boundary shift color : ℤ) : 0 ≤ law modulus boundary shift color := by
  unfold law
  split_ifs <;> positivity





/-- Every actual trimmed law has the advertised supremum bound. -/
theorem law_le_of_shift_bound (modulus boundary shift shiftBound color : ℤ)
    (hshift : |shift| ≤ shiftBound) (hwidth : 2 * boundary + shiftBound < modulus) :
    law modulus boundary shift color ≤
      1 / ((modulus : ℝ) - 2 * boundary - shiftBound) := by
  have hcard : ((slice modulus boundary shift).card : ℤ) = modulus - 2 * boundary - |shift| := by
    rw [slice_card, Int.toNat_of_nonneg (by omega)]
  have hcardReal : ((slice modulus boundary shift).card : ℝ) =
      (modulus : ℝ) - 2 * boundary - |(shift : ℝ)| := by exact_mod_cast hcard
  have hshiftReal : |(shift : ℝ)| ≤ shiftBound := by exact_mod_cast hshift
  have hwidthReal : 0 < (modulus : ℝ) - 2 * boundary - shiftBound := by exact_mod_cast (show 0 < modulus - 2 * boundary - shiftBound by omega)
  unfold law
  split_ifs
  · rw [hcardReal, ← one_div]
    exact one_div_le_one_div_of_le hwidthReal (by linarith)
  · positivity

/-- Average the slice over the actual finite public uniform offset interval. -/
noncomputable def intervalMixture (start : ℤ) (width : ℕ) (kernel : ℤ → ℝ) : ℝ :=
  ∑ shift ∈ anchorInterval start width, intervalAnchorLaw start width shift * kernel shift









noncomputable def averagedLaw (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) : ℝ :=
  intervalMixture start width (fun shift => law modulus boundary (shift - source) color)

theorem averagedLaw_nonneg (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    0 ≤ averagedLaw modulus boundary start source width color := by
  unfold averagedLaw intervalMixture
  exact Finset.sum_nonneg fun shift _ => mul_nonneg (intervalAnchorLaw_nonneg _ _ _) (law_nonneg _ _ _ _)





/-- A finite source and public-blur mixture. A product index includes the
original source and independent public blur without altering either law. -/
noncomputable def mixedLaw {τ : Type*} [Fintype τ] (modulus boundary : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (color : ℤ) : ℝ :=
  ∑ index, weights index * averagedLaw modulus boundary (starts index) (sources index) width color

theorem mixedLaw_nonneg {τ : Type*} [Fintype τ] (modulus boundary : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (color : ℤ)
    (hweights : ∀ index, 0 ≤ weights index) :
    0 ≤ mixedLaw modulus boundary starts sources weights width color := by
  exact Finset.sum_nonneg fun index _ => mul_nonneg (hweights index) (averagedLaw_nonneg _ _ _ _ _ _)





end AFT.TrimmedSlice

end

section






/-!
# Pointwise positivity of the mean-calibrated primary law

The estimates retain the actual mean-calibration formula. The first result
isolates its deterministic arithmetic, including the nonnegative body
mean deficit; concrete averaged trimmed slices supply its hypotheses.
-/

namespace AFT

open scoped BigOperators







namespace TrimmedSlice

/-- The actual mean of a safe uniform center after a finite public body blur. -/
noncomputable def blurredSafeLaw {σ : Type*} [Fintype σ]
    (modulus margin : ℤ) (shifts : σ → ℤ) (weights : σ → ℝ) (color : ℤ) : ℝ :=
  ∑ index, weights index * intervalAnchorLaw margin (modulus - 2 * margin).toNat (color - shifts index)







end TrimmedSlice

end AFT

end

section



namespace AFT
end AFT
namespace AFT.finiteCorrection
end AFT.finiteCorrection



/-!
# Exact finite-group charge mixing

This proves a charge estimate directly by convolution of the signed difference
from uniform. It uses the actual `L¹` distance of the center law, rather than
postulating a Fourier mixing estimate. The bound has `q` instead of `q - 1`,
which suffices for the same eventual parameter regime once the concrete
center law's `L¹` estimate is established.
-/

namespace AFT

open scoped BigOperators
open scoped Classical

namespace FiniteDist

variable {G : Type*} [Fintype G] [AddCommGroup G]

























/-- A concrete uniform distribution on a nonempty safe subset. -/
noncomputable def uniformSafe (safe : Finset G) (hsafe : safe.Nonempty) : FiniteDist G where
  weight x := if x ∈ safe then (safe.card : ℝ)⁻¹ else 0
  nonneg x := by split_ifs <;> positivity
  sum_one := by
    have hc : (safe.card : ℝ) ≠ 0 := by exact_mod_cast hsafe.card_ne_zero
    simp [hc]













section Conditioning

variable {Ω : Type*} [Fintype Ω]











end Conditioning

end FiniteDist

end AFT

end

section






/-!
# Trimmed laws on the actual finite output palette
-/

namespace AFT.TrimmedSlice

open scoped BigOperators

/-- The actual slice, represented in the finite palette. -/
noncomputable def paletteSlice (modulus : ℕ) (boundary shift : ℤ) : Finset (Fin modulus) :=
  Finset.univ.filter fun color => (color.val : ℤ) ∈ slice modulus boundary shift

theorem paletteSlice_image (modulus : ℕ) (boundary shift : ℤ) (hboundary : 0 ≤ boundary) :
    (paletteSlice modulus boundary shift).image (fun color => (color.val : ℤ)) =
      slice modulus boundary shift := by
  ext color
  constructor
  · intro hc
    obtain ⟨point, hp, rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_filter.mp hp).2
  · intro hc
    have hb := (mem_slice modulus boundary shift color).mp hc
    have hcolor : 0 ≤ color ∧ color < modulus := by omega
    let point : Fin modulus := ⟨color.toNat, by omega⟩
    have heq : (point.val : ℤ) = color := by dsimp [point]; omega
    refine Finset.mem_image.mpr ⟨point, ?_, heq⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq ▸ hc⟩

theorem paletteSlice_card (modulus : ℕ) (boundary shift : ℤ) (hboundary : 0 ≤ boundary) :
    (paletteSlice modulus boundary shift).card = ((modulus : ℤ) - 2 * boundary - |shift|).toNat := by
  have hinj : Function.Injective (fun color : Fin modulus => (color.val : ℤ)) := by
    intro first second heq
    apply Fin.ext
    dsimp only at heq
    exact_mod_cast heq
  have hh : ((paletteSlice modulus boundary shift).image (fun color => (color.val : ℤ))).card =
      (paletteSlice modulus boundary shift).card :=
    Finset.card_image_iff.mpr (Set.injOn_of_injective hinj)
  rw [paletteSlice_image modulus boundary shift hboundary, slice_card] at hh
  exact hh.symm

theorem paletteSlice_nonempty (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) :
    (paletteSlice modulus boundary shift).Nonempty := by
  apply Finset.card_pos.mp
  rw [paletteSlice_card modulus boundary shift hboundary]
  omega

/-- The uniform slice is a real finite probability distribution. -/
noncomputable def finiteLaw (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) : FiniteDist (Fin modulus) :=
  FiniteDist.uniformSafe (paletteSlice modulus boundary shift)
    (paletteSlice_nonempty modulus boundary shift hboundary hwidth)

theorem finiteLaw_weight (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) (color : Fin modulus) :
    (finiteLaw modulus boundary shift hboundary hwidth).weight color =
      law modulus boundary shift color.val := by
  simp only [finiteLaw, FiniteDist.uniformSafe, paletteSlice, Finset.mem_filter,
    Finset.mem_univ, true_and, law]
  rw [show (Finset.univ.filter fun color : Fin modulus => (color.val : ℤ) ∈ slice modulus boundary shift).card =
      (slice modulus boundary shift).card by
    rw [← paletteSlice, paletteSlice_card modulus boundary shift hboundary, slice_card]]

theorem law_palette_mass (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) :
    ∑ color : Fin modulus, law modulus boundary shift color.val = 1 := by
  simp_rw [← finiteLaw_weight modulus boundary shift hboundary hwidth]
  exact (finiteLaw modulus boundary shift hboundary hwidth).sum_one

/-- The finite uniform-on-subset L1 identity does not require a group structure. -/
theorem uniformSubset_l1 {ι : Type*} [Fintype ι] (subset : Finset ι) (hsubset : subset.Nonempty) :
    (∑ color, |(FiniteDist.uniformSafe subset hsubset).weight color - (Fintype.card ι : ℝ)⁻¹|) =
      2 * (1 - (subset.card : ℝ) / Fintype.card ι) := by
  classical
  have hs : (0 : ℝ) < subset.card := by exact_mod_cast hsubset.card_pos
  have hle : (subset.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast Finset.card_le_univ subset
  have hcard : (0 : ℝ) < Fintype.card ι := hs.trans_le hle
  have hi : (Fintype.card ι : ℝ)⁻¹ ≤ (subset.card : ℝ)⁻¹ := inv_anti₀ hs hle
  have hpoint (color : ι) :
      |(FiniteDist.uniformSafe subset hsubset).weight color - (Fintype.card ι : ℝ)⁻¹| =
        if color ∈ subset then (subset.card : ℝ)⁻¹ - (Fintype.card ι : ℝ)⁻¹
          else (Fintype.card ι : ℝ)⁻¹ := by
    by_cases hc : color ∈ subset
    · simp only [FiniteDist.uniformSafe, if_pos hc, abs_of_nonneg (sub_nonneg.mpr hi)]
    · simp [FiniteDist.uniformSafe, hc, abs_of_nonneg (inv_nonneg.mpr hcard.le)]
  simp_rw [hpoint]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hcompl : (Finset.univ.filter fun color : ι => color ∉ subset).card = Fintype.card ι - subset.card := by
    simp [← Finset.sdiff_eq_filter, Finset.card_sdiff]
  rw [hcompl, Nat.cast_sub (Finset.card_le_univ subset)]
  field_simp
  ring

/-- Exact L1 deviation of the real trimmed slice from palette uniformity. -/
theorem law_palette_l1 (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) :
    (∑ color : Fin modulus, |law modulus boundary shift color.val - (modulus : ℝ)⁻¹|) =
      2 * (2 * (boundary : ℝ) + |(shift : ℝ)|) / modulus := by
  have hcard : ((paletteSlice modulus boundary shift).card : ℤ) =
      (modulus : ℤ) - 2 * boundary - |shift| := by
    rw [paletteSlice_card modulus boundary shift hboundary, Int.toNat_of_nonneg (by omega)]
  have hcardReal : ((paletteSlice modulus boundary shift).card : ℝ) =
      (modulus : ℝ) - 2 * boundary - |(shift : ℝ)| := by exact_mod_cast hcard
  have hmodulus : (modulus : ℝ) ≠ 0 := by
    have hnonneg := abs_nonneg shift
    have hh : 0 < modulus := by omega
    exact_mod_cast (ne_of_gt hh)
  simp_rw [← finiteLaw_weight modulus boundary shift hboundary hwidth]
  change (∑ color : Fin modulus, |(FiniteDist.uniformSafe _ _).weight color - _|) = _
  rw [show (modulus : ℝ)⁻¹ = (Fintype.card (Fin modulus) : ℝ)⁻¹ by simp,
    uniformSubset_l1, Fintype.card_fin, hcardReal]
  field_simp
  ring

/-- Actual source displacement and trimming yield a uniform finite-palette
L1 bound for each public interval mixture. -/
theorem averagedLaw_palette_l1_le (modulus : ℕ) (boundary start source shiftBound cutoff : ℤ)
    (width : ℕ) (hwidth : width ≠ 0) (hboundary : 0 ≤ boundary)
    (hbound : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hsource : |source| ≤ cutoff) (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    (∑ color : Fin modulus, |averagedLaw modulus boundary start source width color.val - (modulus : ℝ)⁻¹|) ≤
      2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus := by
  have hshift (shift : ℤ) (hs : shift ∈ anchorInterval start width) :
      |shift - source| ≤ shiftBound + cutoff := (abs_sub _ _).trans (add_le_add (hbound shift hs) hsource)
  have hmass := intervalAnchorLaw_mass start width hwidth
  have hrepr (color : Fin modulus) : averagedLaw modulus boundary start source width color.val - (modulus : ℝ)⁻¹ =
      ∑ shift ∈ anchorInterval start width,
        intervalAnchorLaw start width shift * (law modulus boundary (shift - source) color.val - (modulus : ℝ)⁻¹) := by
    simp only [averagedLaw, intervalMixture, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
  calc
    _ ≤ ∑ color : Fin modulus, ∑ shift ∈ anchorInterval start width,
        intervalAnchorLaw start width shift * |law modulus boundary (shift - source) color.val - (modulus : ℝ)⁻¹| := by
      apply Finset.sum_le_sum
      intro color _
      rw [hrepr]
      simpa only [abs_mul, abs_of_nonneg (intervalAnchorLaw_nonneg _ _ _)] using Finset.abs_sum_le_sum_abs
        (fun shift => intervalAnchorLaw start width shift * (law modulus boundary (shift - source) color.val - (modulus : ℝ)⁻¹))
        (anchorInterval start width)
    _ = ∑ shift ∈ anchorInterval start width, intervalAnchorLaw start width shift *
        ∑ color : Fin modulus, |law modulus boundary (shift - source) color.val - (modulus : ℝ)⁻¹| := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ shift ∈ anchorInterval start width, intervalAnchorLaw start width shift *
        (2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus) := by
      apply Finset.sum_le_sum
      intro shift hs
      apply mul_le_mul_of_nonneg_left _ (intervalAnchorLaw_nonneg _ _ _)
      rw [law_palette_l1 modulus boundary (shift - source) hboundary (by have := hshift shift hs; omega)]
      have hh : |((shift - source : ℤ) : ℝ)| ≤ (shiftBound : ℝ) + cutoff := by exact_mod_cast hshift shift hs
      exact div_le_div_of_nonneg_right (by push_cast at hh ⊢; linarith) (Nat.cast_nonneg modulus)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

theorem averagedLaw_palette_mass (modulus : ℕ) (boundary start source shiftBound cutoff : ℤ)
    (width : ℕ) (hwidth : width ≠ 0) (hboundary : 0 ≤ boundary)
    (hbound : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hsource : |source| ≤ cutoff) (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    ∑ color : Fin modulus, averagedLaw modulus boundary start source width color.val = 1 := by
  unfold averagedLaw intervalMixture
  rw [Finset.sum_comm]
  have heq (shift : ℤ) (hs : shift ∈ anchorInterval start width) :
      (∑ color : Fin modulus, intervalAnchorLaw start width shift * law modulus boundary (shift - source) color.val) =
        intervalAnchorLaw start width shift := by
    rw [← Finset.mul_sum, law_palette_mass modulus boundary (shift - source) hboundary, mul_one]
    have hh := (abs_sub shift source).trans (add_le_add (hbound shift hs) hsource)
    omega
  simpa only [Finset.sum_congr rfl heq] using intervalAnchorLaw_mass start width hwidth

theorem mixedLaw_palette_mass {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (hmass : ∑ index, weights index = 1)
    (hboundary : 0 ≤ boundary)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    ∑ color : Fin modulus, mixedLaw modulus boundary starts sources weights width color.val = 1 := by
  unfold mixedLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, averagedLaw_palette_mass modulus boundary _ _ shiftBound cutoff width hwidth
    hboundary (hbound _) (hsources _) hclearance, mul_one]
  exact hmass

theorem mixedLaw_palette_l1_le {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (weights : τ → ℝ)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hboundary : 0 ≤ boundary)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    (∑ color : Fin modulus, |mixedLaw modulus boundary starts sources weights width color.val - (modulus : ℝ)⁻¹|) ≤
      2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus := by
  have hrepr (color : Fin modulus) : mixedLaw modulus boundary starts sources weights width color.val - (modulus : ℝ)⁻¹ =
      ∑ index, weights index * (averagedLaw modulus boundary (starts index) (sources index) width color.val - (modulus : ℝ)⁻¹) := by
    simp only [mixedLaw, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
  calc
    _ ≤ ∑ color : Fin modulus, ∑ index, weights index *
        |averagedLaw modulus boundary (starts index) (sources index) width color.val - (modulus : ℝ)⁻¹| := by
      apply Finset.sum_le_sum
      intro color _
      rw [hrepr]
      simpa only [abs_mul, abs_of_nonneg (hweights _)] using Finset.abs_sum_le_sum_abs
        (fun index => weights index * (averagedLaw modulus boundary (starts index) (sources index) width color.val - (modulus : ℝ)⁻¹))
        Finset.univ
    _ = ∑ index, weights index * ∑ color : Fin modulus,
        |averagedLaw modulus boundary (starts index) (sources index) width color.val - (modulus : ℝ)⁻¹| := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ index, weights index * (2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus) :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left
        (averagedLaw_palette_l1_le modulus boundary (starts index) (sources index) shiftBound cutoff width hwidth
          hboundary (hbound index) (hsources index) hclearance) (hweights index)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]



/-- The source-averaged mixture retains the trimmed-slice supremum bound. -/
theorem mixedLaw_le {τ : Type*} [Fintype τ] (modulus boundary shiftBound cutoff : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (hwidth : width ≠ 0)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) (color : ℤ) :
    mixedLaw modulus boundary starts sources weights width color ≤
      1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) := by
  have hlocal (index : τ) : averagedLaw modulus boundary (starts index) (sources index) width color ≤
      1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) := by
    unfold averagedLaw intervalMixture
    calc
      _ ≤ ∑ shift ∈ anchorInterval (starts index) width, intervalAnchorLaw (starts index) width shift *
          (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) := by
        apply Finset.sum_le_sum
        intro shift hs
        apply mul_le_mul_of_nonneg_left _ (intervalAnchorLaw_nonneg _ _ _)
        have hh := law_le_of_shift_bound modulus boundary (shift - sources index) (shiftBound + cutoff) color
          ((abs_sub _ _).trans (add_le_add (hbound index shift hs) (hsources index))) (by omega)
        simpa only [Int.cast_add, sub_add_eq_sub_sub] using hh
      _ = _ := by rw [← Finset.sum_mul, intervalAnchorLaw_mass _ _ hwidth, one_mul]
  calc
    _ ≤ ∑ index, weights index * (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (hlocal index) (hweights index)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

end AFT.TrimmedSlice

end

section






/-!
# The signed diffuse response is controlled by the actual calibration
-/

namespace AFT

open scoped BigOperators









namespace TrimmedSlice

/-- Equal mixture of the two public shift-sign branches. -/
noncomputable def fairMixedLaw {τ : Type*} [Fintype τ] (modulus boundary : ℤ)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (color : ℤ) : ℝ :=
  (mixedLaw modulus boundary startsPlus sources weights width color +
    mixedLaw modulus boundary startsMinus sources weights width color) / 2



noncomputable def actualFairBasePrimary {σ τ : Type*} [Fintype σ] [Fintype τ]
    (modulus margin boundary : ℤ) (width : ℕ) (bodies legs activation : ℝ)
    (bodyShifts : σ → ℤ) (bodyWeights : σ → ℝ)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ) : ℤ → ℝ :=
  basePrimaryProfile (bodies + 2 * legs) bodies legs activation
    (fun _ => 1 / (modulus : ℝ)) (blurredSafeLaw modulus margin bodyShifts bodyWeights)
    (fairMixedLaw modulus boundary startsPlus startsMinus sources weights width)
    (fairMixedLaw modulus boundary startsPlus startsMinus (fun _ => 0) weights width)











end TrimmedSlice

end AFT

end

section








namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.activation
end AFT.GaussianSource.activation
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.legs
end AFT.Parameters.legs
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.primaryCalibrationEnvelope
end AFT.primaryCalibrationEnvelope
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope



/-!
# Actual V7 calibrated sign estimates with all asymptotic losses discharged
-/

namespace AFT

open Filter
open scoped BigOperators Topology



namespace V7Calibration

noncomputable def basePrimary {σ τ : Type*} [Fintype σ] [Fintype τ]
    (parameter : ℕ) (cutoffScale : ℝ) (boundary : ℤ)
    (bodyShifts : σ → ℤ) (bodyLaw : FiniteDist σ)
    (startsPlus startsMinus sources : τ → ℤ) (sourceLaw : FiniteDist τ) :
    Fin (Parameters.modulus parameter) → ℝ := fun color =>
  TrimmedSlice.actualFairBasePrimary (Parameters.modulus parameter) (Parameters.safeMargin parameter)
    boundary (Parameters.anchorWidth parameter) (Parameters.bodies parameter) (Parameters.legs parameter)
    (GaussianSource.v7Activation cutoffScale parameter) bodyShifts bodyLaw.weight
    startsPlus startsMinus sources sourceLaw.weight color.val







end V7Calibration
end AFT

end

section









namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.activation
end AFT.GaussianSource.activation
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.legs
end AFT.Parameters.legs
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.primaryCalibrationEnvelope
end AFT.primaryCalibrationEnvelope
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope




/-!
# The beta boundary-mass repair preserves the actual primary lower bound
-/

namespace AFT

open Filter
open scoped BigOperators Topology

noncomputable def uniformFiniteProfile {ι : Type*} [DecidableEq ι] (support : Finset ι) (color : ι) : ℝ :=
  if color ∈ support then (support.card : ℝ)⁻¹ else 0





/-- The real V7 boundary palette is the complement of the zero-shift trimmed interval. -/
noncomputable def boundaryPalette (modulus : ℕ) (halfWidth : ℤ) : Finset (Fin modulus) :=
  (TrimmedSlice.paletteSlice modulus halfWidth 0)ᶜ



theorem boundaryPalette_card (modulus : ℕ) (halfWidth : ℤ)
    (hh : 0 ≤ halfWidth) (hsmall : 2 * halfWidth ≤ modulus) :
    ((boundaryPalette modulus halfWidth).card : ℤ) = 2 * halfWidth := by
  rw [boundaryPalette, Finset.card_compl, Fintype.card_fin,
    TrimmedSlice.paletteSlice_card modulus halfWidth 0 hh]
  simp only [abs_zero, Int.sub_zero]
  omega



noncomputable def v7BaseBoundaryMass (cutoffScale : ℝ) (parameter : ℕ) (boundaryHalfWidth : ℤ) : ℝ :=
  (Parameters.dimension parameter : ℝ) * (boundaryPalette (Parameters.modulus parameter) boundaryHalfWidth).card /
    ((Parameters.modulus parameter : ℝ) * Parameters.legs parameter * GaussianSource.v7Activation cutoffScale parameter)





namespace TrimmedSlice









end TrimmedSlice

end AFT

end

section





/-!
# The actual beta-calibrated V7 primary probability and sign response
-/

namespace AFT

open Filter
open scoped BigOperators Topology

theorem uniformFiniteProfile_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (support : Finset ι) (hne : support.Nonempty) :
    ∑ color, uniformFiniteProfile support color = 1 := by
  have hh : (support.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hne.card_pos
  simp [uniformFiniteProfile, hh]

namespace V7Calibration

noncomputable def repairedBoundaryMass (parameter : ℕ) (cutoffScale beta : ℝ) (boundary : ℤ) : ℝ :=
  ((boundaryPalette (Parameters.modulus parameter) boundary).card / (Parameters.modulus parameter : ℝ)) /
    (GaussianSource.v7Activation cutoffScale parameter * beta)

noncomputable def primary {σ τ : Type*} [Fintype σ] [Fintype τ]
    (parameter : ℕ) (cutoffScale beta : ℝ) (boundary : ℤ)
    (bodyShifts : σ → ℤ) (bodyLaw : FiniteDist σ)
    (startsPlus startsMinus sources : τ → ℤ) (sourceLaw : FiniteDist τ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  calibratedPrimaryProfile (basePrimary parameter cutoffScale boundary bodyShifts bodyLaw
    startsPlus startsMinus sources sourceLaw)
    (uniformFiniteProfile (boundaryPalette (Parameters.modulus parameter) boundary))
    (uniformFiniteProfile (boundaryPalette (Parameters.modulus parameter) boundary)ᶜ)
    (repairedBoundaryMass parameter cutoffScale beta boundary - v7BaseBoundaryMass cutoffScale parameter boundary)



end V7Calibration
end AFT

end

section






namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.referenceMean
end AFT.V7Calibration.referenceMean


/-! # Explicit body/reference norm bounds for the actual calibrated model -/

namespace AFT.V7Calibration

open Filter
open scoped BigOperators Classical Topology

noncomputable section



def bodyCompensation (parameter : ℕ) (cutoffScale : ℝ) : ℝ :=
  (Parameters.legs parameter : ℝ) * GaussianSource.v7Activation cutoffScale parameter / Parameters.bodies parameter



end

end AFT.V7Calibration

end

section





/-!
# Exact multi-coordinate marginals of the integer root slice

The selected coordinates are a literal prefix of the full independent
product, and the law is conditioned on the full integer sum. The numerator
below is derived by the append equivalence of those actual finite spaces.
-/

namespace AFT.RootSlice

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.RootSlice.instDecidableEqFin_aFT (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {α : Type*} [Fintype α]

def sumProbability (source : FiniteDist α) (score : α → ℤ) (count : ℕ) (target : ℤ) : ℝ :=
  probability (fun _ : Fin count => source) score target

def prefixLaw (source : FiniteDist α) (score : α → ℤ) (selected remaining : ℕ)
    (h : 0 < sumProbability source score (selected + remaining) 0) :
    FiniteDist (Fin selected → α) :=
  (law (fun _ : Fin (selected + remaining) => source) score 0 h).map
    (fun x i => x (Fin.castAdd remaining i))





/-- The actual first-coordinate law of a population root slice. -/
def marginalLaw (source : FiniteDist α) (score : α → ℤ) (population : ℕ)
    (hn : 0 < population) (h : 0 < sumProbability source score population 0) : FiniteDist α :=
  (prefixLaw source score 1 (population - 1)
    (by have heq : 1 + (population - 1) = population := by omega
        simpa only [heq] using h)).map (Equiv.funUnique (Fin 1) α)






end

end AFT.RootSlice

end

section





namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource



/-!
# Positive marginals and moments on the actual protected root alphabet
-/

set_option backward.isDefEq.respectTransparency false

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.GaussianSource.instDecidableEqFin_aFT (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def windowNegate (cutoff : ℕ) (a : Window cutoff) : Window cutoff :=
  ⟨-(a : ℤ), by
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp a.property
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩



def rootMarginal (width : ℝ) (cutoff population : ℕ) (hn : 0 < population) :
    FiniteDist (Window cutoff) :=
  RootSlice.marginalLaw (windowGaussian width cutoff) (fun z => (z : ℤ)) population hn
    (window_root_probability_positive width cutoff population)









end

end AFT.GaussianSource

end

section





/-!
# Exact sign reversal of the clipped Gaussian and the conditioned root marginal
-/

set_option backward.isDefEq.respectTransparency false

namespace AFT

open scoped BigOperators

namespace RootSlice

noncomputable section

local instance _root_.AFT.RootSlice.instDecidableEqFin_aFT_1 (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _



end

end RootSlice

namespace GaussianSource

noncomputable def windowNegateEquiv (cutoff : ℕ) : Window cutoff ≃ Window cutoff where
  toFun := windowNegate cutoff
  invFun := windowNegate cutoff
  left_inv value := by apply Subtype.ext; simp [windowNegate]
  right_inv value := by apply Subtype.ext; simp [windowNegate]

@[simp] theorem windowNegateEquiv_val (cutoff : ℕ) (value : Window cutoff) :
    ((windowNegateEquiv cutoff value : Window cutoff) : ℤ) = -(value : ℤ) := rfl

theorem windowGaussian_reflection (width : ℝ) (cutoff : ℕ) (value : Window cutoff) :
    (windowGaussian width cutoff).weight (windowNegateEquiv cutoff value) =
      (windowGaussian width cutoff).weight value := by
  simp only [windowGaussian, FiniteDist.normalize, windowNegateEquiv_val, weight, Int.cast_neg, neg_sq]



end GaussianSource
end AFT

end

section





namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier



/-!
# Finite clipped Gaussian sum probabilities

This file relates the actual finite root sum to integer convolutions, with
an explicit clipping defect and the uniform theta error from Poisson summation.
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical



















noncomputable def integerMass (width : ℝ) (z : ℤ) : ℝ := weight width z / realNormalizer width



theorem integerMass_nonneg (width : ℝ) (hw : 0 < width) (z : ℤ) : 0 ≤ integerMass width z :=
  div_nonneg (weight_pos width z).le (le_trans zero_le_one (realNormalizer_ge_one width hw))

theorem summable_integerMass (width : ℝ) (hw : 0 < width) : Summable (integerMass width) :=
  (summable_weight width hw).div_const _

theorem integerMass_sum (width : ℝ) (hw : 0 < width) : (∑' z : ℤ, integerMass width z) = 1 := by
  unfold integerMass
  rw [tsum_div_const]
  exact div_self (lt_of_lt_of_le zero_lt_one (realNormalizer_ge_one width hw)).ne'







noncomputable def restrictWindow (mass : ℤ → ℝ) (cutoff : ℕ) (z : ℤ) : ℝ :=
  if z ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) then mass z else 0







noncomputable def retainedFraction (width : ℝ) (cutoff : ℕ) : ℝ :=
  windowNormalizer width cutoff / realNormalizer width













































end AFT.GaussianSource

end

section








namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent



/-!
# Explicit polynomial-exponential bounds for the root convolution error
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical









noncomputable def v7RootWidth (parameter : ℕ) : ℝ := Real.sqrt 8 * parameter












open Filter
open scoped Topology





noncomputable def v7RootCutoff (parameter : ℕ) : ℕ := 3 * parameter ^ 2 - 1











end AFT.GaussianSource

end

section






namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration




/-!
# The actual body blur of referenceV7

The finite sample includes the true root marginal and independent marginal
attachment/queue indicators. It asserts no independence among different
physical body coordinates.
-/

set_option backward.isDefEq.respectTransparency false

namespace AFT

open scoped BigOperators Classical

noncomputable section

namespace FiniteDist

variable {α : Type*} [Fintype α]

def optional (source : FiniteDist α) (rate : ℝ) (h0 : 0 ≤ rate) (h1 : rate ≤ 1) : FiniteDist (Option α) where
  weight value := match value with | none => 1 - rate | some a => rate * source.weight a
  nonneg value := by cases value with
    | none => exact sub_nonneg.mpr h1
    | some a => exact mul_nonneg h0 (source.nonneg a)
  sum_one := by
    rw [Fintype.sum_option]
    simp only [← Finset.mul_sum, source.sum_one, mul_one]
    ring

@[simp] theorem optional_none (source : FiniteDist α) (rate : ℝ) (h0 h1) :
    (optional source rate h0 h1).weight none = 1 - rate := rfl

@[simp] theorem optional_some (source : FiniteDist α) (rate : ℝ) (h0 h1) (a : α) :
    (optional source rate h0 h1).weight (some a) = rate * source.weight a := rfl



end FiniteDist

namespace GaussianSource

def queueCutoff (parameter : ℕ) : ℕ := parameter ^ 2 - 1

def legRate (parameter : ℕ) : ℝ := (Parameters.legs parameter : ℝ) / Parameters.bodies parameter

def queueRate (parameter : ℕ) : ℝ := (Parameters.modulus parameter : ℝ) / Parameters.bodies parameter

theorem body_rates_le_quarter (parameter : ℕ) : legRate parameter ≤ 1 / 4 ∧ queueRate parameter ≤ 1 / 4 := by
  have hx := Parameters.security_ge_two parameter
  have hm8 : 8 ≤ Parameters.legs parameter := by
    have hh := Nat.pow_le_pow_left hx 30
    change 8 ≤ Parameters.security parameter ^ 30
    omega
  have hdim8m : 8 * Parameters.legs parameter ≤ Parameters.dimension parameter := by
    have hh := (Parameters.dimension_bounds parameter).1
    have heq : Parameters.security parameter ^ 60 = Parameters.legs parameter * Parameters.legs parameter := by
      unfold Parameters.legs
      rw [← pow_add]
    rw [heq] at hh
    exact (Nat.mul_le_mul_right _ hm8).trans hh
  have hx20 : 8 ≤ Parameters.security parameter ^ 20 := by
    have hh := Nat.pow_le_pow_left hx 20
    omega
  have hdim8q : 8 * Parameters.modulus parameter ≤ Parameters.dimension parameter := by
    have hh := Nat.mul_le_mul_left (Parameters.modulus parameter) hx20
    simpa only [Parameters.dimension, Parameters.meanDensity, Nat.mul_comm] using hh
  have hpop := Parameters.population_identity parameter
  have hm4 : 4 * Parameters.legs parameter ≤ Parameters.bodies parameter := by omega
  have hq4 : 4 * Parameters.modulus parameter ≤ Parameters.bodies parameter := by omega
  have hN : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  constructor
  · unfold legRate
    apply (div_le_iff₀ hN).mpr
    have hh : 4 * (Parameters.legs parameter : ℝ) ≤ Parameters.bodies parameter := by exact_mod_cast hm4
    linarith
  · unfold queueRate
    apply (div_le_iff₀ hN).mpr
    have hh : 4 * (Parameters.modulus parameter : ℝ) ≤ Parameters.bodies parameter := by exact_mod_cast hq4
    linarith

def optionalShift {cutoff : ℕ} : Option (Window cutoff) → ℤ
  | none => 0
  | some z => z

def extraSample (cutoffScale : ℝ) (parameter : ℕ) :=
  Option (Window (legCutoff cutoffScale parameter - 1)) × Option (Window (queueCutoff parameter))

instance extraSampleFintype (cutoffScale : ℝ) (parameter : ℕ) : Fintype (extraSample cutoffScale parameter) :=
  inferInstanceAs (Fintype (_ × _))

def extraShift (cutoffScale : ℝ) (parameter : ℕ) (sample : extraSample cutoffScale parameter) : ℤ :=
  optionalShift sample.1 + optionalShift sample.2

def extraBlur (cutoffScale : ℝ) (parameter : ℕ) : FiniteDist (extraSample cutoffScale parameter) :=
  (FiniteDist.optional (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1))
    (legRate parameter) (by unfold legRate; positivity) ((body_rates_le_quarter parameter).1.trans (by norm_num))).prod
  (FiniteDist.optional (windowGaussian parameter (queueCutoff parameter))
    (queueRate parameter) (by unfold queueRate; positivity) ((body_rates_le_quarter parameter).2.trans (by norm_num)))

def bodySample (cutoffScale : ℝ) (parameter : ℕ) :=
  Window (v7RootCutoff parameter) × extraSample cutoffScale parameter

instance bodySampleFintype (cutoffScale : ℝ) (parameter : ℕ) : Fintype (bodySample cutoffScale parameter) :=
  inferInstanceAs (Fintype (_ × _))

def bodyShift (cutoffScale : ℝ) (parameter : ℕ) (sample : bodySample cutoffScale parameter) : ℤ :=
  (sample.1 : ℤ) + extraShift cutoffScale parameter sample.2

def bodyBlur (cutoffScale : ℝ) (parameter : ℕ) : FiniteDist (bodySample cutoffScale parameter) :=
  (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
    (Parameters.bodies_positive parameter)).prod (extraBlur cutoffScale parameter)
























def maxBodyShift (cutoffScale : ℝ) (parameter : ℕ) : ℕ :=
  v7RootCutoff parameter + (legCutoff cutoffScale parameter - 1) + queueCutoff parameter







end GaussianSource

end

end AFT

end

section




/-! # Transport a finite probability law across the unique Fintype instance -/

namespace AFT.FiniteDist

open scoped BigOperators

/-- Only the finite enumeration instance changes. All point weights are
literally preserved, and total mass follows by uniqueness of `Fintype`. -/
def retype {α : Type*} {source : Fintype α} [target : Fintype α]
    (law : @FiniteDist α source) : FiniteDist α where
  weight := @FiniteDist.weight α source law
  nonneg := @FiniteDist.nonneg α source law
  sum_one := by
    have h : source = target := Subsingleton.elim _ _
    cases h
    exact law.sum_one

@[simp] theorem retype_weight {α : Type*} {source : Fintype α} [target : Fintype α]
    (law : @FiniteDist α source) (point : α) : (retype law).weight point = @FiniteDist.weight α source law point := rfl

end AFT.FiniteDist

end

section







/-! # Exact finite scalar expectation identities -/

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

omit [Fintype β] [Fintype ι] in
theorem expectation_const (law : FiniteDist α) (value : ℝ) :
    law.expectation (fun _ => value) = value := by
  simp only [expectation, ← Finset.sum_mul, law.sum_one, one_mul]

omit [Fintype β] [Fintype ι] in
theorem expectation_add (law : FiniteDist α) (f g : α → ℝ) :
    law.expectation (fun x => f x + g x) = law.expectation f + law.expectation g := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

omit [Fintype β] [Fintype ι] in
theorem expectation_sub (law : FiniteDist α) (f g : α → ℝ) :
    law.expectation (fun x => f x - g x) = law.expectation f - law.expectation g := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib]

omit [Fintype β] [Fintype ι] in
theorem expectation_const_mul (law : FiniteDist α) (scalar : ℝ) (f : α → ℝ) :
    law.expectation (fun x => scalar * f x) = scalar * law.expectation f := by
  simp only [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype β] [Fintype ι] in
theorem expectation_mul_const (law : FiniteDist α) (f : α → ℝ) (scalar : ℝ) :
    law.expectation (fun x => f x * scalar) = law.expectation f * scalar := by
  simp only [expectation, ← mul_assoc, Finset.sum_mul]



omit [Fintype ι] in
theorem expectation_comm (first : FiniteDist α) (second : FiniteDist β) (f : α → β → ℝ) :
    first.expectation (fun x => second.expectation (f x)) =
      second.expectation (fun y => first.expectation (fun x => f x y)) := by
  simp only [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype ι] in
theorem expectation_prod (first : FiniteDist α) (second : FiniteDist β) (f : α × β → ℝ) :
    (first.prod second).expectation f =
      first.expectation (fun x => second.expectation (fun y => f (x,y))) := by
  simp only [expectation, prod_weight, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]





end
end AFT.FiniteDist

end

section





/-! # Executable finite-table sampling from a uniformly selected ticket

The selection function uses comparisons and subtraction only. The theorem
below identifies its complete output law for every integer count table.
-/

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

/-- Index of the bucket containing a ticket, in the specified table order. -/
def bucket : List ℕ → ℕ → ℕ
  | [], _ => 0
  | count :: rest, ticket => if ticket < count then 0 else 1 + bucket rest (ticket - count)

theorem bucket_lt_length (counts : List ℕ) (ticket : ℕ) (h : ticket < counts.sum) :
    bucket counts ticket < counts.length := by
  induction counts generalizing ticket with
  | nil => simp at h
  | cons count rest ih =>
    simp only [List.sum_cons] at h
    simp only [bucket, List.length_cons]
    split_ifs with hfirst
    · omega
    · have hh := ih (ticket - count) (by omega)
      omega







end AFT.FiniteTicketSampler

end

section







/-! # Support-preserving finite count tables and their approximation error

The rounding specification uses real weights. The resulting count table is
sampled by `FiniteTicketSampler.draw`; computability of the original real
weights is a separate obligation, not hidden in this statement.
-/

namespace AFT.FiniteQuantization

open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

def floorCount (law : FiniteDist Color) (tickets : ℕ) (color : Color) : ℕ :=
  ⌊(tickets : ℝ) * law.weight color⌋₊

def floorTotal (law : FiniteDist Color) (tickets : ℕ) : ℕ := ∑ color, floorCount law tickets color

theorem floorTotal_le (law : FiniteDist Color) (tickets : ℕ) : floorTotal law tickets ≤ tickets := by
  have hh := Finset.sum_le_sum fun color (_ : color ∈ Finset.univ) =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg tickets) (law.nonneg color))
  rw [← Finset.mul_sum, law.sum_one, mul_one] at hh
  exact_mod_cast hh

def deficit (law : FiniteDist Color) (tickets : ℕ) : ℕ := tickets - floorTotal law tickets



def count (law : FiniteDist Color) (tickets : ℕ) (fallback color : Color) : ℕ :=
  floorCount law tickets color + if color = fallback then deficit law tickets else 0

theorem count_sum (law : FiniteDist Color) (tickets : ℕ) (fallback : Color) :
    (∑ color, count law tickets fallback color) = tickets := by
  have ht := floorTotal_le law tickets
  simp only [count, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change floorTotal law tickets + (tickets - floorTotal law tickets) = tickets
  omega

def roundedLaw (law : FiniteDist Color) (tickets : ℕ) (ht : 0 < tickets) (fallback : Color) : FiniteDist Color where
  weight color := (count law tickets fallback color : ℝ) / tickets
  nonneg _ := by positivity
  sum_one := by
    rw [← Finset.sum_div, ← Nat.cast_sum, count_sum]
    exact div_self (by exact_mod_cast ht.ne')











end
end AFT.FiniteQuantization

end

section





/-! # Exact ticket implementation of the support-preserving rounded law -/

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

def drawFin {n : ℕ} (counts : Fin n → ℕ) (ticket : Fin (∑ index, counts index)) : Fin n :=
  ⟨bucket (List.ofFn counts) ticket.val, by
    have hh := bucket_lt_length (List.ofFn counts) ticket.val
      (by simpa only [List.sum_ofFn] using ticket.isLt)
    simpa only [List.length_ofFn] using hh⟩



end FiniteTicketSampler

namespace FiniteQuantization

open scoped BigOperators Classical
noncomputable section







end
end FiniteQuantization
end AFT

end

section





/-! # A fixed number of independent fair bits implements a dyadic table -/

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

/-- Little-endian binary evaluation; the underlying equivalence is explicit. -/
def bitTicket (bits : ℕ) : (Fin bits → Fin 2) → Fin (2 ^ bits) := finFunctionFinEquiv

theorem bitTicket_value (bits : ℕ) (word : Fin bits → Fin 2) :
    (bitTicket bits word).val = ∑ index, (word index).val * 2 ^ index.val :=
  finFunctionFinEquiv_apply word





/-- Sampling from a precomputed integer table needs exactly `bits` input
bits. Selection uses only the executable integer ticket and bucket routines. -/
def drawBitTable {n : ℕ} (bits : ℕ) (counts : Fin n → ℕ) (htotal : ∑ index, counts index = 2 ^ bits)
    (word : Fin bits → Fin 2) : Fin n :=
  drawFin counts (Fin.cast htotal.symm (bitTicket bits word))



end FiniteTicketSampler
end AFT

end

section









/-! # Executable dyadic sampling of finite rational distributions

The executable count table rounds rational numbers, and assigns the remaining
tickets to index zero. Its probability law is compared with the corresponding
real distribution only in the proofs below.
-/

namespace AFT.RationalFiniteQuantization

open scoped BigOperators

variable {size : ℕ}

def floorCount (weight : Fin (size + 1) → ℚ) (tickets : ℕ)
    (index : Fin (size + 1)) : ℕ :=
  ⌊(tickets : ℚ) * weight index⌋₊

def floorTotal (weight : Fin (size + 1) → ℚ) (tickets : ℕ) : ℕ :=
  ∑ index, floorCount weight tickets index

def deficit (weight : Fin (size + 1) → ℚ) (tickets : ℕ) : ℕ :=
  tickets - floorTotal weight tickets

def counts (weight : Fin (size + 1) → ℚ) (tickets : ℕ)
    (index : Fin (size + 1)) : ℕ :=
  floorCount weight tickets index + if index = 0 then deficit weight tickets else 0

theorem floorTotal_le (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) : floorTotal weight tickets ≤ tickets := by
  have hh := Finset.sum_le_sum fun index (_ : index ∈ Finset.univ) =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg tickets) (hnonneg index))
  rw [← Finset.mul_sum, hsum, mul_one] at hh
  exact_mod_cast hh

theorem counts_total (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) : ∑ index, counts weight tickets index = tickets := by
  have ht := floorTotal_le weight hnonneg hsum tickets
  simp only [counts, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change floorTotal weight tickets + (tickets - floorTotal weight tickets) = tickets
  omega

/-- Exactly `bits` input bits select a ticket in the rationally computed table. -/
def draw (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (bits : ℕ) (word : Fin bits → Fin 2) : Fin (size + 1) :=
  FiniteTicketSampler.drawBitTable bits (counts weight (2 ^ bits))
    (counts_total weight hnonneg hsum (2 ^ bits)) word

noncomputable section

def law (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1) :
    FiniteDist (Fin (size + 1)) where
  weight index := weight index
  nonneg index := by exact_mod_cast hnonneg index
  sum_one := by exact_mod_cast hsum











def roundedLaw (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (ht : 0 < tickets) : FiniteDist (Fin (size + 1)) where
  weight index := (counts weight tickets index : ℝ) / tickets
  nonneg _ := by positivity
  sum_one := by
    rw [← Finset.sum_div, ← Nat.cast_sum, counts_total weight hnonneg hsum]
    exact div_self (by exact_mod_cast ht.ne')













end
end AFT.RationalFiniteQuantization

end

section



/-! # A finite rational program for pi with an explicit dyadic error

The program uses two convergent arctangent series and the proved identity
arctan(1/2)+arctan(1/3)=pi/4. No real-number oracle occurs in the program.
-/
namespace AFT.RationalNumerics
open scoped BigOperators

/-- A rational finite sum, executable by ordinary exact arithmetic. -/
def arctanSum (value : ℚ) (terms : ℕ) : ℚ :=
  ∑ index∈Finset.range terms,(-1 : ℚ)^index*value^(2*index+1)/(2*index+1 : ℕ)

def piApprox (bits : ℕ) : ℚ :=
  4*(arctanSum (1/2) (bits+3)+arctanSum (1/3) (bits+3))

noncomputable section
open scoped Classical







end
end AFT.RationalNumerics

end

section




/-! # Executable positive rational approximations to a negative exponential -/
namespace AFT.RationalNumerics
open scoped BigOperators

def expSum (value : ℚ) (terms : ℕ) : ℚ :=
  ∑ index∈Finset.range terms,value^index/(index.factorial : ℕ)

/-- Range reduction followed by a positive Taylor polynomial and an integer
power. In particular no exponential or real floor is evaluated by the code. -/
def expNegScaled (argument : ℚ) (scale bits : ℕ) : ℚ :=
  (expSum (argument/(scale : ℚ)) (bits+scale+1))⁻¹^scale

def expScale (argument : ℚ) : ℕ := 2*⌈max argument 0⌉₊+1

def expNegApprox (argument : ℚ) (bits : ℕ) : ℚ :=
  expNegScaled (max argument 0) (expScale argument) bits

noncomputable section
open scoped Classical

theorem expSum_ge_one (value : ℚ) (hv : 0 ≤ value) (terms : ℕ) (ht : 0 < terms) :
    1 ≤ (expSum value terms : ℝ) := by
  have hh := Finset.single_le_sum (f := fun i : ℕ => value^i/(i.factorial : ℕ))
    (fun i _ => by positivity) (Finset.mem_range.mpr ht)
  have hh' : (1 : ℚ) ≤ expSum value terms := by simpa only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,expSum] using hh
  exact_mod_cast hh'









theorem expScale_positive (argument : ℚ) : 0 < expScale argument := by
  unfold expScale
  omega



theorem expNegApprox_positive (argument : ℚ) (bits : ℕ) : 0 < expNegApprox argument bits := by
  have hs : (0 : ℚ) < expScale argument := by exact_mod_cast expScale_positive argument
  have hh := expSum_ge_one (max argument 0/(expScale argument : ℚ))
    (div_nonneg (le_max_right _ _) hs.le) (bits+expScale argument+1) (by omega)
  have hh' : (0 : ℚ) < expSum (max argument 0/(expScale argument : ℚ)) (bits+expScale argument+1) := by
    have hh0 : (0 : ℝ) < (expSum (max argument 0/(expScale argument : ℚ)) (bits+expScale argument+1) : ℝ) := by linarith
    exact_mod_cast hh0
  exact pow_pos (inv_pos.mpr hh') _



end
end AFT.RationalNumerics

end

section






/-! # Executable rational Gaussian weights at rational squared widths -/
namespace AFT.RationalNumerics

/-- Squared width avoids an unnecessary square-root computation. -/
def gaussianRatio (squaredWidth : ℚ) (point : ℤ) : ℚ := (point : ℚ)^2/squaredWidth

def gaussianGuard (squaredWidth : ℚ) (point : ℤ) : ℕ := ⌈gaussianRatio squaredWidth point⌉₊

def gaussianApprox (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) : ℚ :=
  expNegApprox (piApprox (bits+gaussianGuard squaredWidth point+1)*gaussianRatio squaredWidth point) (bits+1)

noncomputable section



theorem gaussianApprox_positive (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) :
    0 < gaussianApprox squaredWidth point bits := expNegApprox_positive _ _

/-- This exact special value keeps both the true and approximate Gaussian
normalizers at least one on every symmetric integer window. -/
theorem gaussianApprox_zero (squaredWidth : ℚ) (bits : ℕ) : gaussianApprox squaredWidth 0 bits=1 := by
  have hz (terms : ℕ) (ht : 0 < terms) : expSum 0 terms=1 := by
    unfold expSum
    rw [Finset.sum_eq_single 0]
    · simp
    · intro index hi hn
      simp [hn]
    · simp [Finset.mem_range.mpr ht]
  simp only [gaussianApprox,gaussianRatio,Int.cast_zero,zero_pow (by decide : 2 ≠ 0),zero_div,mul_zero,
    expNegApprox,max_self,expNegScaled,zero_div]
  rw [hz _ (by omega)]
  simp



end
end AFT.RationalNumerics

end

section







/-! # Materialized finite convolution tables

The executable recurrence stores each complete previous row in an array.
It does not enumerate all source words or recursively recompute its cells.
The work counter counts elementary arithmetic, comparisons and array accesses;
bit costs of the coefficient arithmetic remain separate.
-/
namespace AFT.FiniteConvolutionProgram
open scoped BigOperators

structure Result (R : Type*) where
  data : Array R
  work : ℕ

def lookup {R : Type*} [Zero R] (data : Array R) (target : ℕ) : R :=
  data[target]?.getD 0

/-- `alphabet` is the greatest source index. The previous row is evaluated
once and materialized before constructing the next row. -/
def run {R : Type*} [Semiring R] (alphabet : ℕ) (weight : Fin (alphabet+1) → R) : ℕ → Result R
  | 0 => ⟨#[1],1⟩
  | count+1 =>
      let previous := run alphabet weight count
      ⟨Array.ofFn (fun target : Fin (alphabet*(count+1)+1) =>
        ∑ source : Fin (alphabet+1),if source.val ≤ target.val then
          weight source*lookup previous.data (target.val-source.val) else 0),
        previous.work+(alphabet*(count+1)+1)*(5*(alphabet+1)+2)⟩





noncomputable section
open scoped Classical











end
end AFT.FiniteConvolutionProgram

end

section







/-! # The actual integer-window root probabilities are convolution-array entries -/
namespace AFT.FiniteConvolutionProgram
open GaussianSource
open scoped BigOperators

/-- Explicit increasing indexing of the complete protected integer window. -/
def windowIndexEquiv (cutoff : ℕ) : Fin (2*cutoff+1) ≃ Window cutoff where
  toFun index := ⟨(index.val : ℤ)-(cutoff : ℤ),Finset.mem_Icc.mpr (by have hi := index.isLt; constructor <;> omega)⟩
  invFun point := ⟨(point.val+(cutoff : ℤ)).toNat,by
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    omega⟩
  left_inv index := by apply Fin.ext; simp
  right_inv point := by
    apply Subtype.ext
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    dsimp only
    rw [Int.toNat_of_nonneg (by omega)]
    omega

/-- An integer target is shifted to the nonnegative coefficient index.
An impossible target below the entire support returns zero directly. -/
def integerLookup {R : Type*} [Zero R] (data : Array R) (radius : ℕ) (target : ℤ) : R :=
  if 0 ≤ target+(radius : ℤ) then lookup data (target+(radius : ℤ)).toNat else 0

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance rootConvolutionProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _











end
end AFT.FiniteConvolutionProgram

end

section







/-! # Restriction and normalization of an actual signed output law -/

namespace AFT.SignedConditioning

open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]

def restricted (mass : Color → ℝ) (event : Color → Prop) (color : Color) : ℝ :=
  if event color then mass color else 0

def conditionalMass (mass : Color → ℝ) (event : Color → Prop) (color : Color) : ℝ :=
  restricted mass event color / ∑ x, restricted mass event x









end

end AFT.SignedConditioning

end

section









/-! # Executable rational normalization of the actual protected Gaussian -/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

/-- Guard precision absorbs the number of atoms before normalization. -/
def windowApproxPrecision (cutoff bits : ℕ) : ℕ := bits+(2*cutoff+1)+1

def windowApproxRaw (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) : ℚ :=
  gaussianApprox squaredWidth point (windowApproxPrecision cutoff bits)

def windowApproxNormalizer (squaredWidth : ℚ) (cutoff bits : ℕ) : ℚ :=
  ∑ index : Fin (2*cutoff+1),
    windowApproxRaw squaredWidth cutoff bits (windowIndexEquiv cutoff index)

/-- This normalized table uses rational arithmetic only, including its denominator. -/
def windowApproxWeight (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) : ℚ :=
  windowApproxRaw squaredWidth cutoff bits point/windowApproxNormalizer squaredWidth cutoff bits

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Explicit finite numbering computes the same normalizer as the integer-window sum. -/
theorem windowApproxNormalizer_eq_sum (squaredWidth : ℚ) (cutoff bits : ℕ) :
    windowApproxNormalizer squaredWidth cutoff bits =
      ∑ point : Window cutoff, windowApproxRaw squaredWidth cutoff bits point :=
  (windowIndexEquiv cutoff).sum_comp _

theorem windowApproxNormalizer_ge_one (squaredWidth : ℚ) (cutoff bits : ℕ) :
    1 ≤ windowApproxNormalizer squaredWidth cutoff bits := by
  have h := Finset.single_le_sum (f:=windowApproxRaw squaredWidth cutoff bits)
    (fun point _ => (gaussianApprox_positive _ _ _).le) (Finset.mem_univ (windowZero cutoff))
  simpa only [windowApproxNormalizer_eq_sum,windowApproxRaw,windowZero,gaussianApprox_zero] using h

theorem windowApproxWeight_positive (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) :
    0 < windowApproxWeight squaredWidth cutoff bits point :=
  div_pos (gaussianApprox_positive _ _ _) (zero_lt_one.trans_le (windowApproxNormalizer_ge_one _ _ _))

theorem windowApproxWeight_sum (squaredWidth : ℚ) (cutoff bits : ℕ) :
    ∑ point : Window cutoff,windowApproxWeight squaredWidth cutoff bits point=1 := by
  simp only [windowApproxWeight,← Finset.sum_div]
  rw [← windowApproxNormalizer_eq_sum]
  exact div_self (ne_of_gt (zero_lt_one.trans_le (windowApproxNormalizer_ge_one _ _ _)))

/-- The law represented by the executable rational table. -/
def windowApproxLaw (squaredWidth : ℚ) (cutoff bits : ℕ) : FiniteDist (Window cutoff) where
  weight point := (windowApproxWeight squaredWidth cutoff bits point : ℝ)
  nonneg point := by exact_mod_cast (windowApproxWeight_positive squaredWidth cutoff bits point).le
  sum_one := by exact_mod_cast windowApproxWeight_sum squaredWidth cutoff bits



end
end AFT.RationalNumerics

end

section








/-! # Executable fair-bit approximations to every finite Gaussian window -/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

def windowTicketBits (cutoff bits : ℕ) : ℕ := bits+(2*cutoff+1)+2

def windowGaussianWeights (squaredWidth : ℚ) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) : ℚ :=
  windowApproxWeight squaredWidth cutoff bits (windowIndexEquiv cutoff index)

theorem windowGaussianWeights_nonneg (squaredWidth : ℚ) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    0≤windowGaussianWeights squaredWidth cutoff bits index := (windowApproxWeight_positive _ _ _ _).le

theorem windowGaussianWeights_sum (squaredWidth : ℚ) (cutoff bits : ℕ) :
    ∑ index,windowGaussianWeights squaredWidth cutoff bits index=1 := by
  unfold windowGaussianWeights
  rw [(windowIndexEquiv cutoff).sum_comp]
  exact windowApproxWeight_sum _ _ _

def windowTicketCounts (squaredWidth : ℚ) (cutoff bits : ℕ) : Fin (2*cutoff+1) → ℕ :=
  RationalFiniteQuantization.counts (windowGaussianWeights squaredWidth cutoff (bits+1))
    (2^(windowTicketBits cutoff bits))



def windowGaussianDraw (squaredWidth : ℚ) (cutoff bits : ℕ)
    (word : Fin (windowTicketBits cutoff bits) → Fin 2) : Window cutoff :=
  windowIndexEquiv cutoff (RationalFiniteQuantization.draw (windowGaussianWeights squaredWidth cutoff (bits+1))
    (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _) (windowTicketBits cutoff bits) word)

noncomputable section
set_option backward.isDefEq.respectTransparency false

def windowTicketLaw (squaredWidth : ℚ) (cutoff bits : ℕ) : FiniteDist (Window cutoff) :=
  (RationalFiniteQuantization.roundedLaw (windowGaussianWeights squaredWidth cutoff (bits+1))
    (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _)
    (2^(windowTicketBits cutoff bits)) (by positivity)).map (windowIndexEquiv cutoff)









end
end AFT.RationalNumerics

end

section










/-! # Executable actual leg and queue Gaussian sources

The cutoff constant is a natural number. Both leg cutoffs and Gaussian
weights are computed from integers and rationals; the sampler never asks
for a real exponential, real power, or real ceiling.
-/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics
open scoped BigOperators

/-- The source code uses this integer width and its rational square. -/
def actualAuxiliarySquaredWidth (scale n : ℕ) : ℚ := (scale*n : ℚ)^2









noncomputable section
set_option backward.isDefEq.respectTransparency false























end
end AFT.V7Calibration

end

section





/-! # Physical support of the genuine body blur and public pair inputs -/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology

noncomputable section



def boundaryHalf (cutoffScale : ℝ) (parameter : ℕ) : ℤ :=
  (Parameters.safeMargin parameter : ℤ) - maxBodyShift cutoffScale parameter



def pairSample (cutoffScale : ℝ) (parameter : ℕ) :=
  bodySample cutoffScale parameter × Window (legCutoff cutoffScale parameter - 1)

instance pairSampleFintype (cutoffScale : ℝ) (parameter : ℕ) : Fintype (pairSample cutoffScale parameter) :=
  inferInstanceAs (Fintype (_ × _))

def pairSourceLaw (cutoffScale : ℝ) (parameter : ℕ) : FiniteDist (pairSample cutoffScale parameter) :=
  (bodyBlur cutoffScale parameter).prod (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1))

def pairSourceShift (cutoffScale : ℝ) (parameter : ℕ) (sample : pairSample cutoffScale parameter) : ℤ :=
  sample.2

def startsPlus (cutoffScale : ℝ) (parameter : ℕ) (sample : pairSample cutoffScale parameter) : ℤ :=
  (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample.1

def startsMinus (cutoffScale : ℝ) (parameter : ℕ) (sample : pairSample cutoffScale parameter) : ℤ :=
  -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample.1



end

end AFT.GaussianSource

end

section





/-! # Calibrated means with every protected source and blur instantiated -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

def actualPrimary (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  primary parameter cutoffScale beta (boundaryHalf cutoffScale parameter)
    (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter)
    (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
    (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter)












end

end AFT.V7Calibration

end

section






namespace AFT
end AFT
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope


/-!
# The actual local inverse on arbitrary finite Hilbert fibers

Scalar profile bounds extend to arbitrary remaining-coordinate weights.
Applying the inverse separately in each remaining fiber and using its exact
operator equation yields the inverse mixed-activity bound without a
palette-dependent norm-equivalence constant.
-/

namespace AFT

open scoped BigOperators

section FiberTriangle

variable {ι κ : Type*} [Fintype ι] [Fintype κ]









@[simp] theorem coordinateActivity_neg (rate : ℝ) (primary : ι → ℝ) (remaining : κ → ℝ)
    (kernel : ι → κ → ℝ) :
    coordinateActivity rate primary remaining (-kernel) = coordinateActivity rate primary remaining kernel := by
  simp [coordinateActivity, integratedFiberNorm, fixedFiberNorm]

end FiberTriangle

section ProfileAmplification

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Apply an actual profile operator to the distinguished density coordinate. -/
noncomputable def partialProfileOperator (operator : Module.End ℝ (ι → ℝ))
    (primary : ι → ℝ) (kernel : ι → κ → ℝ) : ι → κ → ℝ :=
  fun output rest => operator (fun input => primary input * kernel input rest) output / primary output











omit [Fintype ι] [Fintype κ] in
@[simp] theorem partialProfileOperator_id (primary : ι → ℝ) (kernel : ι → κ → ℝ)
    (hp : ∀ color, 0 < primary color) :
    partialProfileOperator LinearMap.id primary kernel = kernel := by
  funext color rest
  exact mul_div_cancel_left₀ _ (ne_of_gt (hp color))















end ProfileAmplification

end AFT

end

section







/-!
# The actual V7 calibrated inverse on finite mixed fibers
-/

namespace AFT

open Filter
open scoped BigOperators Topology

namespace V7Calibration





/-- Uniform width-W anchors reflected about q-1-c, with a fair direction
at the midpoint. The Boolean is irrelevant off the midpoint. -/
def publicAnchorStart (modulus width : ℕ) (color : Fin modulus) (coin : Bool) : ℤ :=
  if 2 * color.val < modulus - 1 then (modulus : ℤ) - color.val - 2 * width
  else if modulus - 1 < 2 * color.val then (modulus : ℤ) - 1 - color.val + width
  else if coin then (modulus : ℤ) - color.val - 2 * width
    else (modulus : ℤ) - 1 - color.val + width

















end V7Calibration
end AFT

end

section






namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary



/-! # Exact public anchor means and their calibrated supremum bound -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section





namespace V7Calibration

/-- The true fair midpoint anchor kernel, with both non-midpoint directions. -/
def publicAnchorKernel (modulus width : ℕ) (color : Fin modulus) (output : ℤ) : ℝ :=
  (intervalAnchorLaw (publicAnchorStart modulus width color true) width output +
    intervalAnchorLaw (publicAnchorStart modulus width color false) width output) / 2

def anchorMean (modulus width : ℕ) (profile : Fin modulus → ℝ) (output : ℤ) : ℝ :=
  ∑ color, profile color * publicAnchorKernel modulus width color output

theorem publicAnchorKernel_nonneg (modulus width : ℕ) (color : Fin modulus) (output : ℤ) :
    0 ≤ publicAnchorKernel modulus width color output := by
  unfold publicAnchorKernel
  exact div_nonneg (add_nonneg (intervalAnchorLaw_nonneg _ _ _) (intervalAnchorLaw_nonneg _ _ _)) (by norm_num)











end V7Calibration
end
end AFT

end

section





/-!
# Actual public anchor support and the calibrated legal-input projection
-/

namespace AFT.V7Calibration

open scoped BigOperators

/-- Every point of the actual reflected public anchor remains safe after
any displacement admitted by the physical margin. -/
theorem publicAnchorStart_safe (modulus width : ℕ) (color : Fin modulus) (coin : Bool)
    (shift margin : ℤ) (hmodulus : 6 * width + 1 ≤ modulus)
    (hmargin : margin + |shift| ≤ width) (output : ℤ)
    (houtput : output ∈ anchorInterval (publicAnchorStart modulus width color coin + shift) width) :
    margin ≤ output ∧ output < (modulus : ℤ) - margin := by
  have hq : 0 < modulus := Nat.zero_lt_of_lt color.isLt
  have hqcast : ((modulus - 1 : ℕ) : ℤ) = (modulus : ℤ) - 1 := by omega
  have hmod : 6 * (width : ℤ) + 1 ≤ modulus := by exact_mod_cast hmodulus
  have hleft (hhalf : 2 * (color.val : ℤ) ≤ (modulus : ℤ) - 1)
      (hc : output ∈ anchorInterval ((modulus : ℤ) - color.val - 2 * width + shift) width) :
      margin ≤ output ∧ output < (modulus : ℤ) - margin := by
    simp only [anchorInterval, Finset.mem_Ico] at hc
    let offset := (modulus : ℤ) - 1 - color.val + shift - output
    have hl : (width : ℤ) ≤ offset := by dsimp [offset]; omega
    have hu : offset < 2 * (width : ℤ) := by dsimp [offset]; omega
    have hh := publicAnchor_left_safe modulus width color.val offset shift margin |shift|
      hmod (by positivity) hhalf hl hu le_rfl hmargin
    dsimp [offset] at hh
    omega
  have hright (hhalf : (modulus : ℤ) - 1 ≤ 2 * (color.val : ℤ))
      (hc : output ∈ anchorInterval ((modulus : ℤ) - 1 - color.val + width + shift) width) :
      margin ≤ output ∧ output < (modulus : ℤ) - margin := by
    simp only [anchorInterval, Finset.mem_Ico] at hc
    let offset := output - ((modulus : ℤ) - 1 - color.val + shift)
    have hl : (width : ℤ) ≤ offset := by dsimp [offset]; omega
    have hu : offset < 2 * (width : ℤ) := by dsimp [offset]; omega
    have hh := publicAnchor_right_safe modulus width color.val offset shift margin |shift|
      hmod (by exact_mod_cast color.isLt) hhalf hl hu le_rfl hmargin
    dsimp [offset] at hh
    omega
  unfold publicAnchorStart at houtput
  split_ifs at houtput with hl hr hc
  · exact hleft (by omega) houtput
  · exact hright (by omega) houtput
  · exact hleft (by omega) houtput
  · exact hright (by omega) houtput





end AFT.V7Calibration

end

section







/-! # Safe public anchor kernels with the actual optional blur -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem intervalAnchorLaw_palette_mass (modulus width : ℕ) (start : ℤ) (hw : width ≠ 0)
    (hsupport : ∀ output ∈ anchorInterval start width, 0 ≤ output ∧ output < modulus) :
    (∑ color : Fin modulus, intervalAnchorLaw start width color.val) = 1 := by
  let support : Finset (Fin modulus) := Finset.univ.filter fun c => (c.val : ℤ) ∈ anchorInterval start width
  have hc : support.card = width := by
    have hh := Finset.card_bij (s := support) (t := anchorInterval start width)
      (fun (c : Fin modulus) _ => (c.val : ℤ))
      (by intro c hc; exact (Finset.mem_filter.mp hc).2)
      (by intro a _ b _ h; change (a.val : ℤ) = b.val at h; apply Fin.ext; exact_mod_cast h)
      (by
        intro output hout
        have hb := hsupport output hout
        let point : Fin modulus := ⟨output.toNat, by omega⟩
        have heq : (point.val : ℤ) = output := by dsimp [point]; omega
        exact ⟨point, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [heq] using hout⟩, heq⟩)
    simpa only [anchorInterval_card] using hh
  simp only [intervalAnchorLaw, ← Finset.sum_filter]
  change (∑ _color ∈ support, (width : ℝ)⁻¹) = 1
  simp [hc, Nat.cast_ne_zero.mpr hw]

namespace V7Calibration
open GaussianSource











theorem publicAnchorKernel_translate (modulus width : ℕ) (color : Fin modulus) (output shift : ℤ) :
    publicAnchorKernel modulus width color (output - shift) =
      (intervalAnchorLaw (publicAnchorStart modulus width color true + shift) width output +
        intervalAnchorLaw (publicAnchorStart modulus width color false + shift) width output) / 2 := by
  simp only [publicAnchorKernel, intervalAnchorLaw_translate]

theorem publicAnchorKernel_safe_mass (modulus width : ℕ) (margin shift : ℤ)
    (hw : width ≠ 0) (hmodulus : 6 * width + 1 ≤ modulus) (hm0 : 0 ≤ margin)
    (hmargin : margin + |shift| ≤ width) (color : Fin modulus) :
    (∑ output : Fin modulus, publicAnchorKernel modulus width color ((output.val : ℤ) - shift)) = 1 ∧
    (∀ output : ℤ, output < margin ∨ (modulus : ℤ) - margin ≤ output →
      publicAnchorKernel modulus width color (output - shift) = 0) := by
  have hs (coin : Bool) (output : ℤ)
      (hout : output ∈ anchorInterval (publicAnchorStart modulus width color coin + shift) width) :=
    publicAnchorStart_safe modulus width color coin shift margin hmodulus hmargin output hout
  constructor
  · simp only [publicAnchorKernel_translate, ← Finset.sum_div, Finset.sum_add_distrib]
    rw [intervalAnchorLaw_palette_mass modulus width _ hw (by intro output hout; have hh := hs true output hout; omega),
      intervalAnchorLaw_palette_mass modulus width _ hw (by intro output hout; have hh := hs false output hout; omega)]
    norm_num
  · intro output hout
    have hz (coin : Bool) : intervalAnchorLaw (publicAnchorStart modulus width color coin + shift) width output = 0 := by
      unfold intervalAnchorLaw
      split_ifs with hmem
      · have hh := hs coin output hmem; omega
      · rfl
    rw [publicAnchorKernel_translate, hz true, hz false]
    norm_num









end V7Calibration
end
end AFT

end

section





/-! # The actual positive, calibrated safe-center probability -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

def safePalette (parameter : ℕ) : Finset (Fin (Parameters.modulus parameter)) :=
  TrimmedSlice.paletteSlice (Parameters.modulus parameter) (Parameters.safeMargin parameter) 0

theorem safePalette_nonempty (parameter : ℕ) : (safePalette parameter).Nonempty := by
  apply TrimmedSlice.paletteSlice_nonempty _ _ _ (by positivity)
  have hh := Parameters.safeSize_positive parameter
  unfold Parameters.safeSize at hh
  simp only [abs_zero, add_zero]
  omega

def actualCoreLaw (parameter : ℕ) : FiniteDist (Fin (Parameters.modulus parameter)) :=
  FiniteDist.uniformSafe (safePalette parameter) (safePalette_nonempty parameter)



theorem safeMargin_le_anchor (parameter : ℕ) : Parameters.safeMargin parameter ≤ Parameters.anchorWidth parameter := by
  have hh : 20 ≤ Parameters.security parameter ^ 30 := by
    have hh := Nat.pow_le_pow_left (Parameters.security_ge_two parameter) 30
    omega
  have hh' := Nat.mul_le_mul_right (Parameters.security parameter ^ 2) hh
  simpa only [Parameters.safeMargin, Parameters.anchorWidth, ← pow_add] using hh'

theorem actual_anchor_safe_mass (parameter : ℕ) (color : Fin (Parameters.modulus parameter)) :
    (∑ output : Fin (Parameters.modulus parameter), publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      color output.val) = 1 ∧
    (∀ output : Fin (Parameters.modulus parameter), output ∉ safePalette parameter →
      publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color output.val = 0) := by
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact ne_of_gt (pow_pos (lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)) 32)
  have hh := publicAnchorKernel_safe_mass (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    (Parameters.safeMargin parameter) 0 hw (Parameters.anchor_clearance parameter) (by positivity)
    (by simpa only [abs_zero, add_zero] using (show (Parameters.safeMargin parameter : ℤ) ≤ Parameters.anchorWidth parameter by exact_mod_cast safeMargin_le_anchor parameter)) color
  refine ⟨hh.1, ?_⟩
  intro output hout
  apply hh.2 output.val
  simp only [safePalette, TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and,
    TrimmedSlice.mem_slice] at hout
  omega



/-- The actual compensated center profile, including the calibrated primary. -/
def actualBodyCenter (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) : Fin (Parameters.modulus parameter) → ℝ :=
  calibratedBodyProfile (actualCoreLaw parameter).weight
    (fun center => anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (actualPrimary cutoffScale parameter beta) center.val)
    (bodyCompensation parameter cutoffScale)





end
end AFT.V7Calibration

end


