-- Prove2me | Definitions.Def_InfoLossLAR_NativeSparsePrefix_03
-- name    : InfoLossLAR_NativeSparsePrefix_03
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T13:22:46.089039+00:00
-- url     : https://prove2.me/theorems/1fd8fee5-254a-4017-bc66-91baf67a7288
-- title:
--   Safe paired sources and canonical block convolution
-- statement:
--   This package defines safe paired and triple source data, masked window translations, Hilbert profile and block-product spaces, public placement and reference laws, canonical convolution, and finite Neumann correction interfaces.
--
--   These interfaces retain the joint source and public placement data needed by later canonical response and energy estimates. They expose mathematical data and the supporting constructor APIs; the subsequent response, approximation, and transport bounds are stated as separate theorems. Recorded native operation charges are not by themselves platform machine-time certificates.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; Lean source modules AFT/TrimmedPair.lean, AFT/SafePairCore.lean, AFT/ActualTriples.lean, AFT/PairWindowTranslation.lean, AFT/MaskedWindowTranslation.lean, AFT/HilbertConcentration.lean, AFT/ProfileHilbert.lean, AFT/TripleMarginals.lean, AFT/BlockProducts.lean, AFT/FiniteBlockNumbering.lean, AFT/V7ReferenceLaws.lean, AFT/V7Blocks.lean, AFT/PublicPlacement.lean, AFT/V7PublicPlacement.lean, AFT/ActualNormalizedMean.lean, AFT/BetaReference.lean, AFT/FiniteConvolution.lean, AFT/SafeFiniteNeumann.lean, AFT/CanonicalConvolution.lean, AFT/CoreProjectionEnergy.lean, AFT/CoreCenteringDifference.lean. Source bodies and declaration spans are recorded in native_sparse_prefix/manifest.json; SHA256 94d8d539ee8681d1bb262ae64fd98cfa2cc383948486bb6b2088987c71defdf9. Repackaging of identical data declarations, with 4163 public types matched to native source and 7722 origin declarations recursively audited for standard logical axioms only.

import Definitions.Def_InfoLossLAR_NativeSparsePrefix_02
import Definitions.Def_InfoLossLAR_Native_AFT_FiniteConcentration

section









/-!
# The actual integer-window endpoint pair and its exact marginals
-/

namespace AFT.TrimmedSlice

open scoped BigOperators

/-- Draw the first endpoint uniformly from its actual trimmed slice, then
set the second endpoint by the required integer pair sum. -/
noncomputable def orderedPairSlice (modulus : ℕ) (boundary shift : ℤ)
    (first second : Fin modulus) : ℝ :=
  law modulus boundary shift first.val *
    if (second.val : ℤ) = (modulus : ℤ) - 1 + shift - first.val then 1 else 0

theorem orderedPairSlice_nonneg (modulus : ℕ) (boundary shift : ℤ) (first second : Fin modulus) :
    0 ≤ orderedPairSlice modulus boundary shift first second := by
  unfold orderedPairSlice
  exact mul_nonneg (law_nonneg _ _ _ _) (by split_ifs <;> norm_num)

theorem orderedPairSlice_marginal (modulus : ℕ) (boundary shift : ℤ)
    (hb : 0 ≤ boundary) (first : Fin modulus) :
    ∑ second, orderedPairSlice modulus boundary shift first second = law modulus boundary shift first.val := by
  classical
  by_cases hc : (first.val : ℤ) ∈ slice modulus boundary shift
  · have hs := (mem_slice modulus boundary shift first.val).mp hc
    let output := (modulus : ℤ) - 1 + shift - first.val
    have houtput : 0 ≤ output ∧ output < modulus := by dsimp [output]; omega
    let second : Fin modulus := ⟨output.toNat, by omega⟩
    have heq : (second.val : ℤ) = output := by dsimp [second]; omega
    have hdelta (color : Fin modulus) : ((color.val : ℤ) = output) ↔ color = second := by
      constructor
      · intro hh
        apply Fin.ext
        have ht : (color.val : ℤ) = second.val := hh.trans heq.symm
        exact_mod_cast ht
      · rintro rfl
        exact heq
    simp only [orderedPairSlice, ← Finset.mul_sum]
    change law modulus boundary shift first.val * (∑ color : Fin modulus, if (color.val : ℤ) = output then 1 else 0) = _
    simp only [hdelta, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
  · simp only [orderedPairSlice, law, if_neg hc, zero_mul, Finset.sum_const_zero]

theorem orderedPairSlice_symmetric (modulus : ℕ) (boundary shift : ℤ)
    (first second : Fin modulus) :
    orderedPairSlice modulus boundary shift first second = orderedPairSlice modulus boundary shift second first := by
  have hrel : ((second.val : ℤ) = (modulus : ℤ) - 1 + shift - first.val) ↔
      ((first.val : ℤ) = (modulus : ℤ) - 1 + shift - second.val) := by omega
  unfold orderedPairSlice
  by_cases hr : (second.val : ℤ) = (modulus : ℤ) - 1 + shift - first.val
  · have hc : (first.val : ℤ) ∈ slice modulus boundary shift ↔
        (second.val : ℤ) ∈ slice modulus boundary shift := by
      simp only [mem_slice]
      omega
    simp only [if_pos hr, if_pos (hrel.mp hr), mul_one, law, hc]
  · simp only [if_neg hr, if_neg (fun hh => hr (hrel.mpr hh)), mul_zero]

noncomputable def averagedPair (modulus : ℕ) (boundary start source : ℤ) (width : ℕ)
    (first second : Fin modulus) : ℝ :=
  ∑ offset ∈ anchorInterval start width,
    intervalAnchorLaw start width offset * orderedPairSlice modulus boundary (offset - source) first second

noncomputable def mixedPair {τ : Type*} [Fintype τ] (modulus : ℕ) (boundary : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (first second : Fin modulus) : ℝ :=
  ∑ index, weights index * averagedPair modulus boundary (starts index) (sources index) width first second

/-- The exact joint mass keeps the integer sum and its nonconstant slice
denominator; no circular-window replacement is used. -/
theorem averagedPair_formula (modulus : ℕ) (boundary start source : ℤ) (width : ℕ)
    (first second : Fin modulus) :
    averagedPair modulus boundary start source width first second =
      intervalAnchorLaw start width ((first.val : ℤ) + second.val - ((modulus : ℤ) - 1) + source) *
      law modulus boundary ((first.val : ℤ) + second.val - ((modulus : ℤ) - 1)) first.val := by
  let offset := (first.val : ℤ) + second.val - ((modulus : ℤ) - 1) + source
  unfold averagedPair
  rw [Finset.sum_eq_single offset]
  · have hs : offset - source = (first.val : ℤ) + second.val - ((modulus : ℤ) - 1) := by dsimp [offset]; ring
    have hd : (second.val : ℤ) = (modulus : ℤ) - 1 + (offset - source) - first.val := by dsimp [offset]; ring
    simp only [orderedPairSlice]
    rw [if_pos hd, mul_one, hs]
  · intro other _ hne
    have hd : ¬ (second.val : ℤ) = (modulus : ℤ) - 1 + (other - source) - first.val := by
      dsimp [offset] at hne
      omega
    simp [orderedPairSlice, hd]
  · intro hout
    simp only [intervalAnchorLaw, if_neg hout, zero_mul]

theorem mixedPair_first_marginal {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary : ℤ) (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ)
    (hb : 0 ≤ boundary) (first : Fin modulus) :
    ∑ second, mixedPair modulus boundary starts sources weights width first second =
      mixedLaw modulus boundary starts sources weights width first.val := by
  unfold mixedPair mixedLaw averagedPair averagedLaw intervalMixture
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, orderedPairSlice_marginal modulus boundary _ hb]

theorem mixedPair_symmetric {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary : ℤ) (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ)
    (first second : Fin modulus) :
    mixedPair modulus boundary starts sources weights width first second =
      mixedPair modulus boundary starts sources weights width second first := by
  simp only [mixedPair, averagedPair, orderedPairSlice_symmetric modulus boundary _ first second]

theorem mixedPair_nonneg {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary : ℤ) (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ)
    (hw : ∀ index, 0 ≤ weights index) (first second : Fin modulus) :
    0 ≤ mixedPair modulus boundary starts sources weights width first second := by
  apply Finset.sum_nonneg
  intro index _
  apply mul_nonneg (hw index)
  apply Finset.sum_nonneg
  intro offset _
  exact mul_nonneg (intervalAnchorLaw_nonneg _ _ _) (orderedPairSlice_nonneg _ _ _ _ _)

theorem mixedPair_mass {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (weights : τ → ℝ)
    (hmass : ∑ index, weights index = 1) (hb : 0 ≤ boundary)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) :
    ∑ first, ∑ second, mixedPair modulus boundary starts sources weights width first second = 1 := by
  simp_rw [mixedPair_first_marginal modulus boundary starts sources weights width hb]
  exact mixedLaw_palette_mass modulus boundary shiftBound cutoff width hwidth starts sources weights hmass hb hstarts hsources hclear

/-- The physical joint endpoint mass has the sharp `1/(W*(q-D))` ceiling. -/
theorem mixedPair_le {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ)
    (starts sources : τ → ℤ) (weights : τ → ℝ)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) (first second : Fin modulus) :
    mixedPair modulus boundary starts sources weights width first second ≤
      1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) := by
  have hden : 0 < (modulus : ℝ) - 2 * boundary - shiftBound - cutoff := by
    have hh : (0 : ℤ) < (modulus : ℤ) - 2 * boundary - shiftBound - cutoff := by omega
    exact_mod_cast hh
  have hrow (index : τ) : averagedPair modulus boundary (starts index) (sources index) width first second ≤
      (width : ℝ)⁻¹ * (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) := by
    rw [averagedPair_formula]
    let shift := (first.val : ℤ) + second.val - ((modulus : ℤ) - 1)
    by_cases hin : shift + sources index ∈ anchorInterval (starts index) width
    · have hs : |shift| ≤ shiftBound + cutoff := by
        have hh := (abs_sub (shift + sources index) (sources index)).trans
          (add_le_add (hstarts index _ hin) (hsources index))
        simpa only [add_sub_cancel_right] using hh
      have hslice := law_le_of_shift_bound (modulus : ℤ) boundary shift (shiftBound + cutoff) first.val hs (by omega)
      have hh := mul_le_mul (intervalAnchorLaw_bound (starts index) (shift + sources index) width)
        hslice (law_nonneg _ _ _ _) (inv_nonneg.mpr (Nat.cast_nonneg width))
      simpa only [Int.cast_add, Int.cast_natCast, sub_add_eq_sub_sub] using hh
    · have hz : intervalAnchorLaw (starts index) width (shift + sources index) = 0 := by simp [intervalAnchorLaw, hin]
      change intervalAnchorLaw (starts index) width (shift + sources index) * _ ≤ _
      rw [hz, zero_mul]
      positivity
  calc
    _ ≤ ∑ index, weights index * ((width : ℝ)⁻¹ *
      (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (hrow index) (hweights index)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]; simp only [one_div, mul_inv_rev, mul_comm]

/-- The endpoint construction is an actual finite probability distribution. -/
noncomputable def mixedPairDistribution {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (sourceLaw : FiniteDist τ) (hb : 0 ≤ boundary)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) : FiniteDist (Fin modulus × Fin modulus) where
  weight point := mixedPair modulus boundary starts sources sourceLaw.weight width point.1 point.2
  nonneg point := mixedPair_nonneg _ _ _ _ _ _ sourceLaw.nonneg _ _
  sum_one := by
    rw [Fintype.sum_prod_type]
    exact mixedPair_mass modulus boundary shiftBound cutoff width hwidth starts sources sourceLaw.weight
      sourceLaw.sum_one hb hstarts hsources hclear



/-- Fixing either endpoint leaves counting-square mass at most
`1/(W*(q-D)^2)`, rather than introducing a palette-size factor. -/
theorem mixedPair_fiber_square_le {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (sourceLaw : FiniteDist τ) (hb : 0 ≤ boundary)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) (first : Fin modulus) :
    (∑ second, mixedPair modulus boundary starts sources sourceLaw.weight width first second ^ 2) ≤
      1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) ^ 2) := by
  have hden : 0 < (modulus : ℝ) - 2 * boundary - shiftBound - cutoff := by
    have hh : (0 : ℤ) < (modulus : ℤ) - 2 * boundary - shiftBound - cutoff := by omega
    exact_mod_cast hh
  have hheight := mixedPair_le modulus boundary shiftBound cutoff width starts sources sourceLaw.weight
    sourceLaw.nonneg sourceLaw.sum_one hstarts hsources hclear
  have hmarginal := mixedLaw_le (modulus : ℤ) boundary shiftBound cutoff starts sources sourceLaw.weight width
    hwidth sourceLaw.nonneg sourceLaw.sum_one hstarts hsources hclear first.val
  calc
    _ ≤ ∑ second, (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) *
        mixedPair modulus boundary starts sources sourceLaw.weight width first second := by
      apply Finset.sum_le_sum
      intro second _
      have hh := mul_le_mul_of_nonneg_right (hheight first second)
        (mixedPair_nonneg modulus boundary starts sources sourceLaw.weight width sourceLaw.nonneg first second)
      nlinarith only [hh]
    _ = (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) *
        mixedLaw modulus boundary starts sources sourceLaw.weight width first.val := by
      rw [← Finset.mul_sum, mixedPair_first_marginal _ _ _ _ _ _ hb]
    _ ≤ (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) *
        (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Int.cast_natCast] using hmarginal) (by positivity)
    _ = _ := by
      have hwReal : (width : ℝ) ≠ 0 := by exact_mod_cast hwidth
      field_simp

end AFT.TrimmedSlice

end

section










/-!
# Safely supported canonical seeds for the true integer-window pair
-/

namespace AFT.SafePair

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def restrictPair (core : Finset ι) (mass : ι → ι → ℝ) (first second : ι) : ℝ :=
  if first ∈ core ∧ second ∈ core then mass first second else 0

/-- Canonicalize the actual signed pair by subtracting both true marginals
and restoring its total mass once. -/
noncomputable def canonicalPair (reference : ι → ℝ) (mass : ι → ι → ℝ) (first second : ι) : ℝ :=
  mass first second - reference first * (∑ x, mass x second) -
    (∑ y, mass first y) * reference second +
    (∑ x, ∑ y, mass x y) * reference first * reference second

omit [DecidableEq ι] in
theorem canonicalPair_first (reference : ι → ℝ) (mass : ι → ι → ℝ)
    (href : ∑ color, reference color = 1) (first : ι) :
    ∑ second, canonicalPair reference mass first second = 0 := by
  unfold canonicalPair
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, href, mul_one]
  rw [Finset.sum_comm (f := fun y x => mass x y)]
  ring

omit [DecidableEq ι] in
theorem canonicalPair_transpose (reference : ι → ℝ) (mass : ι → ι → ℝ) (first second : ι) :
    canonicalPair reference mass first second =
      canonicalPair reference (fun x y => mass y x) second first := by
  unfold canonicalPair
  rw [Finset.sum_comm (f := fun x y => mass y x)]
  ring

omit [DecidableEq ι] in
theorem canonicalPair_second (reference : ι → ℝ) (mass : ι → ι → ℝ)
    (href : ∑ color, reference color = 1) (second : ι) :
    ∑ first, canonicalPair reference mass first second = 0 := by
  simp_rw [canonicalPair_transpose reference mass]
  exact canonicalPair_first reference (fun x y => mass y x) href second

/-- The actual seed obtained by deleting the edge strips and using uniform
core centering. Its mass and both marginals are exactly zero. -/
noncomputable def coreSeed (core : Finset ι) (mass : ι → ι → ℝ) : ι → ι → ℝ :=
  canonicalPair (uniformFiniteProfile core) (restrictPair core mass)

theorem coreSeed_canonical (core : Finset ι) (mass : ι → ι → ℝ) (hne : core.Nonempty) :
    (∀ first, ∑ second, coreSeed core mass first second = 0) ∧
    (∀ second, ∑ first, coreSeed core mass first second = 0) :=
  ⟨canonicalPair_first _ _ (uniformFiniteProfile_mass core hne),
    canonicalPair_second _ _ (uniformFiniteProfile_mass core hne)⟩

theorem coreSeed_supported (core : Finset ι) (mass : ι → ι → ℝ)
    (first second : ι) (hout : first ∉ core ∨ second ∉ core) :
    coreSeed core mass first second = 0 := by
  rcases hout with hfirst | hsecond
  · simp [coreSeed, canonicalPair, uniformFiniteProfile, restrictPair, hfirst]
  · simp [coreSeed, canonicalPair, uniformFiniteProfile, restrictPair, hsecond]

/-- Deleting either edge strip is charged to its actual fixed-coordinate
square sum. There is no ambient-palette union bound. -/
theorem restriction_square_loss (core : Finset ι) (mass : ι → ι → ℝ) (rowBound : ℝ)
    (hrow : ∀ first, (∑ second, mass first second ^ 2) ≤ rowBound)
    (hcolumn : ∀ second, (∑ first, mass first second ^ 2) ≤ rowBound) :
    (∑ first, ∑ second, (mass first second - restrictPair core mass first second) ^ 2) ≤
      2 * (coreᶜ.card : ℝ) * rowBound := by
  have hfilter : (Finset.univ.filter fun color : ι => color ∉ core) = coreᶜ := by ext; simp
  have hfirst : (∑ first : ι, ∑ second : ι, if first ∉ core then mass first second ^ 2 else 0) ≤
      (coreᶜ.card : ℝ) * rowBound := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite, hfilter]
    simp only [Finset.sum_const_zero, add_zero]
    calc
      _ ≤ ∑ _first ∈ coreᶜ, rowBound := Finset.sum_le_sum fun first _ => hrow first
      _ = _ := by simp
  have hsecond : (∑ first : ι, ∑ second : ι, if second ∉ core then mass first second ^ 2 else 0) ≤
      (coreᶜ.card : ℝ) * rowBound := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite, hfilter]
    simp only [Finset.sum_const_zero, add_zero]
    calc
      _ ≤ ∑ _second ∈ coreᶜ, rowBound := Finset.sum_le_sum fun second _ => hcolumn second
      _ = _ := by simp
  calc
    _ ≤ ∑ first, ∑ second, ((if first ∉ core then mass first second ^ 2 else 0) +
        (if second ∉ core then mass first second ^ 2 else 0)) := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      by_cases hf : first ∈ core <;> by_cases hs : second ∈ core <;>
        simp [restrictPair, hf, hs, sq_nonneg]
    _ = (∑ first, ∑ second, if first ∉ core then mass first second ^ 2 else 0) +
        (∑ first, ∑ second, if second ∉ core then mass first second ^ 2 else 0) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ _ := by linarith

/-- For the actual integer-window pair, the deleted-core square loss is
`4*coreDepth/(W*(q-D)^2)` before uniform-profile scaling by q². -/
theorem actual_core_square_loss {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff coreDepth : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (sourceLaw : FiniteDist τ) (hb : 0 ≤ boundary)
    (hcore : 0 ≤ coreDepth) (hcoreSmall : 2 * coreDepth ≤ modulus)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) :
    let mass := TrimmedSlice.mixedPair modulus boundary starts sources sourceLaw.weight width
    let core := TrimmedSlice.paletteSlice modulus coreDepth 0
    (∑ first, ∑ second, (mass first second - restrictPair core mass first second) ^ 2) ≤
      4 * (coreDepth : ℝ) /
        ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) ^ 2) := by
  dsimp only
  have hrow := TrimmedSlice.mixedPair_fiber_square_le modulus boundary shiftBound cutoff width hwidth
    starts sources sourceLaw hb hstarts hsources hclear
  have hcolumn (second : Fin modulus) :
      (∑ first, TrimmedSlice.mixedPair modulus boundary starts sources sourceLaw.weight width first second ^ 2) ≤
        1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) ^ 2) := by
    simpa only [TrimmedSlice.mixedPair_symmetric modulus boundary starts sources sourceLaw.weight width _ second] using hrow second
  have hcard : ((TrimmedSlice.paletteSlice modulus coreDepth 0)ᶜ.card : ℝ) = 2 * (coreDepth : ℝ) := by
    exact_mod_cast boundaryPalette_card modulus coreDepth hcore hcoreSmall
  have hh := restriction_square_loss (TrimmedSlice.paletteSlice modulus coreDepth 0)
    (TrimmedSlice.mixedPair modulus boundary starts sources sourceLaw.weight width)
    (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) ^ 2)) hrow hcolumn
  rw [hcard] at hh
  exact hh.trans_eq (by ring)

end AFT.SafePair

end

section








namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap


/-! # The actual inactive source and shared-source local triple identities -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section

namespace FiniteDist
variable {α : Type*} [Fintype α]

theorem atom_le_one (p : FiniteDist α) (point : α) : p.weight point ≤ 1 := by
  have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => p.nonneg i) (Finset.mem_univ point)
  simpa only [p.sum_one] using hh





end FiniteDist

namespace GaussianSource









end GaussianSource

namespace V7Calibration
open GaussianSource

























end V7Calibration
end
end AFT

end

section







/-! # Translation of the genuine integer pair window and its denominator -/

set_option backward.isDefEq.respectTransparency false

namespace AFT.TrimmedSlice

open scoped BigOperators

/-- A positive extension of the real reciprocal slice length. On every
allowed window it agrees exactly with the physical denominator; the
extension merely permits a global translation estimate. -/
noncomputable def reciprocalSlice (modulus boundary lower : ℝ) (sum : ℤ) : ℝ :=
  (max (modulus - 2 * boundary - |(sum : ℝ)|) lower)⁻¹

theorem reciprocalSlice_nonneg (modulus boundary lower : ℝ) (hlower : 0 < lower) (sum : ℤ) :
    0 ≤ reciprocalSlice modulus boundary lower sum := by
  unfold reciprocalSlice
  exact inv_nonneg.mpr ((le_max_right _ _).trans' hlower.le)

theorem reciprocalSlice_le (modulus boundary lower : ℝ) (hlower : 0 < lower) (sum : ℤ) :
    reciprocalSlice modulus boundary lower sum ≤ lower⁻¹ := by
  exact inv_anti₀ hlower (le_max_right _ _)

/-- The nonconstant denominator has Lipschitz cost 1/lower², derived
from the integer absolute-value slice length. -/
theorem reciprocalSlice_lipschitz (modulus boundary lower : ℝ) (hlower : 0 < lower) (first second : ℤ) :
    |reciprocalSlice modulus boundary lower first - reciprocalSlice modulus boundary lower second| ≤
      |(first : ℝ) - second| / lower ^ 2 := by
  let a := max (modulus - 2 * boundary - |(first : ℝ)|) lower
  let b := max (modulus - 2 * boundary - |(second : ℝ)|) lower
  have ha : lower ≤ a := le_max_right _ _
  have hb : lower ≤ b := le_max_right _ _
  have ha0 : 0 < a := hlower.trans_le ha
  have hb0 : 0 < b := hlower.trans_le hb
  have hdiff : |b - a| ≤ |(first : ℝ) - second| := by
    have hh := abs_max_sub_max_le_abs (modulus - 2 * boundary - |(second : ℝ)|)
      (modulus - 2 * boundary - |(first : ℝ)|) lower
    have heq : modulus - 2 * boundary - |(second : ℝ)| - (modulus - 2 * boundary - |(first : ℝ)|) =
        |(first : ℝ)| - |(second : ℝ)| := by ring
    rw [heq] at hh
    exact hh.trans (abs_abs_sub_abs_le _ _)
  have hprod : lower ^ 2 ≤ a * b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  change |a⁻¹ - b⁻¹| ≤ _
  have heq : |a⁻¹ - b⁻¹| = |b - a| / (a * b) := by
    rw [inv_sub_inv ha0.ne' hb0.ne', abs_div, abs_of_pos (mul_pos ha0 hb0)]
  rw [heq]
  exact (div_le_div_of_nonneg_right hdiff (mul_nonneg ha0.le hb0.le)).trans
    (div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hlower) hprod)

noncomputable def weightedIntegerWindow (modulus boundary lower : ℝ) (start source : ℤ) (width : ℕ) (sum : ℤ) : ℝ :=
  intervalAnchorLaw start width (sum + source) * reciprocalSlice modulus boundary lower sum

/-- The pointwise difference separates the two changed window strips from
the exact reciprocal-denominator variation. -/
theorem weightedIntegerWindow_difference_square (modulus boundary lower : ℝ) (hlower : 0 < lower)
    (start source shift sum : ℤ) (width : ℕ) :
    (weightedIntegerWindow modulus boundary lower start source width (sum - shift) -
      weightedIntegerWindow modulus boundary lower start source width sum) ^ 2 ≤
      (2 / lower ^ 2) * (intervalAnchorLaw (start + shift) width (sum + source) - intervalAnchorLaw start width (sum + source)) ^ 2 +
        (2 * (shift : ℝ) ^ 2 / lower ^ 4) * intervalAnchorLaw start width (sum + source) ^ 2 := by
  let a := intervalAnchorLaw (start + shift) width (sum + source)
  let b := intervalAnchorLaw start width (sum + source)
  let u := reciprocalSlice modulus boundary lower (sum - shift)
  let v := reciprocalSlice modulus boundary lower sum
  have heq : weightedIntegerWindow modulus boundary lower start source width (sum - shift) -
      weightedIntegerWindow modulus boundary lower start source width sum = (a - b) * u + b * (u - v) := by
    unfold weightedIntegerWindow
    dsimp [a, b, u, v]
    rw [intervalAnchorLaw_translate]
    have harg : sum + source - shift = sum - shift + source := by omega
    rw [harg]
    ring
  rw [heq]
  have hu0 := reciprocalSlice_nonneg modulus boundary lower hlower (sum - shift)
  have hu := reciprocalSlice_le modulus boundary lower hlower (sum - shift)
  have hdiff := reciprocalSlice_lipschitz modulus boundary lower hlower (sum - shift) sum
  have harg : |((sum - shift : ℤ) : ℝ) - sum| = |(shift : ℝ)| := by push_cast; ring_nf; rw [abs_neg]
  rw [harg] at hdiff
  have husq : u ^ 2 ≤ 1 / lower ^ 2 := by
    have hh := mul_le_mul hu hu hu0 (inv_nonneg.mpr hlower.le)
    simpa only [← sq, inv_pow, one_div] using hh
  have hdiffsq : (u - v) ^ 2 ≤ (shift : ℝ) ^ 2 / lower ^ 4 := by
    change |u - v| ≤ |(shift : ℝ)| / lower ^ 2 at hdiff
    calc
      _ = |u - v| ^ 2 := (sq_abs _).symm
      _ ≤ (|(shift : ℝ)| / lower ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
      _ = _ := by rw [div_pow, sq_abs]; ring
  have h1 := mul_le_mul_of_nonneg_left husq (sq_nonneg (a - b))
  have h2 := mul_le_mul_of_nonneg_left hdiffsq (sq_nonneg b)
  have hsq := sq_nonneg ((a - b) * u - b * (u - v))
  change _ ≤ 2 / lower ^ 2 * (a - b) ^ 2 + 2 * (shift : ℝ) ^ 2 / lower ^ 4 * b ^ 2
  calc
    _ ≤ 2 * ((a - b) * u) ^ 2 + 2 * (b * (u - v)) ^ 2 := by nlinarith only [hsq]
    _ = 2 * ((a - b) ^ 2 * u ^ 2) + 2 * (b ^ 2 * (u - v) ^ 2) := by ring
    _ ≤ 2 * ((a - b) ^ 2 * (1 / lower ^ 2)) + 2 * (b ^ 2 * ((shift : ℝ) ^ 2 / lower ^ 4)) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by ring

/-- Finite injective sampling of an integer window costs at most its full
counting energy 1/width. -/
theorem finite_window_square_le {ι : Type*} [Fintype ι] (colors : ι → ℤ)
    (hinj : Function.Injective colors) (start : ℤ) (width : ℕ) :
    (∑ color, intervalAnchorLaw start width (colors color) ^ 2) ≤ 1 / (width : ℝ) := by
  have hh := finitePalette_sum_le_support colors hinj (anchorInterval start width)
    (fun color => intervalAnchorLaw start width color ^ 2) (fun _ => sq_nonneg _)
    (fun color hout => by simp [intervalAnchorLaw, hout])
  exact hh.trans_eq (by
    have hsum : (∑ output ∈ anchorInterval start width, intervalAnchorLaw start width output ^ 2) =
        (width : ℝ) * ((width : ℝ)⁻¹) ^ 2 := by
      calc
        _ = ∑ _output ∈ anchorInterval start width, ((width : ℝ)⁻¹) ^ 2 := by
          apply Finset.sum_congr rfl
          intro output ho
          simp only [intervalAnchorLaw, if_pos ho]
        _ = _ := by simp only [Finset.sum_const, anchorInterval_card, nsmul_eq_mul]
    rw [hsum]
    by_cases hw : (width : ℝ) = 0
    · simp [hw]
    · field_simp)

/-- Full finite row bound for the genuine window-with-denominator kernel.
The first term is the window-edge cost and the second is the exact
reciprocal variation; neither introduces a palette factor. -/
theorem weightedIntegerWindow_translation_square_le {ι : Type*} [Fintype ι]
    (colors : ι → ℤ) (hinj : Function.Injective colors)
    (modulus boundary lower : ℝ) (hlower : 0 < lower) (start source shift : ℤ) (width : ℕ) :
    (∑ color, (weightedIntegerWindow modulus boundary lower start source width (colors color - shift) -
      weightedIntegerWindow modulus boundary lower start source width (colors color)) ^ 2) ≤
      4 * (shift.natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) +
        2 * (shift : ℝ) ^ 2 / (lower ^ 4 * width) := by
  have hinj' : Function.Injective (fun color => colors color + source) := by intro a b h; apply hinj; exact add_right_cancel h
  have hwindow := finitePalette_sum_le_support (fun color => colors color + source) hinj'
    (anchorInterval start width ∪ anchorInterval (start + shift) width)
    (fun color => (intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color) ^ 2)
    (fun _ => sq_nonneg _) (fun color hout => by rw [anchorTranslation_zero_outside _ _ _ _ hout]; simp)
  have hw := hwindow.trans (anchorTranslationSquare_le start shift width)
  have hbase := finite_window_square_le (fun color => colors color + source) hinj' start width
  calc
    _ ≤ ∑ color, ((2 / lower ^ 2) *
        (intervalAnchorLaw (start + shift) width (colors color + source) - intervalAnchorLaw start width (colors color + source)) ^ 2 +
      (2 * (shift : ℝ) ^ 2 / lower ^ 4) * intervalAnchorLaw start width (colors color + source) ^ 2) :=
      Finset.sum_le_sum fun color _ => weightedIntegerWindow_difference_square modulus boundary lower hlower start source shift (colors color) width
    _ = (2 / lower ^ 2) * (∑ color,
        (intervalAnchorLaw (start + shift) width (colors color + source) - intervalAnchorLaw start width (colors color + source)) ^ 2) +
      (2 * (shift : ℝ) ^ 2 / lower ^ 4) * (∑ color, intervalAnchorLaw start width (colors color + source) ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (2 / lower ^ 2) * (2 * (shift.natAbs : ℝ) / (width : ℝ) ^ 2) +
      (2 * (shift : ℝ) ^ 2 / lower ^ 4) * (1 / (width : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hw (by positivity)) (mul_le_mul_of_nonneg_left hbase (by positivity))
    _ = _ := by ring

/-- On its physical window, the extended kernel is exactly the original
integer-sum endpoint law with the true endpoint mask. -/
theorem averagedPair_eq_weightedIntegerWindow (modulus : ℕ) (boundary start source shiftBound cutoff : ℤ)
    (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hsource : |source| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff)
    (first second : Fin modulus) :
    averagedPair modulus boundary start source width first second =
      if boundary ≤ (first.val : ℤ) ∧ (first.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary ∧
          boundary ≤ (second.val : ℤ) ∧ (second.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary then
        weightedIntegerWindow modulus boundary lower start source width
          ((first.val : ℤ) + second.val - ((modulus : ℤ) - 1)) else 0 := by
  rw [averagedPair_formula]
  let total : ℤ := (first.val : ℤ) + second.val - ((modulus : ℤ) - 1)
  have hmask : (first.val : ℤ) ∈ slice modulus boundary total ↔
      boundary ≤ (first.val : ℤ) ∧ (first.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary ∧
        boundary ≤ (second.val : ℤ) ∧ (second.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary := by
    rw [mem_slice]
    dsimp [total]
    omega
  by_cases hwindow : total + source ∈ anchorInterval start width
  · have hshift : |total| ≤ shiftBound + cutoff := by
      have hh := hstarts (total + source) hwindow
      have htriangle := abs_sub (total + source) source
      simp only [add_sub_cancel_right] at htriangle
      linarith
    have hden : lower ≤ (modulus : ℝ) - 2 * boundary - |(total : ℝ)| := by
      have hshift' : |(total : ℝ)| ≤ (shiftBound : ℝ) + cutoff := by exact_mod_cast hshift
      linarith
    have hdenInt : 0 ≤ (modulus : ℤ) - 2 * boundary - |total| := by
      have hh : (0 : ℝ) < (modulus : ℝ) - 2 * boundary - |(total : ℝ)| := hlower.trans_le hden
      have hh' : (0 : ℤ) < (modulus : ℤ) - 2 * boundary - |total| := by exact_mod_cast hh
      omega
    have hcard : ((slice modulus boundary total).card : ℝ) = (modulus : ℝ) - 2 * boundary - |(total : ℝ)| := by
      rw [slice_card]
      exact_mod_cast Int.toNat_of_nonneg hdenInt
    change intervalAnchorLaw start width (total + source) * law modulus boundary total first.val = _
    unfold law
    simp only [hmask, hcard]
    split_ifs with hm
    · change intervalAnchorLaw start width (total + source) * _ =
        intervalAnchorLaw start width (total + source) * reciprocalSlice modulus boundary lower total
      rw [reciprocalSlice, max_eq_left hden]
    · simp
  · have hz : intervalAnchorLaw start width (total + source) = 0 := by simp only [intervalAnchorLaw, if_neg hwindow]
    change intervalAnchorLaw start width (total + source) * law modulus boundary total first.val = _
    rw [hz, zero_mul]
    split_ifs
    · change 0 = intervalAnchorLaw start width (total + source) * reciprocalSlice modulus boundary lower total
      rw [hz, zero_mul]
    · rfl

end AFT.TrimmedSlice

end

section







/-! # Exact endpoint-mask strip costs for an integer-window pair translation -/

namespace AFT.TrimmedSlice

open scoped BigOperators symmDiff

/-- Masking an integer window to an actual finite interval in each output. -/
noncomputable def maskedIntegerPair (modulus boundary lower : ℝ) (start source : ℤ) (width : ℕ)
    (coreStart : ℤ) (coreWidth : ℕ) (first second : ℤ) : ℝ :=
  if first ∈ anchorInterval coreStart coreWidth ∧ second ∈ anchorInterval coreStart coreWidth then
    weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋) else 0

/-- Restricting an injective finite palette to the two changed strips
counts at most twice the integer displacement. -/
theorem interval_change_count_le {ι : Type*} [Fintype ι] (colors : ι → ℤ)
    (hinj : Function.Injective colors) (start shift : ℤ) (width : ℕ) :
    (∑ color, if colors color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width then (1 : ℝ) else 0) ≤
      2 * (shift.natAbs : ℝ) := by
  have hh := finitePalette_sum_le_support colors hinj
    (anchorInterval start width ∆ anchorInterval (start + shift) width)
    (fun color => if color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width then (1 : ℝ) else 0)
    (fun _ => by split_ifs <;> norm_num) (fun color hout => by simp only [if_neg hout])
  have hcard : (∑ color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width,
      if color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width then (1 : ℝ) else 0) =
      2 * (min width shift.natAbs : ℝ) := by
    simp [anchorInterval_symmDiff_card]
  rw [hcard] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right width shift.natAbs) (by norm_num))

/-- Row energy of the exact denominator extension. -/
theorem weightedIntegerWindow_square_le {ι : Type*} [Fintype ι] (colors : ι → ℤ)
    (hinj : Function.Injective colors) (modulus boundary lower : ℝ) (hlower : 0 < lower)
    (start source : ℤ) (width : ℕ) :
    (∑ color, weightedIntegerWindow modulus boundary lower start source width (colors color) ^ 2) ≤
      1 / (lower ^ 2 * width) := by
  have hpoint (color : ι) : weightedIntegerWindow modulus boundary lower start source width (colors color) ^ 2 ≤
      (1 / lower ^ 2) * intervalAnchorLaw start width (colors color + source) ^ 2 := by
    have hnonneg := reciprocalSlice_nonneg modulus boundary lower hlower (colors color)
    have hu := reciprocalSlice_le modulus boundary lower hlower (colors color)
    have hh := mul_le_mul hu hu hnonneg (inv_nonneg.mpr hlower.le)
    have hh' : reciprocalSlice modulus boundary lower (colors color) ^ 2 ≤ 1 / lower ^ 2 := by
      simpa only [← sq, inv_pow, one_div] using hh
    unfold weightedIntegerWindow
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right hh' (sq_nonneg _)
  have hinj' : Function.Injective (fun color => colors color + source) := by
    intro a b heq
    exact hinj (add_right_cancel heq)
  calc
    _ ≤ ∑ color, (1 / lower ^ 2) * intervalAnchorLaw start width (colors color + source) ^ 2 :=
      Finset.sum_le_sum fun color _ => hpoint color
    _ = (1 / lower ^ 2) * ∑ color, intervalAnchorLaw start width (colors color + source) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 / lower ^ 2) * (1 / (width : ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_window_square_le _ hinj' start width) (by positivity)
    _ = _ := by ring

 theorem masked_difference_square (a b c d : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    (first second : ℝ) :
    ((if a ∧ b then first else 0) - (if c ∧ d then second else 0)) ^ 2 ≤
      2 * (first - second) ^ 2 +
      2 * (if (a ∧ ¬c) ∨ (c ∧ ¬a) then second ^ 2 else 0) +
      2 * (if (b ∧ ¬d) ∨ (d ∧ ¬b) then second ^ 2 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;>
    simp only [ha, hb, hc, hd, not_true_eq_false, not_false_eq_true, and_self, and_true, and_false,
      or_self, or_false, false_or, if_true, if_false, sub_zero, zero_sub, neg_sq,
      mul_zero, add_zero] <;>
    nlinarith [sq_nonneg (first - 2 * second), sq_nonneg (first - second), sq_nonneg second]

/-- A shifted core mask changes only its actual one-dimensional symmetric
difference strips, in addition to the integer-sum window change. -/
theorem maskedIntegerPair_difference_square (modulus boundary lower : ℝ)
    (start source firstShift secondShift first second coreStart : ℤ) (width coreWidth : ℕ) :
    (maskedIntegerPair modulus boundary lower start source width coreStart coreWidth (first - firstShift) (second - secondShift) -
      maskedIntegerPair modulus boundary lower start source width coreStart coreWidth first second) ^ 2 ≤
      2 * (weightedIntegerWindow modulus boundary lower start source width
        ((first + second - ⌊modulus - 1⌋) - (firstShift + secondShift)) -
        weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋)) ^ 2 +
      2 * (if first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth then
        weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋) ^ 2 else 0) +
      2 * (if second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth then
        weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋) ^ 2 else 0) := by
  have hmem (value shift : ℤ) : value - shift ∈ anchorInterval coreStart coreWidth ↔
      value ∈ anchorInterval (coreStart + shift) coreWidth := by
    simp only [anchorInterval, Finset.mem_Ico]
    omega
  have htotal : first - firstShift + (second - secondShift) - ⌊modulus - 1⌋ =
      first + second - ⌊modulus - 1⌋ - (firstShift + secondShift) := by ring
  unfold maskedIntegerPair
  simp only [hmem, htotal]
  have hh := masked_difference_square
    (first ∈ anchorInterval (coreStart + firstShift) coreWidth) (second ∈ anchorInterval (coreStart + secondShift) coreWidth)
    (first ∈ anchorInterval coreStart coreWidth) (second ∈ anchorInterval coreStart coreWidth)
    (weightedIntegerWindow modulus boundary lower start source width
      (first + second - ⌊modulus - 1⌋ - (firstShift + secondShift)))
    (weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋))
  simpa only [Finset.mem_symmDiff, or_comm] using hh

/-- Both endpoint mask costs use one-fixed row energies. The final bound
contains precisely the physical window-edge, reciprocal-denominator, and
endpoint-strip terms. -/
theorem maskedIntegerPair_translation_square_le {ι : Type*} [Fintype ι]
    (colors : ι → ℤ) (hinj : Function.Injective colors)
    (modulus boundary lower : ℝ) (hlower : 0 < lower) (start source firstShift secondShift coreStart : ℤ)
    (width coreWidth : ℕ) :
    (∑ first, ∑ second,
      (maskedIntegerPair modulus boundary lower start source width coreStart coreWidth
        (colors first - firstShift) (colors second - secondShift) -
      maskedIntegerPair modulus boundary lower start source width coreStart coreWidth (colors first) (colors second)) ^ 2) ≤
      2 * (Fintype.card ι : ℝ) *
        (4 * ((firstShift + secondShift).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) +
          2 * ((firstShift + secondShift : ℤ) : ℝ) ^ 2 / (lower ^ 4 * width)) +
      4 * ((firstShift.natAbs : ℝ) + secondShift.natAbs) / (lower ^ 2 * width) := by
  let window (first second : ι) :=
    weightedIntegerWindow modulus boundary lower start source width (colors first + colors second - ⌊modulus - 1⌋)
  have hinjrow (first : ι) : Function.Injective (fun second => colors first + colors second - ⌊modulus - 1⌋) := by
    intro a b heq
    exact hinj (add_left_cancel (sub_left_inj.mp heq))
  have hinjcol (second : ι) : Function.Injective (fun first => colors first + colors second - ⌊modulus - 1⌋) := by
    intro a b heq
    exact hinj (add_right_cancel (sub_left_inj.mp heq))
  have hrows (first : ι) : (∑ second, window first second ^ 2) ≤ 1 / (lower ^ 2 * width) :=
    weightedIntegerWindow_square_le _ (hinjrow first) modulus boundary lower hlower start source width
  have hcols (second : ι) : (∑ first, window first second ^ 2) ≤ 1 / (lower ^ 2 * width) :=
    weightedIntegerWindow_square_le _ (hinjcol second) modulus boundary lower hlower start source width
  have hfirst : (∑ first, ∑ second, if colors first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth
      then window first second ^ 2 else 0) ≤ 2 * (firstShift.natAbs : ℝ) / (lower ^ 2 * width) := by
    calc
      _ ≤ ∑ first, if colors first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth
          then 1 / (lower ^ 2 * width) else 0 := by
        apply Finset.sum_le_sum
        intro first _
        split_ifs <;> simp_all only [Finset.sum_const_zero, le_refl]
      _ = (∑ first, if colors first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth then (1 : ℝ) else 0) /
          (lower ^ 2 * width) := by simp only [Finset.sum_div, ite_div, zero_div, one_div]
      _ ≤ _ := div_le_div_of_nonneg_right (interval_change_count_le colors hinj coreStart firstShift coreWidth) (by positivity)
  have hsecond : (∑ first, ∑ second, if colors second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth
      then window first second ^ 2 else 0) ≤ 2 * (secondShift.natAbs : ℝ) / (lower ^ 2 * width) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ second, if colors second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth
          then 1 / (lower ^ 2 * width) else 0 := by
        apply Finset.sum_le_sum
        intro second _
        split_ifs <;> simp_all only [Finset.sum_const_zero, le_refl]
      _ = (∑ second, if colors second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth then (1 : ℝ) else 0) /
          (lower ^ 2 * width) := by simp only [Finset.sum_div, ite_div, zero_div, one_div]
      _ ≤ _ := div_le_div_of_nonneg_right (interval_change_count_le colors hinj coreStart secondShift coreWidth) (by positivity)
  have hwindow : (∑ first, ∑ second,
      (weightedIntegerWindow modulus boundary lower start source width
        ((colors first + colors second - ⌊modulus - 1⌋) - (firstShift + secondShift)) - window first second) ^ 2) ≤
      (Fintype.card ι : ℝ) *
        (4 * ((firstShift + secondShift).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) +
          2 * ((firstShift + secondShift : ℤ) : ℝ) ^ 2 / (lower ^ 4 * width)) := by
    calc
      _ ≤ ∑ _first : ι, (4 * ((firstShift + secondShift).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) +
          2 * ((firstShift + secondShift : ℤ) : ℝ) ^ 2 / (lower ^ 4 * width)) :=
        Finset.sum_le_sum fun first _ => weightedIntegerWindow_translation_square_le _ (hinjrow first)
          modulus boundary lower hlower start source (firstShift + secondShift) width
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ ≤ ∑ first, ∑ second,
        (2 * (weightedIntegerWindow modulus boundary lower start source width
          ((colors first + colors second - ⌊modulus - 1⌋) - (firstShift + secondShift)) - window first second) ^ 2 +
        2 * (if colors first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth then window first second ^ 2 else 0) +
        2 * (if colors second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth then window first second ^ 2 else 0)) :=
      Finset.sum_le_sum fun first _ => Finset.sum_le_sum fun second _ =>
        maskedIntegerPair_difference_square modulus boundary lower start source firstShift secondShift (colors first) (colors second) coreStart width coreWidth
    _ ≤ _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hh := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hwindow (by norm_num : (0 : ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 2)))
        (mul_le_mul_of_nonneg_left hsecond (by norm_num : (0 : ℝ) ≤ 2))
      exact hh.trans_eq (by ring)

end AFT.TrimmedSlice

end

section



namespace AFT
end AFT
namespace AFT.FiniteConcentration
end AFT.FiniteConcentration


/-! # Exponential-square concentration for genuine independent Hilbert sums -/

namespace AFT.FiniteConcentration

open scoped BigOperators Classical

noncomputable section

variable {Color Hilbert : Type*} [Fintype Color]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

def vectorMean (law : FiniteDist Color) (value : Color → Hilbert) : Hilbert :=
  ∑ color, law.weight color • value color











end

end AFT.FiniteConcentration

end

section









namespace AFT
end AFT
namespace AFT.FiniteConcentration
end AFT.FiniteConcentration
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.condition
end AFT.FiniteDist.condition
namespace AFT.LocalTensors
end AFT.LocalTensors



/-! # Exact Hilbert vectors of physical color profiles -/

namespace AFT

open scoped BigOperators Classical

noncomputable section

namespace FiniteConcentration

variable {Sample Hilbert : Type*} [Fintype Sample]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

theorem vectorMean_norm_le (law : FiniteDist Sample) (value : Sample → Hilbert)
    (bound : ℝ) (hvalue : ∀ sample, ‖value sample‖ ≤ bound) : ‖vectorMean law value‖ ≤ bound := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ sample, law.weight sample * bound := by
      apply Finset.sum_le_sum
      intro sample _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (law.nonneg sample)]
      exact mul_le_mul_of_nonneg_left (hvalue sample) (law.nonneg sample)
    _ = _ := by rw [← Finset.sum_mul, law.sum_one, one_mul]





end FiniteConcentration

namespace ProfileHilbert

variable {Color Sample : Type*} [Fintype Color] [Fintype Sample]

/-- Whitening is a literal linear map into the finite Euclidean space. -/
def whiten (reference : Color → ℝ) : (Color → ℝ) →ₗ[ℝ] EuclideanSpace ℝ Color where
  toFun profile := WithLp.toLp 2 (fun color => profile color / Real.sqrt (reference color))
  map_add' first second := by ext color; simp [add_div]
  map_smul' scalar profile := by ext color; simp [mul_div_assoc]

omit [Fintype Sample] in
@[simp] theorem whiten_apply (reference profile : Color → ℝ) (color : Color) :
    (whiten reference profile).ofLp color = profile color / Real.sqrt (reference color) := rfl

omit [Fintype Sample] in
/-- Its norm is precisely the weighted profile energy. -/
theorem whiten_norm_sq (reference profile : Color → ℝ) (href : ∀ color, 0 ≤ reference color) :
    ‖whiten reference profile‖ ^ 2 = profileSquareNorm reference profile := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [whiten_apply, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (href _)]
  rfl

/-- Averaging arbitrary joint-source profile vectors retains their Hilbert
bound without a palette-cardinality factor. -/
theorem whiten_average (reference : Color → ℝ) (law : FiniteDist Sample) (profile : Sample → Color → ℝ) :
    whiten reference (fun color => law.expectation (fun sample => profile sample color)) =
      FiniteConcentration.vectorMean law (fun sample => whiten reference (profile sample)) := by
  have hh : (fun color => law.expectation (fun sample => profile sample color)) =
      ∑ sample, law.weight sample • profile sample := by
    funext color
    simp only [FiniteDist.expectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hh, map_sum]
  simp only [map_smul, FiniteConcentration.vectorMean]

/-- Centered mixture profiles are the exact average of the centered
component vectors. -/
theorem whiten_mixture_centered (reference : FiniteDist Color) (law : FiniteDist Sample)
    (component : Sample → FiniteDist Color) :
    whiten reference.weight (fun color => (law.mix component).weight color - reference.weight color) =
      FiniteConcentration.vectorMean law (fun sample => whiten reference.weight
        (fun color => (component sample).weight color - reference.weight color)) := by
  rw [← whiten_average]
  congr 1
  funext color
  simp only [FiniteDist.expectation, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    law.sum_one, one_mul, FiniteDist.mix_weight]

end ProfileHilbert

end

end AFT

end

section










namespace AFT
end AFT
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap




/-! # Exact physical triple marginals and their first coefficient energy -/

namespace AFT.PhysicalBlockTensors

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.PhysicalBlockTensors.instDecidableEqFin_aFT_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {Source Color : Type*} [Fintype Source] [Fintype Color]















end

end AFT.PhysicalBlockTensors

end

section







namespace AFT
end AFT
namespace AFT.Fock
end AFT.Fock
namespace AFT.Fock.response
end AFT.Fock.response
namespace AFT.Fock.tensorResponse
end AFT.Fock.tensorResponse
namespace AFT.TaggedFock
end AFT.TaggedFock



/-! # Full coefficient and tail bounds for actual independent finite output blocks -/

namespace AFT
namespace BlockProducts

open scoped BigOperators Classical

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

/-- The exact product mass on all physical output positions, with one
independent finite law per block and arbitrary dependence within each block. -/
noncomputable def blockMass (law : (index : Index) → FiniteDist (Slots index → Color))
    (word : Sigma Slots → Color) : ℝ :=
  ∏ index, (law index).weight (fun slot => word ⟨index, slot⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The actual independent block mass sums to one. -/
theorem blockMass_sum (law : (index : Index) → FiniteDist (Slots index → Color)) :
    (∑ word, blockMass Slots law word) = 1 := by
  letI : DecidableEq (Sigma Slots) := Classical.decEq _
  have hequiv := (Equiv.piCurry (fun index (_ : Slots index) => Color)).sum_comp
    (fun word => ∏ index, (law index).weight (word index))
  have hmass : (∑ word : (index : Index) → Slots index → Color,
      ∏ index, (law index).weight (word index)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [FiniteDist.sum_one, Finset.prod_const_one]
  apply Eq.trans ?_ (hequiv.trans hmass)
  unfold blockMass
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

/-- The complete finite output law of independent physical blocks. -/
noncomputable def blockLaw (law : (index : Index) → FiniteDist (Slots index → Color)) :
    FiniteDist (Sigma Slots → Color) where
  weight := blockMass Slots law
  nonneg _ := Finset.prod_nonneg fun index _ => (law index).nonneg _
  sum_one := blockMass_sum Slots law



/-- The actual homogeneous tensor of one physical block. -/
noncomputable def localCoefficient (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (index : Index) (degree : ℕ) :=
  LocalTensors.degreeTensor (fun _ : Slots index => reference) (law index).weight degree

/-- Actual normalized first coefficient for each block. -/
noncomputable def normalizedLinear (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ) (index : Index) (color : Color) : ℝ :=
  scale * localCoefficient Slots reference law index 1 (fun _ => color)

/-- Actual normalized second coefficient for each block. -/
noncomputable def normalizedQuadratic (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ)
    (index : Index) (word : Fin 2 → Color) : ℝ :=
  scale ^ 2 * localCoefficient Slots reference law index 2 word

/-- Actual normalized third coefficient for each block. -/
noncomputable def normalizedCubic (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ)
    (index : Index) (word : Fin 3 → Color) : ℝ :=
  scale ^ 3 * localCoefficient Slots reference law index 3 word







end BlockProducts
end AFT

end

section





/-! # Explicit numberings of block roots, endpoints and edges

These are arithmetic sum/product encodings; no chosen finite enumeration
is part of the runtime representation.
-/
namespace AFT

 def blockNumbering (legs rest : ℕ) : (Fin legs⊕Fin rest)≃Fin (legs+rest) := finSumFinEquiv

 abbrev blockSlotsProgram (legs rest : ℕ) (index : Fin legs⊕Fin rest) :=
  Fin (Sum.elim (fun _ => 3) (fun _ => 1) index)

 def blockVertexSplit (legs rest : ℕ) :
    (Sigma (blockSlotsProgram legs rest))≃
      ((Fin legs×Fin 3)⊕(Fin rest×Fin 1)) where
  toFun point := match point with
    | ⟨.inl leg,slot⟩ => .inl (leg,slot)
    | ⟨.inr body,slot⟩ => .inr (body,slot)
  invFun point := match point with
    | .inl (leg,slot) => ⟨.inl leg,slot⟩
    | .inr (body,slot) => ⟨.inr body,slot⟩
  left_inv point := by rcases point with ⟨leg|body,slot⟩ <;> rfl
  right_inv point := by rcases point with ⟨leg,slot⟩|⟨body,slot⟩ <;> rfl

 def blockVertexNumbering (legs rest : ℕ) :
    (Sigma (blockSlotsProgram legs rest))≃
      Fin (legs*3+rest) :=
  (blockVertexSplit legs rest).trans
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by omega))))

 

end AFT

end

section




namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap


/-! # Actual V7 reference probabilities with legal small-parameter fallbacks -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

/-- A finite probability with specified weights whenever those weights are
nonnegative and normalized. The fallback is used only outside that domain. -/
def probabilityOr {Color : Type*} [Fintype Color] (profile : Color → ℝ)
    (fallback : FiniteDist Color) : FiniteDist Color :=
  if h : (∀ color, 0 ≤ profile color) ∧ (∑ color, profile color) = 1 then
    ⟨profile, h.1, h.2⟩ else fallback



def actualPrimaryLaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  probabilityOr (actualPrimary cutoffScale parameter beta) (actualCoreLaw parameter)

def actualBodyLaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  probabilityOr (actualBodyCenter cutoffScale parameter beta) (actualCoreLaw parameter)





end

end AFT.V7Calibration

end

section


















namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture





/-! # The actual V7 independent blocks at a fixed root word and queue -/

namespace AFT

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.instDecidableEqFin_aFT (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance _root_.AFT.instDecidableEqSum_aFT {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

namespace LocalTensors



end LocalTensors

namespace V7Calibration

open Filter GaussianSource
open scoped Topology







/-- Each leg owns one attached body and two endpoints; every other body is
its own single-output block. -/
abbrev blockIndex (parameter : ℕ) := Fin (Parameters.legs parameter) ⊕ Fin (Parameters.bodies parameter - Parameters.legs parameter)

instance blockIndexFintype (parameter : ℕ) : Fintype (blockIndex parameter) := inferInstanceAs (Fintype (_ ⊕ _))

abbrev blockSlots (parameter : ℕ) (index : blockIndex parameter) :=
  Fin (match index with | .inl _ => 3 | .inr _ => 1)

instance blockSlotsFintype (parameter : ℕ) (index : blockIndex parameter) : Fintype (blockSlots parameter index) := by
  exact inferInstanceAs (Fintype (Fin _))

theorem blockIndex_card (parameter : ℕ) : Fintype.card (blockIndex parameter) = Parameters.bodies parameter := by
  have hh := Parameters.legs_le_half_bodies parameter
  simp only [blockIndex, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Explicit leg-first arithmetic numbering of the actual body roots. -/
def blockIndexNumbering (parameter : ℕ) : blockIndex parameter ≃ Fin (Parameters.bodies parameter) :=
  (blockNumbering (Parameters.legs parameter) (Parameters.bodies parameter-Parameters.legs parameter)).trans
    (finCongr (by have := Parameters.legs_le_half_bodies parameter;omega))











end V7Calibration
end
end AFT

end

section







/-! # Public permutation placements and a single shared queue

All positions use the same realized queue value. Only the selected public
positions receive it. The one-position marginal is derived from the exact
uniform permutation law; no independence of different positions is asserted.
-/

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Position Sample : Type*} [Fintype Position] [DecidableEq Position] [Nonempty Position]
  [Fintype Sample]





omit [Fintype Sample] in
/-- A public mask is moved by a single random permutation. -/
def permutationMask (selected : Finset Position) (permutation : Equiv.Perm Position) : Finset Position :=
  selected.map permutation.symm.toEmbedding

omit [Fintype Sample] [Fintype Position] [DecidableEq Position] [Nonempty Position] in
@[simp] theorem permutationMask_mem (selected : Finset Position) (permutation : Equiv.Perm Position)
    (position : Position) : position ∈ permutationMask selected permutation ↔ permutation position ∈ selected := by
  simp [permutationMask]

omit [Fintype Sample] [Fintype Position] [DecidableEq Position] [Nonempty Position] in
@[simp] theorem permutationMask_card (selected : Finset Position) (permutation : Equiv.Perm Position) :
    (permutationMask selected permutation).card = selected.card := Finset.card_map _










end
end AFT.FiniteDist

end

section












/-! # Actual public placement of the shared V7 queue -/

namespace AFT.GaussianSource

open scoped BigOperators Classical
open V7Calibration FiniteDist

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem modulus_le_bodies (parameter : ℕ) : Parameters.modulus parameter ≤ Parameters.bodies parameter := by
  have hb : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  have hh := (body_rates_le_quarter parameter).2.trans (by norm_num : (1 : ℝ) / 4 ≤ 1)
  unfold queueRate at hh
  exact_mod_cast (div_le_one hb).mp hh

/-- A fixed mask of exactly q body indices, subsequently moved by a uniform
public permutation independently of the single hidden queue draw. -/
def actualQueueSelection (parameter : ℕ) : Finset (blockIndex parameter) :=
  Finset.univ.map ((Fin.castLEEmb (modulus_le_bodies parameter)).trans
    (blockIndexNumbering parameter).symm.toEmbedding)

@[simp] theorem actualQueueSelection_card (parameter : ℕ) :
    (actualQueueSelection parameter).card = Parameters.modulus parameter := by
  simp only [actualQueueSelection, Finset.card_map, Finset.card_univ, Fintype.card_fin]











end
end AFT.GaussianSource

end

section




















namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BlockProducts
end AFT.BlockProducts
namespace AFT.BlockProducts.normalizedLinear
end AFT.BlockProducts.normalizedLinear
namespace AFT.FiniteConcentration
end AFT.FiniteConcentration
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.sharedQueueShift
end AFT.FiniteDist.sharedQueueShift
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBlockBodyLaw
end AFT.V7Calibration.actualBlockBodyLaw
namespace AFT.V7Calibration.actualBlockBodyLaw.match_1
end AFT.V7Calibration.actualBlockBodyLaw.match_1
namespace AFT.V7Calibration.actualBlockBodyVector
end AFT.V7Calibration.actualBlockBodyVector
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualRootValue
end AFT.V7Calibration.actualRootValue
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile





/-! # Exact centering of the physical normalized block mean -/

namespace AFT.V7Calibration

open Filter GaussianSource FiniteConcentration
open scoped BigOperators Classical Topology

noncomputable section

local instance actualNormalizedMeanFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualNormalizedMeanSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def actualRootWord (parameter : ℕ) := Fin (Parameters.bodies parameter) → Window (v7RootCutoff parameter)

instance actualRootWordFintype (parameter : ℕ) : Fintype (actualRootWord parameter) := inferInstanceAs (Fintype (_ → _))















end

end AFT.V7Calibration

end

section





/-!
# The integer beta identity in the calibrated reference

The beta mixture in V7, Lemma `accuracy-beta-reference`, is a genuine
integral identity, not an assumed closeness property.  The lemmas here prove
its integer-parameter integral from mathlib's Gamma/Beta integral.
-/
namespace AFT
namespace BetaReference

open MeasureTheory

/-- The elementary integer beta integral, with no analytic estimates assumed. -/
theorem integer_beta_integral (m n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, x ^ m * (1 - x) ^ n) =
      (m.factorial : ℝ) * n.factorial / (m + n + 1).factorial := by
  have hc : (∫ x : ℝ in (0 : ℝ)..1,
      (x : ℂ) ^ m * (1 - (x : ℂ)) ^ n) =
      (m.factorial : ℂ) * n.factorial / (m + n + 1).factorial := by
    have h := Complex.betaIntegral_eq_Gamma_mul_div
      ((m : ℂ) + 1) ((n : ℂ) + 1) (by simp; positivity) (by simp; positivity)
    simp only [Complex.betaIntegral, add_sub_cancel_right,
      Complex.cpow_natCast, Complex.Gamma_nat_eq_factorial] at h
    convert h using 1
    congr 2
    rw [show (m : ℂ) + 1 + ((n : ℂ) + 1) = ((m + n + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  have hr : Complex.ofReal (∫ x : ℝ in (0 : ℝ)..1,
      x ^ m * (1 - x) ^ n) =
      ((m.factorial : ℝ) * n.factorial / (m + n + 1).factorial : ℝ) := by
    rw [← intervalIntegral.integral_ofReal]
    simpa using hc
  exact Complex.ofReal_injective hr



/-- The polynomial density of `Beta(K + 1, n + 1)` on `[0,1]`. -/
noncomputable def density (K n : ℕ) (x : ℝ) : ℝ :=
  ((K + n + 1).factorial : ℝ) / (K.factorial * n.factorial) *
    x ^ K * (1 - x) ^ n







/-- The beta density is normalized on the unit interval. -/
theorem density_integral_one (K n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, density K n x) = 1 := by
  have heq : density K n = fun x : ℝ =>
      (((K + n + 1).factorial : ℝ) / (K.factorial * n.factorial)) *
      (x ^ K * (1 - x) ^ n) := by funext x; unfold density; ring
  rw [heq, intervalIntegral.integral_const_mul _ (fun x : ℝ => x ^ K * (1 - x) ^ n),
    integer_beta_integral]
  have hK : (K.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr K.factorial_ne_zero
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hN : ((K + n + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (K + n + 1).factorial_ne_zero
  field_simp































end BetaReference
end AFT

end

section





/-!
# Concrete finite convolution operators and palette-independent Hilbert bounds
-/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def kernelL1 (kernel : G → ℝ) : ℝ := ∑ shift, |kernel shift|
noncomputable def countingL2 (profile : G → ℝ) : ℝ := Real.sqrt (∑ color, profile color ^ 2)

noncomputable def convolution (kernel : G → ℝ) : Module.End ℝ (G → ℝ) where
  toFun profile output := ∑ shift, kernel shift * profile (output - shift)
  map_add' first second := by ext output; simp [mul_add, Finset.sum_add_distrib]
  map_smul' scalar profile := by ext output; simp [← Finset.mul_sum, mul_left_comm]

@[simp] theorem convolution_apply (kernel profile : G → ℝ) (output : G) :
    convolution kernel profile output = ∑ shift, kernel shift * profile (output - shift) := rfl

omit [AddCommGroup G] in
theorem kernelL1_nonneg (kernel : G → ℝ) : 0 ≤ kernelL1 kernel :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [AddCommGroup G] in
theorem countingL2_nonneg (profile : G → ℝ) : 0 ≤ countingL2 profile := Real.sqrt_nonneg _

omit [AddCommGroup G] in
theorem countingL2_add (first second : G → ℝ) :
    countingL2 (first + second) ≤ countingL2 first + countingL2 second := by
  simpa only [countingL2, profileSquareNorm, div_one] using
    profileSquareNorm_sqrt_add_le (fun _ : G => (1 : ℝ)) first second (by intro; norm_num)

omit [AddCommGroup G] in
theorem countingL2_smul (scalar : ℝ) (profile : G → ℝ) :
    countingL2 (scalar • profile) = |scalar| * countingL2 profile := by
  unfold countingL2
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
    Real.sqrt_mul (sq_nonneg scalar), Real.sqrt_sq_eq_abs]

omit [AddCommGroup G] in
theorem countingL2_neg (profile : G → ℝ) : countingL2 (-profile) = countingL2 profile := by
  simp only [countingL2, Pi.neg_apply, neg_sq]

theorem translated_sum (profile : G → ℝ) (shift : G) :
    (∑ color, profile (color - shift)) = ∑ color, profile color :=
  Equiv.sum_comp (Equiv.subRight shift) profile



/-- Signed Young inequality proved from the actual finite kernel entries. -/
theorem convolution_square_le (kernel profile : G → ℝ) :
    (∑ color, convolution kernel profile color ^ 2) ≤ kernelL1 kernel ^ 2 * ∑ color, profile color ^ 2 := by
  have hpoint (color : G) : convolution kernel profile color ^ 2 ≤
      kernelL1 kernel * ∑ shift, |kernel shift| * profile (color - shift) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro shift _
      exact abs_nonneg _
    · intro shift _
      exact mul_nonneg (abs_nonneg _) (sq_nonneg _)
    · intro shift _
      rw [mul_pow]
      nlinarith [sq_abs (kernel shift)]
  calc
    _ ≤ ∑ color, kernelL1 kernel * ∑ shift, |kernel shift| * profile (color - shift) ^ 2 :=
      Finset.sum_le_sum fun color _ => hpoint color
    _ = kernelL1 kernel * ∑ shift, |kernel shift| * ∑ color, profile (color - shift) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp_rw [translated_sum (fun color => profile color ^ 2)]
      rw [← Finset.sum_mul]
      dsimp [kernelL1]
      ring

theorem convolution_L2_le (kernel profile : G → ℝ) :
    countingL2 (convolution kernel profile) ≤ kernelL1 kernel * countingL2 profile := by
  exact (Real.sqrt_le_sqrt (convolution_square_le kernel profile)).trans_eq (by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (kernelL1_nonneg kernel)]
    rfl)

theorem probability_convolution_L2_le (source : FiniteDist G) (profile : G → ℝ) :
    countingL2 (convolution source.weight profile) ≤ countingL2 profile := by
  have hmass : kernelL1 source.weight = 1 := by simp only [kernelL1, abs_of_nonneg (source.nonneg _), source.sum_one]
  simpa only [hmass, one_mul] using convolution_L2_le source.weight profile











end AFT.SafeConvolution

end

section






namespace AFT
end AFT
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.intervalDistribution
end AFT.SafeConvolution.intervalDistribution
namespace AFT.SafeConvolution.intervalKernel
end AFT.SafeConvolution.intervalKernel
namespace AFT.SafeConvolution.pushIntegerKernel
end AFT.SafeConvolution.pushIntegerKernel
namespace AFT.finiteCorrection
end AFT.finiteCorrection


/-! # Finite compactly smoothed root inverse with its exact residual -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G σ : Type*} [Fintype G] [AddCommGroup G] [Fintype σ]



omit [AddCommGroup G] in
theorem operator_power_L2_le (operator : Module.End ℝ (G → ℝ)) (bound : ℝ) (hbound : 0 ≤ bound)
    (hoperator : ∀ profile, countingL2 (operator profile) ≤ bound * countingL2 profile)
    (order : ℕ) (profile : G → ℝ) :
    countingL2 ((operator ^ order) profile) ≤ bound ^ order * countingL2 profile := by
  induction order with
  | zero => simp
  | succ order ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (hoperator _).trans ((mul_le_mul_of_nonneg_left ih hbound).trans_eq (by ring))



theorem probability_power_L2_le (source : FiniteDist G) (order : ℕ) (profile : G → ℝ) :
    countingL2 ((convolution source.weight ^ order) profile) ≤ countingL2 profile := by
  simpa only [one_pow, one_mul] using operator_power_L2_le (convolution source.weight) 1 (by norm_num)
    (fun profile => by simpa only [one_mul] using probability_convolution_L2_le source profile) order profile







variable [DecidableEq G]



end AFT.SafeConvolution

end

section





/-! # Exact canonicality under the finite smoothing and Neumann operators -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Both true signed marginals vanish. -/
def PairCanonical (profile : G × G → ℝ) : Prop :=
  (∀ first, ∑ second, profile (first, second) = 0) ∧
  (∀ second, ∑ first, profile (first, second) = 0)

theorem convolution_pairCanonical (kernel profile : G × G → ℝ) (h : PairCanonical profile) :
    PairCanonical (convolution kernel profile) := by
  constructor
  · intro first
    simp only [convolution_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro shift _
    rw [← Finset.mul_sum]
    change kernel shift * (∑ second, profile (first - shift.1, second - shift.2)) = 0
    rw [translated_sum (fun second => profile (first - shift.1, second)), h.1, mul_zero]
  · intro second
    simp only [convolution_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro shift _
    rw [← Finset.mul_sum]
    change kernel shift * (∑ first, profile (first - shift.1, second - shift.2)) = 0
    rw [translated_sum (fun first => profile (first, second - shift.2)), h.2, mul_zero]

omit [AddCommGroup G] in
theorem PairCanonical.sub {first second : G × G → ℝ} (ha : PairCanonical first) (hb : PairCanonical second) :
    PairCanonical (first - second) := by
  constructor
  · intro color; simp only [Pi.sub_apply, Finset.sum_sub_distrib, ha.1, hb.1, sub_self]
  · intro color; simp only [Pi.sub_apply, Finset.sum_sub_distrib, ha.2, hb.2, sub_self]







end AFT.SafeConvolution

end

section










/-! # Exact Hilbert contraction of the real core-supported canonical seed -/

namespace AFT.SafePair

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def centerOnCore (core : Finset ι) (profile : ι → ℝ) (color : ι) : ℝ :=
  profile color - uniformFiniteProfile core color * ∑ x, profile x



/-- Core centering is the genuine orthogonal projection in counting L2,
including its exact energy decrement. -/
theorem centerOnCore_square (core : Finset ι) (profile : ι → ℝ) (hne : core.Nonempty)
    (hsupport : ∀ color, color ∉ core → profile color = 0) :
    (∑ color, centerOnCore core profile color ^ 2) =
      (∑ color, profile color ^ 2) - (∑ color, profile color) ^ 2 / core.card := by
  have hcross (color : ι) : profile color * uniformFiniteProfile core color = profile color / core.card := by
    by_cases hc : color ∈ core <;> simp [uniformFiniteProfile, hc, hsupport, div_eq_mul_inv]
  have hrefsquare (color : ι) : uniformFiniteProfile core color ^ 2 = uniformFiniteProfile core color / core.card := by
    by_cases hc : color ∈ core <;> simp [uniformFiniteProfile, hc]
    ring
  unfold centerOnCore
  simp only [sub_sq, mul_pow, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hmiddle : (∑ color, 2 * profile color * (uniformFiniteProfile core color * ∑ x, profile x)) =
      2 * (∑ x, profile x) * ((∑ color, profile color) / core.card) := by
    simp_rw [show ∀ color, 2 * profile color * (uniformFiniteProfile core color * ∑ x, profile x) =
      (2 * ∑ x, profile x) * (profile color * uniformFiniteProfile core color) by intro; ring]
    rw [← Finset.mul_sum]
    simp only [hcross, ← Finset.sum_div]
  rw [hmiddle]
  simp only [hrefsquare, ← Finset.sum_mul, ← Finset.sum_div, uniformFiniteProfile_mass core hne]
  ring

theorem centerOnCore_square_le (core : Finset ι) (profile : ι → ℝ) (hne : core.Nonempty)
    (hsupport : ∀ color, color ∉ core → profile color = 0) :
    (∑ color, centerOnCore core profile color ^ 2) ≤ ∑ color, profile color ^ 2 := by
  rw [centerOnCore_square core profile hne hsupport]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

theorem coreSeed_eq_centers (core : Finset ι) (mass : ι → ι → ℝ) (first second : ι) :
    coreSeed core mass first second =
      centerOnCore core (fun x => centerOnCore core (restrictPair core mass x) second) first := by
  simp only [coreSeed, canonicalPair, centerOnCore, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun x y => restrictPair core mass x y)]
  ring

/-- Restricting the true pair and canonicalizing on its core loses no
counting-L2 energy. No independent-product approximation is introduced. -/
theorem coreSeed_square_le (core : Finset ι) (mass : ι → ι → ℝ) (hne : core.Nonempty) :
    (∑ first, ∑ second, coreSeed core mass first second ^ 2) ≤ ∑ first, ∑ second, mass first second ^ 2 := by
  have hcolumn (second : ι) :
      (∑ first, coreSeed core mass first second ^ 2) ≤
        ∑ first, centerOnCore core (restrictPair core mass first) second ^ 2 := by
    simp_rw [coreSeed_eq_centers]
    apply centerOnCore_square_le core _ hne
    intro color hout
    simp [centerOnCore, restrictPair, hout]
  calc
    _ = ∑ second, ∑ first, coreSeed core mass first second ^ 2 := Finset.sum_comm
    _ ≤ ∑ second, ∑ first, centerOnCore core (restrictPair core mass first) second ^ 2 :=
      Finset.sum_le_sum fun second _ => hcolumn second
    _ = ∑ first, ∑ second, centerOnCore core (restrictPair core mass first) second ^ 2 := Finset.sum_comm
    _ ≤ ∑ first, ∑ second, restrictPair core mass first second ^ 2 := by
      apply Finset.sum_le_sum
      intro first _
      exact centerOnCore_square_le core _ hne (by intro color hout; simp [restrictPair, hout])
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      unfold restrictPair
      split_ifs <;> simp [sq_nonneg]

end AFT.SafePair

end

section








/-! # Exact cost of changing the canonical core reference to the full palette -/

namespace AFT.SafePair

open scoped BigOperators
open SafeConvolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def pairCountingL2 (mass : ι → ι → ℝ) : ℝ := countingL2 (fun color : ι × ι => mass color.1 color.2)

omit [DecidableEq ι] in
theorem pairCountingL2_add (first second : ι → ι → ℝ) :
    pairCountingL2 (first + second) ≤ pairCountingL2 first + pairCountingL2 second :=
  countingL2_add _ _

omit [DecidableEq ι] in
theorem pairCountingL2_neg (mass : ι → ι → ℝ) : pairCountingL2 (-mass) = pairCountingL2 mass := countingL2_neg _

omit [DecidableEq ι] in
theorem pairCountingL2_tensor (first second : ι → ℝ) :
    pairCountingL2 (fun x y => first x * second y) = countingL2 first * countingL2 second := by
  unfold pairCountingL2 countingL2
  rw [Fintype.sum_prod_type]
  simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]

theorem uniformFiniteProfile_square (core : Finset ι) (hne : core.Nonempty) :
    (∑ color, uniformFiniteProfile core color ^ 2) = 1 / (core.card : ℝ) := by
  have hp (color : ι) : uniformFiniteProfile core color ^ 2 = uniformFiniteProfile core color / core.card := by
    by_cases hc : color ∈ core <;> simp [uniformFiniteProfile, hc]
    ring
  simp only [hp, ← Finset.sum_div, uniformFiniteProfile_mass core hne]

/-- The full exact distance between the two actual uniform reference laws. -/
theorem uniformCore_difference_square (core : Finset ι) (hne : core.Nonempty) :
    (∑ color, (uniformFiniteProfile core color - 1 / (Fintype.card ι : ℝ)) ^ 2) =
      1 / (core.card : ℝ) - 1 / (Fintype.card ι : ℝ) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    have hh : 0 < Fintype.card ι := lt_of_lt_of_le (Finset.card_pos.mpr hne) (Finset.card_le_univ core)
    positivity
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [uniformFiniteProfile_square core hne]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, uniformFiniteProfile_mass core hne, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

omit [DecidableEq ι] in
/-- A bounded nonnegative subprobability marginal has counting energy at
most its actual height. -/
theorem nonnegative_countingL2_le (profile : ι → ℝ) (upper : ℝ) (hu : 0 ≤ upper)
    (hp : ∀ color, 0 ≤ profile color) (hb : ∀ color, profile color ≤ upper)
    (hmass : (∑ color, profile color) ≤ 1) : countingL2 profile ≤ Real.sqrt upper := by
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∑ color, upper * profile color := Finset.sum_le_sum fun color _ => by
      nlinarith [mul_le_mul_of_nonneg_right (hb color) (hp color)]
    _ = upper * ∑ color, profile color := by rw [Finset.mul_sum]
    _ ≤ upper := by nlinarith

omit [DecidableEq ι] in
/-- Changing the centering law is a sum of two explicit rank-one profiles,
which keeps the reference-change error separate from the pair edge loss. -/
theorem canonicalPair_reference_difference (firstReference secondReference : ι → ℝ)
    (mass : ι → ι → ℝ) (first second : ι) :
    canonicalPair firstReference mass first second - canonicalPair secondReference mass first second =
      -((firstReference first - secondReference first) *
        ((∑ x, mass x second) - (∑ x, ∑ y, mass x y) * firstReference second)) -
      (((∑ y, mass first y) - (∑ x, ∑ y, mass x y) * secondReference first) *
        (firstReference second - secondReference second)) := by
  unfold canonicalPair
  ring

omit [DecidableEq ι] in
/-- The reference change has a palette-independent Hilbert estimate in
terms of actual marginal heights, total mass, and the two reference laws. -/
theorem canonicalPair_reference_L2_le (firstReference secondReference : ι → ℝ)
    (mass : ι → ι → ℝ) (upper : ℝ) (hu : 0 ≤ upper)
    (hmass : ∀ first second, 0 ≤ mass first second)
    (htotal : (∑ first, ∑ second, mass first second) ≤ 1)
    (hrow : ∀ first, (∑ second, mass first second) ≤ upper)
    (hcolumn : ∀ second, (∑ first, mass first second) ≤ upper) :
    pairCountingL2 (canonicalPair firstReference mass - canonicalPair secondReference mass) ≤
      countingL2 (firstReference - secondReference) *
        (2 * Real.sqrt upper + countingL2 firstReference + countingL2 secondReference) := by
  let total := ∑ first, ∑ second, mass first second
  let row := fun first => ∑ second, mass first second
  let column := fun second => ∑ first, mass first second
  have ht0 : 0 ≤ total := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hmass _ _
  have hr := nonnegative_countingL2_le row upper hu
    (fun _ => Finset.sum_nonneg fun _ _ => hmass _ _) hrow htotal
  have hc := nonnegative_countingL2_le column upper hu
    (fun _ => Finset.sum_nonneg fun _ _ => hmass _ _) hcolumn (by dsimp only [column]; rw [Finset.sum_comm]; exact htotal)
  have hcenter (marginal reference : ι → ℝ) (hm : countingL2 marginal ≤ Real.sqrt upper) :
      countingL2 (marginal - total • reference) ≤ Real.sqrt upper + countingL2 reference := by
    change countingL2 (marginal + -(total • reference)) ≤ _
    have hh := countingL2_add marginal (-(total • reference))
    rw [countingL2_neg, countingL2_smul, abs_of_nonneg ht0] at hh
    have hm' := mul_le_mul_of_nonneg_right htotal (countingL2_nonneg reference)
    exact hh.trans (by dsimp only [total] at *; nlinarith)
  have hfirst := hcenter column firstReference hc
  have hsecond := hcenter row secondReference hr
  have heq : canonicalPair firstReference mass - canonicalPair secondReference mass =
      -(fun x y => (firstReference - secondReference) x * (column - total • firstReference) y) +
      -(fun x y => (row - total • secondReference) x * (firstReference - secondReference) y) := by
    funext first second
    exact canonicalPair_reference_difference firstReference secondReference mass first second
  rw [heq]
  calc
    _ ≤ pairCountingL2 (-(fun x y => (firstReference - secondReference) x * (column - total • firstReference) y)) +
      pairCountingL2 (-(fun x y => (row - total • secondReference) x * (firstReference - secondReference) y)) := pairCountingL2_add _ _
    _ = countingL2 (firstReference - secondReference) * countingL2 (column - total • firstReference) +
      countingL2 (row - total • secondReference) * countingL2 (firstReference - secondReference) := by
      rw [pairCountingL2_neg, pairCountingL2_neg, pairCountingL2_tensor, pairCountingL2_tensor]
    _ ≤ countingL2 (firstReference - secondReference) * (Real.sqrt upper + countingL2 firstReference) +
      (Real.sqrt upper + countingL2 secondReference) * countingL2 (firstReference - secondReference) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (countingL2_nonneg _))
        (mul_le_mul_of_nonneg_right hsecond (countingL2_nonneg _))
    _ = _ := by ring

end AFT.SafePair

end


