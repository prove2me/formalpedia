-- Prove2me | Definitions.Def_InfoLossLAR_NativeSparsePrefix_04
-- name    : InfoLossLAR_NativeSparsePrefix_04
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T13:24:54.218496+00:00
-- url     : https://prove2.me/theorems/e1a1a1e3-14e2-420e-ac92-635c3947fe43
-- title:
--   Mixed kernels, polynomial output, and histogram coordinates
-- statement:
--   This package defines mixed coordinate kernels and iteration, canonical moment and collision indices, finite refresh and contraction patterns, coefficient reindexing, represented and centered polynomials, formal logarithms, and joint pair-output interfaces.
--
--   These interfaces retain actual finite polynomial and channel expressions on which later norm and histogram theorems operate. They expose mathematical data and the supporting constructor APIs; the subsequent response, approximation, and transport bounds are stated as separate theorems. Recorded native operation charges are not by themselves platform machine-time certificates.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; Lean source modules AFT/SmoothingDifference.lean, AFT/CanonicalSmoothing.lean, AFT/CoreWindowKernel.lean, AFT/MixedKernel.lean, AFT/MixedCoordinateOperator.lean, AFT/MixedCoordinateIteration.lean, AFT/MixedTensor.lean, AFT/V7RootSmoothing.lean, AFT/PairErrorAssembly.lean, AFT/PairCoreNumerics.lean, AFT/CanonicalMoments.lean, AFT/CollisionCounting.lean, AFT/CollisionOccurrences.lean, AFT/MixedTransfer.lean, AFT/FiniteRefresh.lean, AFT/CollisionGraph.lean, AFT/GraphScopes.lean, AFT/HistogramNormalization.lean, AFT/SymmetricCoefficients.lean, AFT/ReindexedCoefficients.lean, AFT/CanonicalVariance.lean, AFT/PlacedFibers.lean, AFT/PatternContractions.lean, AFT/ReflectionCalibration.lean, AFT/RepresentedPolynomial.lean, AFT/RepresentedTruncation.lean, AFT/RepresentedQueue.lean, AFT/RepresentedRing.lean, AFT/RepresentedOutput.lean, AFT/MeanOutput.lean, AFT/CenteredPolynomial.lean, AFT/FormalLogarithm.lean, AFT/HistogramGenerating.lean, AFT/MixedCoordinateProducts.lean, AFT/JointPairOutput.lean, AFT/RepresentedControlKernel.lean. Source bodies and declaration spans are recorded in native_sparse_prefix/manifest.json; SHA256 b34f18fb1e86d34cd1ca258efc8b0b519ea5d576a1bbf1e47e2a03d9d12fb63f. Repackaging of identical data declarations, with 4163 public types matched to native source and 7722 origin declarations recursively audited for standard logical axioms only.

import Definitions.Def_InfoLossLAR_NativeSparsePrefix_03

section





/-! # Squared Hilbert error of averaging genuine finite translations -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G]





omit [AddCommGroup G] in
/-- Full finite mixtures of joint profiles obey the same squared bound;
no rank-one decomposition of their output coordinates is used. -/
theorem probability_profile_mixture_square_le {σ : Type*} [Fintype σ]
    (source : FiniteDist σ) (profiles : σ → G → ℝ) :
    (∑ color, (∑ sample, source.weight sample * profiles sample color) ^ 2) ≤
      ∑ sample, source.weight sample * ∑ color, profiles sample color ^ 2 := by
  have hpoint (color : G) : (∑ sample, source.weight sample * profiles sample color) ^ 2 ≤
      ∑ sample, source.weight sample * profiles sample color ^ 2 := by
    have hh : (∑ sample, source.weight sample * profiles sample color) ^ 2 ≤
        (∑ sample, source.weight sample) * ∑ sample, source.weight sample * profiles sample color ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      · intro sample _; exact source.nonneg _
      · intro sample _; exact mul_nonneg (source.nonneg _) (sq_nonneg _)
      · intro sample _; ring
    simpa only [source.sum_one, one_mul] using hh
  calc
    _ ≤ ∑ color, ∑ sample, source.weight sample * profiles sample color ^ 2 :=
      Finset.sum_le_sum fun color _ => hpoint color
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

omit [AddCommGroup G] in
theorem probability_profile_mixture_square_le_uniform {σ : Type*} [Fintype σ]
    (source : FiniteDist σ) (profiles : σ → G → ℝ) (bound : ℝ)
    (hbound : ∀ sample, (∑ color, profiles sample color ^ 2) ≤ bound) :
    (∑ color, (∑ sample, source.weight sample * profiles sample color) ^ 2) ≤ bound := by
  exact (probability_profile_mixture_square_le source profiles).trans (by
    calc
      _ ≤ ∑ sample, source.weight sample * bound :=
        Finset.sum_le_sum fun sample _ => mul_le_mul_of_nonneg_left (hbound sample) (source.nonneg sample)
      _ = _ := by rw [← Finset.sum_mul, source.sum_one, one_mul])



/-- Repeated actual probability smoothing costs only the fixed number of
steps times the proved one-step error. -/
theorem probability_power_error_L2_le (source : FiniteDist G) (profile : G → ℝ) (order : ℕ) :
    countingL2 ((convolution source.weight ^ order) profile - profile) ≤
      order * countingL2 (convolution source.weight profile - profile) := by
  induction order with
  | zero => simp [countingL2]
  | succ order ih =>
    rw [pow_succ', Module.End.mul_apply]
    have heq : convolution source.weight ((convolution source.weight ^ order) profile) - profile =
        convolution source.weight ((convolution source.weight ^ order) profile - profile) +
          (convolution source.weight profile - profile) := by
      rw [map_sub]
      abel
    rw [heq]
    exact (countingL2_add _ _).trans ((add_le_add
      ((probability_convolution_L2_le source _).trans ih) le_rfl).trans_eq (by push_cast; ring))

end AFT.SafeConvolution

end

section










/-! # Uniform canonical projection commutes with actual finite smoothing -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

noncomputable def uniformCanonical : Module.End ℝ (G × G → ℝ) where
  toFun profile color := SafePair.canonicalPair (fun _ : G => 1 / (Fintype.card G : ℝ))
    (fun x y => profile (x, y)) color.1 color.2
  map_add' first second := by
    funext color
    simp only [SafePair.canonicalPair, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' scalar profile := by
    funext color
    simp only [SafePair.canonicalPair, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

omit [AddCommGroup G] [DecidableEq G] in
@[simp] theorem uniformCanonical_apply (profile : G × G → ℝ) (color : G × G) :
    uniformCanonical profile color = SafePair.canonicalPair (fun _ : G => 1 / (Fintype.card G : ℝ))
      (fun x y => profile (x, y)) color.1 color.2 := rfl

omit [DecidableEq G] in
theorem uniformCanonical_translation (profile : G × G → ℝ) (shift : G × G) :
    uniformCanonical (fun color => profile (color - shift)) = fun color => uniformCanonical profile (color - shift) := by
  funext color
  simp only [uniformCanonical_apply, SafePair.canonicalPair]
  have hfirst (second : G) : (∑ first, profile (first - shift.1, second - shift.2)) =
      ∑ first, profile (first, second - shift.2) := translated_sum (fun first => profile (first, second - shift.2)) shift.1
  have hsecond (first : G) : (∑ second, profile (first - shift.1, second - shift.2)) =
      ∑ second, profile (first - shift.1, second) := translated_sum (fun second => profile (first - shift.1, second)) shift.2
  have htotal : (∑ first, ∑ second, profile (first - shift.1, second - shift.2)) =
      ∑ first, ∑ second, profile (first, second) := by
    simp_rw [hsecond]
    exact translated_sum (fun first => ∑ second, profile (first, second)) shift.1
  change profile (color.1 - shift.1, color.2 - shift.2) - 1 / (Fintype.card G : ℝ) *
    (∑ x, profile (x - shift.1, color.2 - shift.2)) -
    (∑ x, profile (color.1 - shift.1, x - shift.2)) * (1 / (Fintype.card G : ℝ)) +
    (∑ x, ∑ y, profile (x - shift.1, y - shift.2)) * (1 / (Fintype.card G : ℝ)) * (1 / (Fintype.card G : ℝ)) = _
  rw [hfirst, hsecond, htotal]
  rfl

omit [DecidableEq G] in
theorem uniformCanonical_commute (kernel : G × G → ℝ) : Commute uniformCanonical (convolution kernel) := by
  apply LinearMap.ext
  intro profile
  funext color
  have hrepr : convolution kernel profile = ∑ shift, kernel shift • (fun point => profile (point - shift)) := by
    funext point
    simp only [convolution_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change uniformCanonical (convolution kernel profile) color = convolution kernel (uniformCanonical profile) color
  rw [hrepr, map_sum]
  simp only [map_smul, uniformCanonical_translation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, convolution_apply]

/-- Uniform canonicalization is the exact counting-Hilbert orthogonal
projection, including for a signed non-product joint profile. -/
theorem uniformCanonical_L2_le (profile : G × G → ℝ) :
    countingL2 (uniformCanonical profile) ≤ countingL2 profile := by
  have hh := SafePair.coreSeed_square_le (Finset.univ : Finset G) (fun x y => profile (x, y)) Finset.univ_nonempty
  simp only [SafePair.coreSeed, SafePair.canonicalPair, SafePair.restrictPair, uniformFiniteProfile, Finset.mem_univ, and_self,
    if_true, Finset.card_univ] at hh
  apply Real.sqrt_le_sqrt
  simpa only [Fintype.sum_prod_type, uniformCanonical_apply, SafePair.canonicalPair, one_div] using hh

/-- The actual smoothed core seed differs from the desired canonical pair
by exactly the core-centering error, the retained smoothing error, and the
deleted edge error. Each is measured before any parameter simplification. -/
theorem smoothed_core_error_L2_le (source : FiniteDist (G × G)) (core : Finset G)
    (mass : G → G → ℝ) (order : ℕ) :
    let original := fun color : G × G => mass color.1 color.2
    let restricted := fun color : G × G => SafePair.restrictPair core mass color.1 color.2
    let seed := fun color : G × G => SafePair.coreSeed core mass color.1 color.2
    countingL2 ((convolution source.weight ^ order) seed - uniformCanonical original) ≤
      countingL2 (seed - uniformCanonical restricted) +
      order * countingL2 (convolution source.weight restricted - restricted) +
      countingL2 (restricted - original) := by
  dsimp only
  let original := fun color : G × G => mass color.1 color.2
  let restricted := fun color : G × G => SafePair.restrictPair core mass color.1 color.2
  let seed := fun color : G × G => SafePair.coreSeed core mass color.1 color.2
  have hc := (uniformCanonical_commute source.weight).pow_right order
  have hcomm : (convolution source.weight ^ order) (uniformCanonical restricted) =
      uniformCanonical ((convolution source.weight ^ order) restricted) := by
    have hh := congrArg (fun operator : Module.End ℝ (G × G → ℝ) => operator restricted) hc.eq
    simpa only [Module.End.mul_apply] using hh.symm
  have heq : (convolution source.weight ^ order) seed - uniformCanonical original =
      (convolution source.weight ^ order) (seed - uniformCanonical restricted) +
      uniformCanonical ((convolution source.weight ^ order) restricted - restricted) +
      uniformCanonical (restricted - original) := by
    simp only [map_sub]
    rw [hcomm]
    abel
  change countingL2 ((convolution source.weight ^ order) seed - uniformCanonical original) ≤ _
  rw [heq]
  exact (countingL2_add _ _).trans ((add_le_add
    ((countingL2_add _ _).trans (add_le_add (probability_power_L2_le source order _)
      ((uniformCanonical_L2_le _).trans (probability_power_error_L2_le source restricted order))))
    (uniformCanonical_L2_le _)))

end AFT.SafeConvolution

end

section










/-! # Identification of the actual restricted pair with its integer core kernel -/

namespace AFT.TrimmedSlice

open scoped BigOperators

/-- The core mask is the original integer palette interval, not a cyclic
window or a replacement endpoint law. -/
theorem core_interval_mem (modulus coreDepth : ℕ) (hcore : 2 * coreDepth ≤ modulus) (color : ℤ) :
    color ∈ anchorInterval coreDepth (modulus - 2 * coreDepth) ↔
      (coreDepth : ℤ) ≤ color ∧ color < (modulus : ℤ) - coreDepth := by
  simp only [anchorInterval, Finset.mem_Ico]
  omega

theorem core_palette_mem (modulus coreDepth : ℕ) (color : Fin modulus) :
    color ∈ paletteSlice modulus coreDepth 0 ↔
      (coreDepth : ℤ) ≤ color.val ∧ (color.val : ℤ) < (modulus : ℤ) - coreDepth := by
  simp only [paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and, slice,
    max_self, min_self, add_zero, Finset.mem_Ico]

/-- Exact equality between the actual core-restricted window pair and the
integer kernel to which the complete translation bound applies. -/
theorem restricted_averagedPair_eq_maskedIntegerPair (modulus coreDepth : ℕ)
    (boundary start source shiftBound cutoff : ℤ) (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hcore : 2 * coreDepth ≤ modulus) (hboundary : boundary ≤ coreDepth)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound) (hsource : |source| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff)
    (first second : Fin modulus) :
    SafePair.restrictPair (paletteSlice modulus coreDepth 0) (averagedPair modulus boundary start source width) first second =
      maskedIntegerPair modulus boundary lower start source width coreDepth (modulus - 2 * coreDepth) first.val second.val := by
  have hfloor : ⌊(modulus : ℝ) - 1⌋ = (modulus : ℤ) - 1 := by
    have heq : (modulus : ℝ) - 1 = ((modulus : ℤ) - 1 : ℤ) := by push_cast; rfl
    rw [heq, Int.floor_intCast]
  unfold SafePair.restrictPair maskedIntegerPair
  simp only [core_palette_mem, core_interval_mem modulus coreDepth hcore, hfloor]
  split_ifs with hc
  · rw [averagedPair_eq_weightedIntegerWindow modulus boundary start source shiftBound cutoff width lower hlower
      hstarts hsource hclear]
    have hmask : boundary ≤ (first.val : ℤ) ∧ (first.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary ∧
        boundary ≤ (second.val : ℤ) ∧ (second.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary := by omega
    rw [if_pos hmask]
  · rfl

end AFT.TrimmedSlice

end

section







/-!
# The full mixed input activity on actual finite kernels

The coordinate rates are `pool⁻¹/²`; allowing a rate for each coordinate
covers both primary and body pools.  Every fixed-coordinate set is included.
The norm is taken on input kernels themselves, without identifying equal
images under an output evaluation map.
-/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def freeze (fixed : Finset Slot) (values integrated : Slot → Color) : Slot → Color :=
  fun slot => if slot ∈ fixed then values slot else integrated slot

def fiberSq (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (fixed : Finset Slot) (values : Slot → Color) : ℝ :=
  (FiniteDist.independent reference).l2Sq fun integrated => kernel (freeze fixed values integrated)

def fiberNorm (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (fixed : Finset Slot) : ℝ :=
  ‖fun values => Real.sqrt (fiberSq reference kernel fixed values)‖

def activity (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) : ℝ :=
  (∏ slot, rate slot) * ∑ fixed : Finset Slot, (∏ slot ∈ fixed, rate slot) *
    fiberNorm reference kernel fixed









@[simp] theorem fiberNorm_zero (reference : Slot → FiniteDist Color) (fixed : Finset Slot) :
    fiberNorm reference (0 : (Slot → Color) → ℝ) fixed = 0 := by
  simp [fiberNorm, fiberSq, FiniteDist.l2Sq, FiniteDist.expectation]
  rfl





@[simp] theorem activity_zero (rate : Slot → ℝ) (reference : Slot → FiniteDist Color) :
    activity rate reference (0 : (Slot → Color) → ℝ) = 0 := by simp [activity]









end

end AFT.MixedKernel

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

@[simp] theorem fiberSq_univ (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (values : Slot → Color) :
    fiberSq reference kernel Finset.univ values = kernel values ^ 2 := by
  have hf (integrated : Slot → Color) : freeze Finset.univ values integrated = values := by
    ext slot
    simp [freeze]
  simp only [fiberSq, FiniteDist.l2Sq, FiniteDist.expectation, hf, ← Finset.sum_mul,
    FiniteDist.sum_one, one_mul]

@[simp] theorem fiberNorm_univ (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) :
    fiberNorm reference kernel Finset.univ = ‖kernel‖ := by
  simp only [fiberNorm, fiberSq_univ, Real.sqrt_sq_eq_abs]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg kernel)).mpr
    intro values
    rw [Real.norm_eq_abs, abs_abs]
    exact norm_le_pi_norm kernel values
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro values
    have h := norm_le_pi_norm (fun values => |kernel values|) values
    simpa only [Real.norm_eq_abs, abs_abs] using h





/-- The empty fixed set is the full integrated L2 fiber. -/
@[simp] theorem fiberSq_empty (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (values : Slot → Color) :
    fiberSq reference kernel ∅ values = (FiniteDist.independent reference).l2Sq kernel := by
  have hf (integrated : Slot → Color) : freeze ∅ values integrated = integrated := by
    ext slot
    simp [freeze]
  simp only [fiberSq, hf]

@[simp] theorem fiberNorm_empty (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) :
    fiberNorm reference kernel ∅ = Real.sqrt ((FiniteDist.independent reference).l2Sq kernel) := by
  haveI : Nonempty (Slot → Color) := by
    by_contra hn
    haveI : IsEmpty (Slot → Color) := not_nonempty_iff.mp hn
    have h := (FiniteDist.independent reference).sum_one
    simp at h
  simp only [fiberNorm, fiberSq_empty, pi_norm_const, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]



end

end AFT.MixedKernel

end

section





/-! # A genuine coordinate operator on every mixed input fiber

The operator acts on the literal joint kernel. Grouping fixed-coordinate
sets in pairs gives a dimension-free bound on the full mixed activity.
-/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color] [DecidableEq Slot]

/-- Apply a profile operator in one actual input coordinate. -/
def partialInputOperator (slot : Slot) (operator : Module.End ℝ (Color → ℝ))
    (primary : Color → ℝ) (kernel : (Slot → Color) → ℝ) : (Slot → Color) → ℝ :=
  fun word => operator (fun input => primary input * kernel (Function.update word slot input))
    (word slot) / primary (word slot)



























end
end AFT.MixedKernel

end

section





/-! # Literal coordinate composition and finite tensor inverse iteration -/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- The actual coordinate operation is linear on the complete joint kernel. -/
def partialInputLinear (slot : Slot) (operator : Module.End ℝ (Color → ℝ))
    (primary : Color → ℝ) : Module.End ℝ ((Slot → Color) → ℝ) where
  toFun := partialInputOperator slot operator primary
  map_add' first second := by
    funext word
    unfold partialInputOperator
    have heq : (fun input => primary input * (first + second) (Function.update word slot input)) =
        (fun input => primary input * first (Function.update word slot input)) +
        (fun input => primary input * second (Function.update word slot input)) := by funext input; simp [mul_add]
    rw [heq, map_add]
    simp only [Pi.add_apply, add_div]
  map_smul' scalar kernel := by
    funext word
    unfold partialInputOperator
    have heq : (fun input => primary input * (scalar • kernel) (Function.update word slot input)) =
        scalar • (fun input => primary input * kernel (Function.update word slot input)) := by funext input; simp [mul_left_comm]
    rw [heq, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, RingHom.id_apply]

omit [Fintype Slot] [Fintype Color] in
@[simp] theorem partialInputOperator_id (slot : Slot) (primary : Color → ℝ)
    (hprimary : ∀ color, primary color ≠ 0) (kernel : (Slot → Color) → ℝ) :
    partialInputOperator slot LinearMap.id primary kernel = kernel := by
  funext word
  simp only [partialInputOperator, LinearMap.id_apply, Function.update_eq_self]
  exact mul_div_cancel_left₀ _ (hprimary _)





/-- A specified ordered finite list retains all coordinate actions literally. -/
def inputIteration (coordinates : List Slot) (operator : Slot → Module.End ℝ (Color → ℝ))
    (reference : Slot → FiniteDist Color) : Module.End ℝ ((Slot → Color) → ℝ) :=
  coordinates.foldr (fun slot accumulated => (partialInputLinear slot (operator slot) (reference slot).weight).comp accumulated)
    LinearMap.id

omit [Fintype Slot] in
@[simp] theorem inputIteration_nil (operator : Slot → Module.End ℝ (Color → ℝ))
    (reference : Slot → FiniteDist Color) : inputIteration [] operator reference = LinearMap.id := rfl

omit [Fintype Slot] in
@[simp] theorem inputIteration_cons (slot : Slot) (coordinates : List Slot)
    (operator : Slot → Module.End ℝ (Color → ℝ)) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) :
    inputIteration (slot :: coordinates) operator reference kernel =
      partialInputOperator slot (operator slot) (reference slot).weight
        (inputIteration coordinates operator reference kernel) := rfl



end
end AFT.MixedKernel

end

section





/-! # Tensor multiplication of the full mixed input activity -/

set_option backward.isDefEq.respectTransparency false

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Left Right Color : Type*} [Fintype Left] [Fintype Right] [Fintype Color]
  [DecidableEq Left] [DecidableEq Right]



omit [Fintype Left] [Fintype Right] [Fintype Color] in
@[simp] theorem freeze_disjSum_left (first : Finset Left) (second : Finset Right)
    (values integrated : Left ⊕ Right → Color) :
    freeze (first.disjSum second) values integrated ∘ Sum.inl =
      freeze first (values ∘ Sum.inl) (integrated ∘ Sum.inl) := by
  ext slot
  simp [freeze]

omit [Fintype Left] [Fintype Right] [Fintype Color] in
@[simp] theorem freeze_disjSum_right (first : Finset Left) (second : Finset Right)
    (values integrated : Left ⊕ Right → Color) :
    freeze (first.disjSum second) values integrated ∘ Sum.inr =
      freeze second (values ∘ Sum.inr) (integrated ∘ Sum.inr) := by
  ext slot
  simp [freeze]







end

end AFT.MixedKernel

end

section







/-! # Finite Neumann smoothing instantiated at the actual V7 root parameters -/

namespace AFT.GaussianSource

open scoped BigOperators Classical
open AFT.SafeConvolution

noncomputable section

local instance actualModulusNeZero (parameter : ℕ) : NeZero (Parameters.modulus parameter) :=
  ⟨(Parameters.modulus_prime parameter).ne_zero⟩

 















end
end AFT.GaussianSource

end

section











namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox




/-! # Complete error of the actual finite safe pair input -/

namespace AFT.SafePair

open scoped BigOperators
open SafeConvolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coreSeed_reference_error_le (core : Finset ι) (hne : core.Nonempty)
    (mass : ι → ι → ℝ) (upper : ℝ) (hu : 0 ≤ upper)
    (hmass : ∀ first second, 0 ≤ mass first second)
    (htotal : (∑ first, ∑ second, mass first second) ≤ 1)
    (hrow : ∀ first, (∑ second, mass first second) ≤ upper)
    (hcolumn : ∀ second, (∑ first, mass first second) ≤ upper) :
    pairCountingL2 (coreSeed core mass - canonicalPair (fun _ => 1 / (Fintype.card ι : ℝ))
      (restrictPair core mass)) ≤
      Real.sqrt (1 / (core.card : ℝ) - 1 / (Fintype.card ι : ℝ)) *
        (2 * Real.sqrt upper + Real.sqrt (1 / (core.card : ℝ)) +
          Real.sqrt (1 / (Fintype.card ι : ℝ))) := by
  have hnonneg (first second : ι) : 0 ≤ restrictPair core mass first second := by
    unfold restrictPair; split_ifs
    · exact hmass first second
    · exact le_rfl
  have hle (first second : ι) : restrictPair core mass first second ≤ mass first second := by
    unfold restrictPair; split_ifs <;> simp_all
  have hh := canonicalPair_reference_L2_le (uniformFiniteProfile core)
    (fun _ => 1 / (Fintype.card ι : ℝ)) (restrictPair core mass) upper hu hnonneg
    ((Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hle x y).trans htotal)
    (fun x => (Finset.sum_le_sum fun y _ => hle x y).trans (hrow x))
    (fun y => (Finset.sum_le_sum fun x _ => hle x y).trans (hcolumn y))
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    have hp := (Finset.card_pos.mpr hne).trans_le (Finset.card_le_univ core)
    positivity
  have hfull : countingL2 (fun _ : ι => 1 / (Fintype.card ι : ℝ)) =
      Real.sqrt (1 / (Fintype.card ι : ℝ)) := by
    unfold countingL2
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hcore : countingL2 (uniformFiniteProfile core) = Real.sqrt (1 / (core.card : ℝ)) := by
    unfold countingL2
    rw [uniformFiniteProfile_square core hne]
  have hdiff : countingL2 (uniformFiniteProfile core - fun _ : ι => 1 / (Fintype.card ι : ℝ)) =
      Real.sqrt (1 / (core.card : ℝ) - 1 / (Fintype.card ι : ℝ)) := by
    unfold countingL2
    simp only [Pi.sub_apply, uniformCore_difference_square core hne]
  simpa only [coreSeed, hcore, hfull, hdiff] using hh

end AFT.SafePair

namespace AFT.GaussianSource

open scoped BigOperators Classical
open SafeConvolution

attribute [local instance] actualModulusNeZero



end AFT.GaussianSource

end

section








/-! # Numerical cost of the true core reference and deleted edges -/

namespace AFT.SafePair

open scoped BigOperators

/-- The change from the core uniform law to the full uniform law has
squared normalized cost proportional to the deleted fraction. -/
theorem core_reference_scaled_square_le (modulus size depth : ℝ)
    (hq : 0 < modulus) (hd : 0 ≤ depth) (hk : modulus / 2 ≤ size)
    (hsize : size = modulus - 2 * depth) :
    (modulus * (Real.sqrt (1 / size - 1 / modulus) *
      (2 * Real.sqrt (2 / modulus) + Real.sqrt (1 / size) + Real.sqrt (1 / modulus)))) ^ 2 ≤
      128 * depth / modulus := by
  have hk0 : 0 < size := lt_of_lt_of_le (half_pos hq) hk
  have hdiff : 0 ≤ 1 / size - 1 / modulus := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le hk0 (by linarith)
  have hsmall : 1 / size ≤ 2 / modulus := by
    apply (div_le_div_iff₀ hk0 hq).mpr
    linarith
  have hone : 1 / modulus ≤ 2 / modulus := by gcongr; norm_num
  have hroot := Real.sqrt_le_sqrt hsmall
  have honeRoot := Real.sqrt_le_sqrt hone
  have hs : 0 ≤ 2 * Real.sqrt (2 / modulus) + Real.sqrt (1 / size) + Real.sqrt (1 / modulus) := by positivity
  have hsum : 2 * Real.sqrt (2 / modulus) + Real.sqrt (1 / size) + Real.sqrt (1 / modulus) ≤
      4 * Real.sqrt (2 / modulus) := by linarith
  have hsum2 := (sq_le_sq₀ hs (by positivity : 0 ≤ 4 * Real.sqrt (2 / modulus))).mpr hsum
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 / modulus)] at hsum2
  have hdiffEq : 1 / size - 1 / modulus = 2 * depth / (size * modulus) := by
    field_simp
    nlinarith
  have hdiffBound : 1 / size - 1 / modulus ≤ 4 * depth / modulus ^ 2 := by
    rw [hdiffEq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ 2 * depth * modulus)]
  rw [mul_pow, mul_pow, Real.sq_sqrt hdiff]
  calc
    _ ≤ modulus ^ 2 * ((4 * depth / modulus ^ 2) * (16 * (2 / modulus))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg modulus)
      exact mul_le_mul hdiffBound (by norm_num at hsum2 ⊢; exact hsum2) (sq_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

end AFT.SafePair

end

section





/-! # Exact finite collision expansion of canonical U-statistic moments -/

namespace AFT
namespace CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color Copy : Type*}
variable [Fintype Slot] [Fintype Pool] [Fintype Color] [Fintype Copy]

/-- Evaluate a genuine joint kernel at distinct sampled pool indices. -/
noncomputable def placedKernel (kernel : (Slot → Color) → ℝ) (placement : Slot ↪ Pool)
    (word : Pool → Color) : ℝ := kernel (word ∘ placement)



/-- The complete product belonging to one labeled moment collision pattern. -/
noncomputable def patternProduct (kernel : (Slot → Color) → ℝ)
    (pattern : Copy → Slot ↪ Pool) (word : Pool → Color) : ℝ :=
  ∏ copy, placedKernel kernel (pattern copy) word







/-- The pool labels actually used by a moment pattern. -/
noncomputable def usedLabels (pattern : Copy → Slot ↪ Pool) : Finset Pool :=
  Finset.univ.image (fun occurrence : Copy × Slot => pattern occurrence.1 occurrence.2)

/-- A surviving pattern has no sample label occurring in only one kernel. -/
def NoSingleton (pattern : Copy → Slot ↪ Pool) : Prop :=
  ∀ copy slot, ∃ otherCopy otherSlot,
    otherCopy ≠ copy ∧ pattern otherCopy otherSlot = pattern copy slot







end CanonicalMoments
end AFT

end

section





/-!
# Counting actual finite collision patterns

A pattern with exactly `used` labels is encoded by an injective enumeration
of those labels and a word on the occurrence positions.  This retains the
falling-factorial pool factor and has no color-alphabet dependence.
-/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

variable {Slot Pool Copy : Type*} [Fintype Slot] [Fintype Pool] [Fintype Copy]

abbrev PatternsWithLabels (used : ℕ) :=
  {pattern : Copy → Slot ↪ Pool // (usedLabels pattern).card = used}

def labelEnumeration (used : ℕ) (pattern : PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used) :
    Fin used ≃ usedLabels pattern.val :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_coe] using pattern.property.symm)

def collisionCode (used : ℕ) (pattern : PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used) :
    (Fin used ↪ Pool) × (Copy × Slot → Fin used) :=
  ((labelEnumeration used pattern).toEmbedding.trans (Function.Embedding.subtype _),
    fun occurrence => (labelEnumeration used pattern).symm
      ⟨pattern.val occurrence.1 occurrence.2,
        Finset.mem_image.mpr ⟨occurrence, Finset.mem_univ _, rfl⟩⟩)

















end

end AFT.CanonicalMoments

end

section





/-! # First, last and middle occurrences in actual finite collision graphs -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

variable {Copy Label : Type*} [Fintype Copy] [LinearOrder Copy] [Fintype Label]

def occurrenceCopies (scope : Copy → Finset Label) (label : Label) : Finset Copy :=
  Finset.univ.filter fun copy => label ∈ scope copy

def middleScopes (scope : Copy → Finset Label) (copy : Copy) : Finset Label :=
  (scope copy).filter fun label =>
    (∃ before, before < copy ∧ label ∈ scope before) ∧
    (∃ after, copy < after ∧ label ∈ scope after)

def scopeUnion (scope : Copy → Finset Label) : Finset Label :=
  Finset.univ.biUnion scope

def NoSingletonScopes (scope : Copy → Finset Label) : Prop :=
  ∀ copy label, label ∈ scope copy → ∃ other, other ≠ copy ∧ label ∈ scope other













end

end AFT.CanonicalMoments

end

section





/-! # Mixed-fiber Hilbert transfers for canonical moment collision graphs -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Ending New Fixed Keep : Type*}
variable [Fintype Ending] [Fintype New] [Fintype Fixed] [Fintype Keep]

omit [Fintype New] [Fintype Fixed] [Fintype Keep] in
/-- Weighted Cauchy--Schwarz in an actual finite probability space. -/
theorem expectation_mul_sq_le (law : FiniteDist Ending) (first second : Ending → ℝ) :
    law.expectation (fun value => first value * second value) ^ 2 ≤ law.l2Sq first * law.l2Sq second := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro value _
    exact mul_nonneg (law.nonneg value) (sq_nonneg _)
  · intro value _
    exact mul_nonneg (law.nonneg value) (sq_nonneg _)
  · intro value _
    ring









end AFT.CanonicalMoments

end

section





/-! # Exact coordinate refresh operators on finite product probability laws -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The actual deterministic finite law. -/
noncomputable def pointLaw (value : Color) : FiniteDist Color where
  weight color := if value = color then 1 else 0
  nonneg color := by split_ifs <;> norm_num
  sum_one := by simp

omit [Fintype Slot] in
@[simp] theorem pointLaw_expectation (value : Color) (function : Color → ℝ) :
    (pointLaw value).expectation function = function value := by
  simp [FiniteDist.expectation, pointLaw]

omit [Fintype Slot] in
@[simp] theorem pointLaw_mix (value : Color) (kernel : Color → FiniteDist Color) :
    (pointLaw value).mix kernel = kernel value := by
  ext color
  simp [FiniteDist.mix_weight, pointLaw]

omit [Fintype Slot] in
@[simp] theorem mix_pointLaw (law : FiniteDist Color) : law.mix pointLaw = law := by
  ext color
  simp [FiniteDist.mix_weight, pointLaw]



/-- Resample precisely the indicated coordinates from their product laws. -/
noncomputable def refreshLaw (reference : Slot → FiniteDist Color) (resampled : Finset Slot)
    (word : Slot → Color) : FiniteDist (Slot → Color) :=
  FiniteDist.independent (fun slot => if slot ∈ resampled then reference slot else pointLaw (word slot))

/-- The concrete partial integration operator. -/
noncomputable def refresh (reference : Slot → FiniteDist Color) (resampled : Finset Slot)
    (function : (Slot → Color) → ℝ) (word : Slot → Color) : ℝ :=
  (refreshLaw reference resampled word).expectation function













omit [Fintype Slot] in
@[simp] theorem map_identity (law : FiniteDist Color) : law.map id = law := by
  ext color
  exact FiniteDist.map_equiv_weight law (Equiv.refl Color) color

omit [Fintype Slot] in
@[simp] theorem map_constant (law : FiniteDist Color) (value : Color) :
    law.map (fun _ => value) = pointLaw value := by
  ext color
  by_cases h : value = color
  · simp [FiniteDist.map_weight, pointLaw, h, law.sum_one]
  · simp [FiniteDist.map_weight, pointLaw, h]









end AFT.CanonicalMoments

end

section




namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments


/-! # The exact transfer chain of a finite joint-kernel collision graph -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Label Color : Type*} [Fintype Label] [Fintype Color]

/-- Coordinate sets that remain active after each actual integration step. -/
noncomputable def graphActive (scope ending : ℕ → Finset Label) : ℕ → Finset Label
  | 0 => ∅
  | index + 1 => (scope index ∪ graphActive scope ending index) \ ending index

/-- Actual partially integrated product of the first kernel copies. -/
noncomputable def graphMessage (reference : Label → FiniteDist Color)
    (ending : ℕ → Finset Label) (kernel : ℕ → (Label → Color) → ℝ) : ℕ → (Label → Color) → ℝ
  | 0 => fun _ => 1
  | index + 1 => refresh reference (ending index)
      (fun word => kernel index word * graphMessage reference ending kernel index word)

/-- Middle occurrences are the coordinates fixed by a graph step. -/
noncomputable def graphFixed (scope ending : ℕ → Finset Label) (index : ℕ) : Finset Label :=
  scope index \ ((scope index \ graphActive scope ending index) ∪ ending index)





/-- The exact unprocessed kernel product. -/
noncomputable def graphSuffix (kernel : ℕ → (Label → Color) → ℝ) (length start : ℕ)
    (word : Label → Color) : ℝ := ∏ index ∈ Finset.Ico start length, kernel index word







end AFT.CanonicalMoments

end

section





/-! # The active and fixed coordinates of the actual ordered collision graph -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Label : Type*} [Fintype Label] {count : ℕ}

/-- Extend a finite copy sequence by empty scopes. -/
noncomputable def scopeAt (scope : Fin count → Finset Label) (index : ℕ) : Finset Label :=
  if h : index < count then scope ⟨index, h⟩ else ∅

/-- Labels appearing strictly before a position. -/
noncomputable def scopePrefix (scope : Fin count → Finset Label) (index : ℕ) : Finset Label :=
  Finset.univ.filter (fun label => ∃ copy : Fin count, copy.val < index ∧ label ∈ scope copy)

/-- Labels appearing at or after a position. -/
noncomputable def scopeSuffix (scope : Fin count → Finset Label) (index : ℕ) : Finset Label :=
  Finset.univ.filter (fun label => ∃ copy : Fin count, index ≤ copy.val ∧ label ∈ scope copy)

/-- Integrate a label exactly at its last occurrence. -/
noncomputable def scopeEnding (scope : Fin count → Finset Label) (index : ℕ) : Finset Label :=
  scopeAt scope index \ scopeSuffix scope (index + 1)











variable {Color : Type*} [Fintype Color]

/-- Extend an actual finite sequence of kernels by zero. -/
noncomputable def kernelAt (kernel : Fin count → (Label → Color) → ℝ) (index : ℕ) : (Label → Color) → ℝ :=
  if h : index < count then kernel ⟨index, h⟩ else fun _ => 0



end AFT.CanonicalMoments

end

section







/-! # Exact finite histogram normalization of actual symmetric coefficients -/

namespace AFT
namespace HistogramNormalization

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- Exchangeability of an actual signed output mass. -/
def ExchangeableMass (mass : (Slot → Color) → ℝ) : Prop :=
  ∀ word (permutation : Equiv.Perm Slot), mass (word ∘ permutation) = mass word

/-- Reindex the complete finite word space by a position permutation. -/
def precomposeEquiv (permutation : Equiv.Perm Slot) : (Slot → Color) ≃ (Slot → Color) where
  toFun word := word ∘ permutation
  invFun word := word ∘ permutation.symm
  left_inv word := by ext slot; simp
  right_inv word := by ext slot; simp



















end HistogramNormalization
end AFT

end

section







namespace AFT
end AFT
namespace AFT.TensorFock
end AFT.TensorFock



/-! # Symmetrization preserves the actual complete coefficient sequence -/

namespace AFT
namespace HistogramNormalization

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The actual signed mass after an independently uniform permutation. -/
noncomputable def symmetrizedMass (mass : (Slot → Color) → ℝ) : (Slot → Color) → ℝ :=
  BlockFock.symmetrize mass

















end HistogramNormalization
end AFT

end

section







/-! # Renaming physical output positions preserves all constructed coefficients -/

namespace AFT
namespace HistogramNormalization

open scoped BigOperators Classical

variable {Slot OtherSlot Color : Type*}
variable [Fintype Slot] [Fintype OtherSlot] [Fintype Color]

/-- Rename the actual finite word's physical position type. -/
def renameWord (equiv : Slot ≃ OtherSlot) : (Slot → Color) ≃ (OtherSlot → Color) where
  toFun word := word ∘ equiv.symm
  invFun word := word ∘ equiv
  left_inv word := by ext slot; simp
  right_inv word := by ext slot; simp

/-- The signed mass of a renamed physical law. -/
noncomputable def renamedMass (equiv : Slot ≃ OtherSlot) (mass : (Slot → Color) → ℝ)
    (word : OtherSlot → Color) : ℝ := mass (word ∘ equiv)







end HistogramNormalization
end AFT

end

section










/-! # Exact finite-pool variance for actual canonical subset statistics -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]









set_option backward.isDefEq.respectTransparency false in
/-- Renaming independent, identically distributed coordinates preserves the
actual finite expectation, including its weights. -/
theorem independent_equiv_expectation (equiv : Slot ≃ Pool) (reference : FiniteDist Color)
    (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent (fun _ : Pool => reference)).expectation
      (fun word => function (word ∘ equiv)) =
      (FiniteDist.independent (fun _ : Slot => reference)).expectation function := by
  have h := (HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word => (∏ slot, reference.weight (word slot)) * function word)
  unfold FiniteDist.expectation FiniteDist.independent
  apply Eq.trans ?_ h
  apply Finset.sum_congr (by ext; simp)
  intro word _
  change (∏ slot, reference.weight (word slot)) * function (word ∘ equiv) =
    (∏ slot, reference.weight ((word ∘ equiv) slot)) * function (word ∘ equiv)
  congr 1
  exact (equiv.prod_comp (fun slot => reference.weight (word slot))).symm







end AFT.CanonicalMoments

end

section








/-! # Actual mixed fibers of a distinct-index placement -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]

/-- The actual injective placement identifies its slot set with its image. -/
noncomputable def placementEquiv (placement : Slot ↪ Pool) : Slot ≃ (Finset.univ.map placement) :=
  Equiv.ofBijective (fun slot => ⟨placement slot, Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, rfl⟩⟩) (by
    constructor
    · intro first second heq
      exact placement.injective (congrArg Subtype.val heq)
    · intro label
      obtain ⟨slot, _, heq⟩ := Finset.mem_map.mp label.property
      exact ⟨slot, Subtype.ext heq⟩)

/-- Every finite injective subword has exactly the original independent law. -/
theorem independent_embedding_expectation (reference : FiniteDist Color) (placement : Slot ↪ Pool)
    (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent (fun _ : Pool => reference)).expectation (fun word => function (word ∘ placement)) =
      (FiniteDist.independent (fun _ : Slot => reference)).expectation function := by
  have hr := LocalTensors.independent_restriction_expectation
    (fun _ : Pool => reference) (Finset.univ.map placement)
      (fun word => function (word ∘ placementEquiv placement))
  have he := independent_equiv_expectation (placementEquiv placement) reference function
  apply Eq.trans ?_ (hr.trans ?_)
  · rfl
  · apply Eq.trans ?_ he
    unfold FiniteDist.expectation FiniteDist.independent
    apply Finset.sum_congr (by ext; simp)
    intro word _
    rfl

/-- Pull a set of fixed pool labels back to genuine kernel arguments. -/
noncomputable def placementFixed (placement : Slot ↪ Pool) (fixed : Finset Pool) : Finset Slot :=
  Finset.univ.filter (fun slot => placement slot ∈ fixed)





end AFT.CanonicalMoments

end

section












/-! # Actual arbitrary-joint-kernel collision contractions in mixed activity -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color] {power : ℕ}

/-- The exact scope of each actual distinct-index copy. -/
noncomputable def patternScopes (pattern : Fin power → Slot ↪ Pool) : Fin power → Finset Pool :=
  fun copy => Finset.univ.map (pattern copy)

/-- The original kernel arguments fixed at the middle occurrences of a pattern. -/
noncomputable def patternFixed (pattern : Fin power → Slot ↪ Pool) (copy : Fin power) : Finset Slot :=
  placementFixed (pattern copy) (middleScopes (patternScopes pattern) copy)















end AFT.CanonicalMoments

end

section





/-!
# Reflection symmetry of the actual calibrated primary law
-/

namespace AFT

open scoped BigOperators

namespace TrimmedSlice

def reflectedStart (start : ℤ) (width : ℕ) : ℤ := -start - width + 1













end TrimmedSlice

namespace V7Calibration













end V7Calibration
end AFT

end

section





namespace AFT
end AFT
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.QueueNormalization
end AFT.QueueNormalization
namespace AFT.QueueNormalization.average
end AFT.QueueNormalization.average
namespace AFT.QueueNormalization.averageUnit
end AFT.QueueNormalization.averageUnit
namespace AFT.QueueNormalization.finiteExp
end AFT.QueueNormalization.finiteExp
namespace AFT.finiteCorrection
end AFT.finiteCorrection



/-!
# Finite polynomials in specified input seeds

Different seed labels remain different formal variables even when their
leading output tensors agree.  The activity is the coefficient L1 sum
weighted by the product of the actual seed activities.  This is an upper
bound for the fully expanded, symmetrized input representation by
`MixedTensor` and `MixedSymmetry`; no quotient by output tensors is used.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*}

abbrev Table (Seed : Type*) := MvPolynomial Seed ℝ

def monomialWeight (weight : Seed → ℝ) (powers : Seed →₀ ℕ) : ℝ :=
  powers.prod fun seed power => weight seed ^ power

def activity (weight : Seed → ℝ) (table : Table Seed) : ℝ :=
  (AddMonoidAlgebra.coeff table).sum fun powers coefficient => |coefficient| * monomialWeight weight powers



@[simp] theorem monomialWeight_zero (weight : Seed → ℝ) : monomialWeight weight 0 = 1 := by
  simp [monomialWeight]





@[simp] theorem activity_zero (weight : Seed → ℝ) : activity weight (0 : Table Seed) = 0 := by
  simp [activity, MvPolynomial.sum_def]

@[simp] theorem activity_monomial (weight : Seed → ℝ) (powers : Seed →₀ ℕ) (coefficient : ℝ) :
    activity weight (MvPolynomial.monomial powers coefficient) = |coefficient| * monomialWeight weight powers :=
  MvPolynomial.sum_monomial_eq (by simp)

@[simp] theorem activity_one (weight : Seed → ℝ) : activity weight (1 : Table Seed) = 1 := by
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply, activity_monomial, monomialWeight_zero]
  norm_num







/-- A seed's polynomial variable carries precisely its supplied activity. -/
@[simp] theorem activity_X (weight : Seed → ℝ) (seed : Seed) :
    activity weight (MvPolynomial.X seed : Table Seed) = weight seed := by
  simp [MvPolynomial.X, activity_monomial, monomialWeight, Finsupp.prod_single_index]

end

end AFT.RepresentedPolynomial

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed Color : Type*} [Fintype Color]

/-- The literal primary/body input table, before output evaluation. -/
structure InputSeed (Color : Type*) where
  primaryOrder : ℕ
  bodyOrder : ℕ
  kernel : (Fin (primaryOrder + bodyOrder) → Color) → ℝ

def inputReference (primary body : FiniteDist Color) (seed : InputSeed Color) :
    Fin (seed.primaryOrder + seed.bodyOrder) → FiniteDist Color :=
  Fin.addCases (fun _ => primary) (fun _ => body)







omit [Fintype Color] in
@[simp] theorem activity_C (weight : Seed → ℝ) (scalar : ℝ) :
    activity weight (MvPolynomial.C scalar : Table Seed) = |scalar| := by
  rw [MvPolynomial.C_apply, activity_monomial, monomialWeight_zero, mul_one]

omit [Fintype Color] in
@[simp] theorem activity_neg (weight : Seed → ℝ) (table : Table Seed) :
    activity weight (-table) = activity weight table := by
  simp only [activity, MvPolynomial.sum_def, MvPolynomial.support_neg,
    MvPolynomial.coeff_neg, abs_neg]











end

end AFT.RepresentedPolynomial

end

section





/-!
# Weighted truncation of literal input seed polynomials

The cutoff acts on the sum of the primary and body input orders.  Formal
seed labels remain distinct.  Finite Neumann inversion is exact after this
cutoff, with its activity controlled before and after truncation.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*}

def weightedOrder (order : Seed → ℕ) (powers : Seed →₀ ℕ) : ℕ :=
  powers.sum fun seed power => power * order seed

@[simp] theorem weightedOrder_zero (order : Seed → ℕ) : weightedOrder order 0 = 0 := by
  simp [weightedOrder]

theorem weightedOrder_add (order : Seed → ℕ) (first second : Seed →₀ ℕ) :
    weightedOrder order (first + second) = weightedOrder order first + weightedOrder order second :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

def truncate (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed) : Table Seed :=
  AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun powers => weightedOrder order powers ≤ cutoff) (AddMonoidAlgebra.coeff table))

@[simp] theorem coeff_truncate (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed)
    (powers : Seed →₀ ℕ) :
    MvPolynomial.coeff powers (truncate order cutoff table) =
      if weightedOrder order powers ≤ cutoff then MvPolynomial.coeff powers table else 0 := rfl

@[simp] theorem truncate_zero (order : Seed → ℕ) (cutoff : ℕ) :
    truncate order cutoff (0 : Table Seed) = 0 := by
  ext powers
  simp

@[simp] theorem truncate_one (order : Seed → ℕ) (cutoff : ℕ) :
    truncate order cutoff (1 : Table Seed) = 1 := by
  ext powers
  by_cases h : powers = 0
  · subst powers; simp
  · simp [MvPolynomial.coeff_one, Ne.symm h]

theorem truncate_add (order : Seed → ℕ) (cutoff : ℕ) (first second : Table Seed) :
    truncate order cutoff (first + second) = truncate order cutoff first + truncate order cutoff second := by
  ext powers
  simp only [coeff_truncate, MvPolynomial.coeff_add]
  split_ifs <;> simp





@[simp] theorem truncate_idempotent (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed) :
    truncate order cutoff (truncate order cutoff table) = truncate order cutoff table := by
  ext powers
  simp only [coeff_truncate]
  split_ifs <;> rfl

theorem truncate_mul (order : Seed → ℕ) (cutoff : ℕ) (first second : Table Seed) :
    truncate order cutoff (first * second) =
      truncate order cutoff (truncate order cutoff first * truncate order cutoff second) := by
  ext powers
  simp only [coeff_truncate]
  split_ifs with h
  · simp only [MvPolynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro pair hpair
    have heq := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
    have hsum : weightedOrder order pair.1 + weightedOrder order pair.2 ≤ cutoff := by
      rw [← weightedOrder_add, heq]
      exact h
    rw [coeff_truncate, coeff_truncate, if_pos (by omega), if_pos (by omega)]
  · rfl



/-- Every coefficient strictly below the specified weighted order vanishes. -/
def HasOrder (order : Seed → ℕ) (minimum : ℕ) (table : Table Seed) : Prop :=
  ∀ powers, weightedOrder order powers < minimum → MvPolynomial.coeff powers table = 0

theorem hasOrder_zero (order : Seed → ℕ) (table : Table Seed) : HasOrder order 0 table := by
  intro powers h
  omega



theorem hasOrder_mul (order : Seed → ℕ) (firstOrder secondOrder : ℕ)
    (first second : Table Seed) (hfirst : HasOrder order firstOrder first)
    (hsecond : HasOrder order secondOrder second) :
    HasOrder order (firstOrder + secondOrder) (first * second) := by
  intro powers hp
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro pair hpair
  have heq := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
  have hsum : weightedOrder order pair.1 + weightedOrder order pair.2 < firstOrder + secondOrder := by
    rw [← weightedOrder_add, heq]
    exact hp
  by_cases h : weightedOrder order pair.1 < firstOrder
  · rw [hfirst _ h, zero_mul]
  · rw [hsecond _ (by omega), mul_zero]









end

end AFT.RepresentedPolynomial

end

section





/-!
# Shared-queue normalization in the explicit input polynomial algebra

The average, exponential and finite reciprocal are concrete finite
polynomials.  Exactness is checked coefficient by coefficient through the
specified input-order cutoff; the activity estimates use the actual seed
weights, with no normed-algebra instance supplied as an assumption.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed Queue : Type*} [Fintype Queue]

omit [Fintype Queue] in
theorem hasOrder_sum {Tag : Type*} (order : Seed → ℕ) (minimum : ℕ)
    (tables : Tag → Table Seed) (tags : Finset Tag)
    (h : ∀ tag ∈ tags, HasOrder order minimum (tables tag)) :
    HasOrder order minimum (∑ tag ∈ tags, tables tag) := by
  intro powers hp
  exact (MvPolynomial.coeff_sum tags tables powers).trans
    (Finset.sum_eq_zero fun tag ht => h tag ht powers hp)

omit [Fintype Queue] in
theorem hasOrder_mono (order : Seed → ℕ) (first second : ℕ) (table : Table Seed)
    (h : HasOrder order second table) (hle : first ≤ second) : HasOrder order first table :=
  fun powers hp => h powers (hp.trans_le hle)



def queueAverage (queue : FiniteDist Queue) (tables : Queue → Table Seed) : Table Seed :=
  ∑ value, MvPolynomial.C (queue.weight value) * tables value





@[simp] theorem queueAverage_const (queue : FiniteDist Queue) (table : Table Seed) :
    queueAverage queue (fun _ => table) = table := by
  simp only [queueAverage, ← Finset.sum_mul, ← map_sum, queue.sum_one, map_one, one_mul]



























end

end AFT.RepresentedPolynomial

end

section





/-!
# The actual quotient ring of specified input seed polynomials

Only coefficients above the input-order cutoff are identified.  In
particular, equality of output images is never a quotient relation here.
-/

set_option backward.isDefEq.respectTransparency false

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*}

def cutoffIdeal (order : Seed → ℕ) (cutoff : ℕ) : Ideal (Table Seed) where
  carrier := {table | HasOrder order (cutoff + 1) table}
  zero_mem' := by intro powers _; simp
  add_mem' := by
    intro first second hfirst hsecond powers hp
    simp only [MvPolynomial.coeff_add, hfirst powers hp, hsecond powers hp, add_zero]
  smul_mem' := by
    intro scalar table htable
    change HasOrder order (cutoff + 1) (scalar * table)
    simpa only [zero_add] using
      hasOrder_mul order 0 (cutoff + 1) scalar table (hasOrder_zero order scalar) htable

abbrev CutoffRing (order : Seed → ℕ) (cutoff : ℕ) := (Table Seed) ⧸ cutoffIdeal order cutoff

def quotientMap (order : Seed → ℕ) (cutoff : ℕ) : Table Seed →+* CutoffRing order cutoff :=
  Ideal.Quotient.mk (cutoffIdeal order cutoff)







@[simp] theorem quotient_C (order : Seed → ℕ) (cutoff : ℕ) (scalar : ℝ) :
    quotientMap order cutoff (MvPolynomial.C scalar) = algebraMap ℝ (CutoffRing order cutoff) scalar := rfl






end

end AFT.RepresentedPolynomial

end

section







/-!
# Generating polynomials of literal input seed tables

Every channel is an actual signed finite transition table.  Substitution
into the seed polynomial is an algebra homomorphism; its product is the
joint generating polynomial on disjoint output slots.  Equal output
images do not identify distinct input representations.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Color Output Seed : Type*} [Fintype Color] [Fintype Output]

def channelForm (channel : Color → Output → ℝ) (input : Color) : MvPolynomial Output ℝ :=
  ∑ output, MvPolynomial.C (channel input output) * MvPolynomial.X output

def seedChannel (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    Fin (seed.primaryOrder + seed.bodyOrder) → Color → Output → ℝ :=
  Fin.addCases (fun _ => primaryChannel) (fun _ => bodyChannel)

def seedOutput (primary body : FiniteDist Color) (primaryChannel bodyChannel : Color → Output → ℝ)
    (seed : InputSeed Color) : MvPolynomial Output ℝ :=
  ∑ word : Fin (seed.primaryOrder + seed.bodyOrder) → Color,
    MvPolynomial.C (seed.kernel word * ∏ slot, (inputReference primary body seed slot).weight (word slot)) *
      ∏ slot, channelForm (seedChannel primaryChannel bodyChannel seed slot) (word slot)

/-- The represented input map uses all joint kernel entries, with their
actual product-reference weights. It does not factor a joint kernel. -/
def outputHom (primary body : FiniteDist Color) (primaryChannel bodyChannel : Color → Output → ℝ) :
    Table (InputSeed Color) →ₐ[ℝ] MvPolynomial Output ℝ :=
  MvPolynomial.aeval (seedOutput primary body primaryChannel bodyChannel)

@[simp] theorem outputHom_X (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    outputHom primary body primaryChannel bodyChannel (MvPolynomial.X seed) =
      seedOutput primary body primaryChannel bodyChannel seed := MvPolynomial.aeval_X _ _

omit [Fintype Color] in
theorem channelForm_homogeneous (channel : Color → Output → ℝ) (input : Color) :
    (channelForm channel input).IsHomogeneous 1 :=
  MvPolynomial.IsHomogeneous.sum _ _ _ (fun _ _ => MvPolynomial.isHomogeneous_C_mul_X _ _)

theorem seedOutput_homogeneous (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    (seedOutput primary body primaryChannel bodyChannel seed).IsHomogeneous
      (seed.primaryOrder + seed.bodyOrder) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro word _
  apply MvPolynomial.IsHomogeneous.C_mul
  convert MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun slot => channelForm (seedChannel primaryChannel bodyChannel seed slot) (word slot))
    (fun _ => 1) (fun slot _ => channelForm_homogeneous _ _) using 1
  simp







omit [Fintype Color] [Fintype Output] in
theorem homogeneous_hasOrder (degree : ℕ) (table : Table Output)
    (h : table.IsHomogeneous degree) : HasOrder (fun _ => 1) degree table := by
  intro powers hp
  apply h.coeff_eq_zero
  change powers.sum (fun _ power => power) ≠ degree
  simpa only [weightedOrder, mul_one] using ne_of_lt hp

omit [Fintype Color] [Fintype Output] in
theorem aeval_monomial_homogeneous (order : Seed → ℕ)
    (images : Seed → MvPolynomial Output ℝ)
    (himages : ∀ seed, (images seed).IsHomogeneous (order seed))
    (powers : Seed →₀ ℕ) (coefficient : ℝ) :
    (MvPolynomial.aeval images (MvPolynomial.monomial powers coefficient)).IsHomogeneous
      (weightedOrder order powers) := by
  rw [MvPolynomial.aeval_monomial]
  change (MvPolynomial.C coefficient * _).IsHomogeneous _
  apply MvPolynomial.IsHomogeneous.C_mul
  unfold Finsupp.prod weightedOrder Finsupp.sum
  apply MvPolynomial.IsHomogeneous.prod
  intro seed _
  simpa only [mul_comm] using (himages seed).pow (powers seed)

omit [Fintype Color] [Fintype Output] in
theorem aeval_hasOrder (order : Seed → ℕ) (images : Seed → MvPolynomial Output ℝ)
    (himages : ∀ seed, (images seed).IsHomogeneous (order seed))
    (minimum : ℕ) (table : Table Seed) (h : HasOrder order minimum table) :
    HasOrder (fun _ => 1) minimum (MvPolynomial.aeval images table) := by
  conv in MvPolynomial.aeval images table => rw [MvPolynomial.as_sum table]
  rw [map_sum]
  apply hasOrder_sum
  intro powers hp
  have hmin : minimum ≤ weightedOrder order powers := by
    by_contra hlt
    exact (MvPolynomial.mem_support_iff.mp hp) (h powers (by omega))
  exact hasOrder_mono _ _ _ _
    (homogeneous_hasOrder _ _ (aeval_monomial_homogeneous order images himages powers _)) hmin

theorem outputHom_hasOrder (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ)
    (minimum : ℕ) (table : Table (InputSeed Color))
    (h : HasOrder (fun seed => seed.primaryOrder + seed.bodyOrder) minimum table) :
    HasOrder (fun _ => 1) minimum (outputHom primary body primaryChannel bodyChannel table) :=
  aeval_hasOrder _ _ (seedOutput_homogeneous primary body primaryChannel bodyChannel) _ _ h

/-- Degree preservation makes the same map well-defined on the two actual
cutoff rings, while retaining all distinctions in the input ring. -/
def outputQuotient (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (cutoff : ℕ) :
    CutoffRing (fun seed : InputSeed Color => seed.primaryOrder + seed.bodyOrder) cutoff →+*
      CutoffRing (fun _ : Output => 1) cutoff :=
  Ideal.Quotient.lift _
    ((quotientMap (fun _ : Output => 1) cutoff).comp
      (outputHom primary body primaryChannel bodyChannel).toRingHom)
    (fun table h => Ideal.Quotient.eq_zero_iff_mem.mpr
      (outputHom_hasOrder primary body primaryChannel bodyChannel (cutoff + 1) table h))

@[simp] theorem outputQuotient_mk (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (cutoff : ℕ)
    (table : Table (InputSeed Color)) :
    outputQuotient primary body primaryChannel bodyChannel cutoff
      (quotientMap (fun seed : InputSeed Color => seed.primaryOrder + seed.bodyOrder) cutoff table) =
      quotientMap (fun _ : Output => 1) cutoff
        (outputHom primary body primaryChannel bodyChannel table) := rfl



end

end AFT.RepresentedPolynomial

end

section




































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.partialInputLinear
end AFT.MixedKernel.partialInputLinear
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
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
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap



/-! # Exact evaluation of the actual body and endpoint mean input tables -/

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

def profileForm : (Color → ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun profile := ∑ color, MvPolynomial.C (profile color)*MvPolynomial.X color
  map_add' first second := by simp only [Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]
  map_smul' scalar profile := by
    simp only [Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum,RingHom.id_apply,MvPolynomial.smul_eq_C_mul,mul_assoc]



end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section






end
end AFT.V7Calibration

end

section









/-! # Exact centered generating polynomials of finite physical laws -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

theorem profileForm_apply (profile : Color → ℝ) :
    profileForm profile = ∑ color,MvPolynomial.C (profile color)*MvPolynomial.X color := rfl

/-- The color factor used by the actual centered histogram generating law. -/
def centeredFactor (reference : Color → ℝ) (color : Color) : MvPolynomial Color ℝ :=
  1+MvPolynomial.X color-profileForm reference

def singleGenerating (reference profile : Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ color,MvPolynomial.C (profile color)*centeredFactor reference color

def pairForm (mass : Color → Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ first,∑ second,MvPolynomial.C (mass first second)*MvPolynomial.X first*MvPolynomial.X second



def pairGenerating (reference : Color → ℝ) (mass : Color → Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ first,∑ second,MvPolynomial.C (mass first second)*centeredFactor reference first*centeredFactor reference second

def tripleGenerating (reference : Color → ℝ) (mass : Color → Color → Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ first,∑ second,∑ third,MvPolynomial.C (mass first second third)*centeredFactor reference first*
    centeredFactor reference second*centeredFactor reference third



























end
end AFT.RepresentedPolynomial

end

section





/-! # The exact rational formal logarithm used by finite log certificates -/

namespace AFT.FormalLogarithm

open scoped BigOperators Classical PowerSeries

noncomputable section

set_option backward.isDefEq.respectTransparency false

def logarithm : PowerSeries ℚ := PowerSeries.mk fun order =>
  match order with
  | 0 => 0
  | index + 1 => (-1 : ℚ) ^ index / (index + 1)

@[simp] theorem logarithm_constant : PowerSeries.constantCoeff logarithm = 0 := rfl











end

end AFT.FormalLogarithm

end

section











/-! # Ordinary generating polynomials determine the entire finite histogram -/
namespace AFT.HistogramGenerating
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color Slot : Type*} [Fintype Color] [Fintype Slot]

/-- Color counts for an arbitrary finite set of physical coordinates. -/
def counts (word : Slot → Color) : Color →₀ ℕ := ∑ slot,Finsupp.single (word slot) 1

omit [Fintype Color] in
theorem counts_apply (word : Slot → Color) (color : Color) :
    counts word color = Fintype.card {slot // word slot=color} := by
  simp only [counts,Finsupp.finset_sum_apply,Finsupp.single_apply]
  simp only [← Finset.card_filter,← Fintype.card_subtype]

def boundedHistogram (N : ℕ) (hcard : Fintype.card Slot≤N) (word : Slot → Color) : Histogram N Color :=
  fun color => ⟨counts word color,by
    rw [counts_apply]
    exact Nat.lt_succ_of_le ((Fintype.card_subtype_le _).trans hcard)⟩

def histogramExponent (N : ℕ) (hist : Histogram N Color) : Color →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun color => (hist color : ℕ)



@[simp] theorem boundedHistogram_exponent (N : ℕ) (hcard : Fintype.card Slot≤N) (word : Slot → Color) :
    histogramExponent N (boundedHistogram N hcard word)=counts word := by ext color; rfl













end
end AFT.HistogramGenerating

end

section





/-! # Exact action of coordinate profile operators on a spanning product family -/

namespace AFT.MixedKernel

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def productKernel (functions : Slot → Color → ℝ) (word : Slot → Color) : ℝ :=
  ∏ slot, functions slot (word slot)



















end
end AFT.MixedKernel

end

section



































namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
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
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap




/-! # Actual joint root convolution of literal body and mixed pair inputs -/

namespace AFT.FiniteDist

open scoped BigOperators Classical
noncomputable section
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]



end
end AFT.FiniteDist

namespace AFT.SafeConvolution

open scoped BigOperators Classical
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G]



end
end AFT.SafeConvolution

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]
local instance jointPairFinDecEq (n : ℕ) : DecidableEq (Fin n) := instDecidableEqFin n


end
end AFT.RepresentedPolynomial

namespace AFT.GaussianSource

noncomputable section



end
end AFT.GaussianSource

namespace AFT.V7Calibration

open GaussianSource SafeConvolution RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero





end
end AFT.V7Calibration

end

section











namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput



/-! # Literal finite seed monomials as disjoint joint input kernels -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

/-- Every seed occurrence has its own distinct input coordinates. -/
def ControlProductSlot : List (InputSeed Color) → Type
  | [] => PEmpty
  | seed :: rest => Fin (seed.primaryOrder + seed.bodyOrder) ⊕ ControlProductSlot rest

instance controlProductSlotFintype (seeds : List (InputSeed Color)) : Fintype (ControlProductSlot seeds) := by
  induction seeds with
  | nil => exact inferInstanceAs (Fintype PEmpty)
  | cons seed rest ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin (seed.primaryOrder + seed.bodyOrder) ⊕ ControlProductSlot rest))

instance controlProductSlotDecEq (seeds : List (InputSeed Color)) : DecidableEq (ControlProductSlot seeds) := by
  induction seeds with
  | nil => exact inferInstanceAs (DecidableEq PEmpty)
  | cons seed rest ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Fin (seed.primaryOrder + seed.bodyOrder) ⊕ ControlProductSlot rest))































end
end AFT.RepresentedPolynomial

end


