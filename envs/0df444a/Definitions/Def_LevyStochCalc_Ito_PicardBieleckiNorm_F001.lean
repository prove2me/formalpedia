-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F001
-- name    : LevyStochCalc_Ito_PicardBieleckiNorm_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:20:37.875187+00:00
-- url     : https://prove2.me/theorems/18750247-502a-472e-bccc-a46b161fed14
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardBieleckiNorm
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardBieleckiNorm. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F000
import Definitions.Def_SourceProof_18a36b239cd6db9b2d40a2d3

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki norm, the process space `S²`, and the drift step of Picard iteration

The Bielecki-weighted `L²` norm `‖X‖_{β,T} = sup_{t ∈ [0,T]} e^{-βt} (𝔼‖X_t‖²)^{1/2}` of a
process on `[0, T]`, the space `SBoundedProcess` of jointly measurable, progressively measurable,
almost surely càdlàg processes of finite norm at weight `0`, and the freeze of such a process at
the horizon, which leaves the norm unchanged and is `L²`-bounded at every later time.  The drift
component `picardStep_drift` of the Picard map is defined here, with its per-component difference
identities, its `L¹` Lipschitz bound, the Cauchy-Schwarz bound `(∫_0^t f)² ≤ t ∫_0^t f²` on a
window, and the per-component `L²` Lipschitz bound that follows from them.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace SBoundedProcess

/-- **The deterministic-time freeze.** `X.stop` is `X` on `[0, T]` and constant at `X T`
afterwards. It has the same Bielecki norm on `[0, T]`, and its `L²` bounds hold at every
horizon, which is what the Picard step's integrand hypotheses need. -/
noncomputable def stop {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (X : SBoundedProcess (n := n) P ℱ T) : SBoundedProcess (n := n) P ℱ T where
  X s ω := X.X (min s T) ω
  measurable_path :=
    X.measurable_path.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  adapted i := (_root_.Prove2MeSourceProof.h_18a36b239cd6db9b2d40a2d3 (X.adapted i)) T
  cadlag_paths := by
    filter_upwards [X.cadlag_paths] with ω hω
    intro t
    refine ⟨?_, ?_⟩
    · rcases lt_or_ge t T with ht | ht
      · have hXt : X.X (min t T) ω = X.X t ω := by rw [min_eq_left ht.le]
        have hev : (fun s => X.X s ω) =ᶠ[nhdsWithin t (Set.Ioi t)]
            fun s => X.X (min s T) ω := by
          filter_upwards [nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Iio ht)] with s hs
          rw [min_eq_left (le_of_lt hs)]
        rw [hXt]
        exact ((hω t).1).congr' hev
      · have hXt : X.X (min t T) ω = X.X T ω := by rw [min_eq_right ht]
        have hev : (fun _ : ℝ => X.X T ω) =ᶠ[nhdsWithin t (Set.Ioi t)]
            fun s => X.X (min s T) ω := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          rw [min_eq_right (le_of_lt (lt_of_le_of_lt ht hs))]
        rw [hXt]
        exact tendsto_const_nhds.congr' hev
    · intro i
      rcases le_or_gt t T with ht | ht
      · obtain ⟨L, hL⟩ := (hω t).2 i
        refine ⟨L, hL.congr' ?_⟩
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [min_eq_left (le_of_lt (lt_of_lt_of_le hs ht))]
      · refine ⟨X.X T ω i, tendsto_const_nhds.congr' ?_⟩
        filter_upwards [nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Ioi ht)] with s hs
        rw [min_eq_right (le_of_lt hs)]
  sup_L2 := by
    rw [bieleckiNorm_min]
    exact X.sup_L2
/-- The second moment at a single time of `[0, T]` is bounded by the squared Bielecki norm. -/
theorem lintegral_sq_le_bieleckiNorm_sq {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (Y : SBoundedProcess (n := n) P ℱ T) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) :
    (∫⁻ ω, ∑ i, (‖Y.X u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ (bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) := by
  have hle : (∫⁻ ω, ∑ i, (‖Y.X u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)
      ≤ bieleckiNorm (P := P) 0 T Y.X := by
    unfold bieleckiNorm
    refine le_trans (le_of_eq ?_)
      (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
        ENNReal.ofReal (Real.exp (-0 * t))
          * (∫⁻ ω, ∑ i, (‖Y.X t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)) u hu)
    simp
  calc (∫⁻ ω, ∑ i, (‖Y.X u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ((∫⁻ ω, ∑ i, (‖Y.X u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := by
        rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ (bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) := pow_le_pow_left' hle 2
/-- **The frozen process is `L²`-bounded at every nonnegative time**, not only on `[0, T]` —
this is what the Picard step's integrand hypotheses need at horizons beyond `T`. -/
theorem lintegral_sq_stop_le {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T) {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ ω, ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ (bieleckiNorm (P := P) 0 T Y.X) ^ (2 : ℕ) :=
  Y.lintegral_sq_le_bieleckiNorm_sq ⟨le_min hs hT, min_le_right s T⟩
@[simp] theorem stop_apply {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (X : SBoundedProcess (n := n) P ℱ T) (s : ℝ) (ω : Ω) :
    X.stop.X s ω = X.X (min s T) ω := rfl
/-- On `[0, T]` the frozen process agrees with the original. -/
theorem stop_eq_of_le {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (X : SBoundedProcess (n := n) P ℱ T) {s : ℝ} (hs : s ≤ T) (ω : Ω) :
    X.stop.X s ω = X.X s ω := by
  rw [stop_apply, min_eq_left hs]
end SBoundedProcess

/-- **The Picard map step.** Given a candidate process `X` and the
coefficients `(μ, σ, γ)`, the next iterate is

  `Φ X : t ↦ x_0 + ∫_0^t μ(s, X_s) ds + ∫_0^t σ(s, X_s) dW_s
      + ∫_0^t ∫_E γ(s, X_s, e) Ñ(ds, de)`.

This is the actual Picard map — not a placeholder. The integrands
require joint measurability + adaptedness hypotheses on `X` together
with measurability of the coefficient functions; these are bundled as
explicit hypotheses to keep the map well-typed.

For now we provide ONLY the drift component `∫_0^t μ(s, X_s) ds`; the
Brownian and compensated-Poisson integral components require
additional measurability bundling that is built up in subsequent
lemmas. -/
noncomputable def picardStep_drift
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  x₀ + fun i => ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Per-component pointwise drift difference identity.** For any two
candidates `X, Y`, the difference of drift components is the Bochner
integral of the per-component drift-coefficient difference:

  `(drift X x₀ t ω - drift Y x₀ t ω) i
    = ∫ s in [0, t], (μ s (X s ω) i - μ s (Y s ω) i) ds`.

This is just the algebraic identity that `picardStep_drift` cancels the
common `x₀` and pulls the integral subtraction componentwise — no
analytic content yet, but a load-bearing intermediate. -/
lemma picardStep_drift_diff
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω) (i : Fin n)
    -- Integrability of each side (needed for `integral_sub`):
    (h_X_int : MeasureTheory.IntegrableOn (fun s => coeffs.μ s (X s ω) i)
      (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn (fun s => coeffs.μ s (Y s ω) i)
      (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    (picardStep_drift (E := E) coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i
      = ∫ s in Set.Icc (0 : ℝ) t,
          (coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i) := by
  unfold picardStep_drift
  -- LHS = ((x₀ + (fun i => ∫ ... μ(X) i)) - (x₀ + (fun i => ∫ ... μ(Y) i))) i
  --     = (∫ ... μ(X) i - ∫ ... μ(Y) i)  by add_sub_add_cancel
  --     = ∫ ... (μ(X) i - μ(Y) i)        by integral_sub
  simp only [Pi.add_apply, Pi.sub_apply, add_sub_add_left_eq_sub]
  exact (MeasureTheory.integral_sub h_X_int h_Y_int).symm
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Vector form of the drift difference identity.** Bundles the per-component
identity into a `funext` over `i : Fin n`.

  `drift X x₀ t ω - drift Y x₀ t ω
    = fun i => ∫ s in [0, t], (μ s (X s ω) i - μ s (Y s ω) i)`. -/
lemma picardStep_drift_diff_vec
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω)
    (h_X_int : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω
      = fun i => ∫ s in Set.Icc (0 : ℝ) t,
          (coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i) := by
  funext i
  exact picardStep_drift_diff coeffs X Y x₀ t ω i (h_X_int i) (h_Y_int i)
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Per-component pointwise L¹ Lipschitz bound on the drift step.**

For Lipschitz μ with rate `L_μ` componentwise, the i-th component of
the drift-step difference is bounded by the time-integral of the
componentwise difference:

  `|(drift X x₀ t ω - drift Y x₀ t ω) i|
    ≤ ∫ s in [0, t], |μ s (X s ω) i - μ s (Y s ω) i|`. -/
lemma picardStep_drift_diff_componentwise_norm_bound
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω) (i : Fin n)
    (h_X_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    |(picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i|
      ≤ ∫ s in Set.Icc (0 : ℝ) t,
          |coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i| := by
  rw [picardStep_drift_diff coeffs X Y x₀ t ω i h_X_int h_Y_int]
  -- |∫ f| ≤ ∫ |f| via MeasureTheory.norm_integral_le_integral_norm specialized to ℝ.
  have h_sub_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i)
      (Set.Icc (0 : ℝ) t) MeasureTheory.volume := h_X_int.sub h_Y_int
  -- For ℝ-valued integrand, ‖x‖ = |x|, so norm_integral_le_integral_norm gives
  -- |∫ f| ≤ ∫ |f|. The lemma is stated for normed groups; |·| is the ℝ-norm.
  have h := MeasureTheory.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))
    (f := fun s => coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i)
  -- ‖·‖ on ℝ is |·|, so the goal matches after rewriting.
  simpa [Real.norm_eq_abs] using h
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Per-component Lipschitz bound on the drift step.**

Using the per-component Lipschitz hypothesis on `μ`, the i-th component
of the drift difference is bounded by `L_μ * ∫_0^t ‖X_s - Y_s‖ ds`:

  `|(drift X x₀ t ω - drift Y x₀ t ω) i|
    ≤ L_μ · ∫ s in [0, t], ‖X s ω - Y s ω‖`.

This is the operator-level statement that feeds the Bielecki-norm
contraction. -/
lemma picardStep_drift_diff_lipschitz_componentwise
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (_hL_μ_nn : 0 ≤ L_μ)
    -- Per-component Lipschitz on μ: |μ s x₁ i - μ s x₂ i| ≤ L_μ · ‖x₁ - x₂‖.
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω) (i : Fin n)
    (h_X_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    -- And the integrand ‖X_s - Y_s‖ must itself be integrable for the RHS
    -- bound's `mul_integral` rewrite to be valid:
    (h_XY_diff_int : MeasureTheory.IntegrableOn
      (fun s => ‖X s ω - Y s ω‖) (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    |(picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i|
      ≤ L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ := by
  -- Chain the two preceding bounds:
  -- |·| ≤ ∫ |μ(X) i - μ(Y) i|        (norm_integral_le_integral_norm)
  --     ≤ ∫ L_μ * ‖X - Y‖             (Lipschitz, integral monotonicity)
  --     = L_μ * ∫ ‖X - Y‖             (constant pull-out)
  refine (picardStep_drift_diff_componentwise_norm_bound
    coeffs X Y x₀ t ω i h_X_int h_Y_int).trans ?_
  -- Now goal: ∫ |μ(X) i - μ(Y) i| ≤ L_μ * ∫ ‖X - Y‖.
  -- Use integral_mono_of_nonneg or set_integral_mono after rewriting RHS as integral.
  rw [show L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖
        = ∫ s in Set.Icc (0 : ℝ) t, L_μ * ‖X s ω - Y s ω‖ from
      (MeasureTheory.integral_const_mul L_μ _).symm]
  -- Integral monotonicity. Need: integrability of both integrands + pointwise ≤.
  refine MeasureTheory.setIntegral_mono_on ?_ ?_
    measurableSet_Icc (fun s _ => h_μ_lip s (X s ω) (Y s ω) i)
  · -- LHS integrable: |μ(X) i - μ(Y) i| ∈ L¹.
    exact (h_X_int.sub h_Y_int).abs
  · -- RHS integrable: L_μ * ‖X - Y‖ ∈ L¹.
    exact h_XY_diff_int.const_mul L_μ
end LevyStochCalc.Ito.Picard


