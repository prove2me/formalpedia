-- Prove2me | Definitions.Def_ConnesGreen_RG0_original_actors
-- name    : ConnesGreen_RG0_original_actors
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-07T22:24:51.55255+00:00
-- url     : https://prove2.me/theorems/e519d2ed-5541-4911-8aed-da57a12a9e5c
-- title:
--   Original completed Green pair syntheses and covariance interfaces recovered from RG-0
-- statement:
--   On the original completed Dirichlet carrier, retain the native bounded column synthesis, actual analytic zeta-zero multiplicities and reflected pair columns. The accepted RG-0 realization supplies exact physical column norms and square summability; the original positive, selected-negative, full-negative and complementary-negative synthesis operators are then defined by the unchanged native column-synthesis bodies. Basis-column identities and uniqueness give original actor custody. The positive covariance and complete complementary covariance retain every actual zero in their specified channels. No positivity, endpoint identification, arithmetic jump bound or RH is assumed.
-- source:
--   Recovered exact declaration bodies from monocap-tech/weil at 4ba3a3a569d72a0d5af2ba6ea320f948030dcca5: WeilDefect/Connes/ColumnSynthesis.lean, CanonicalGreenSeparation.lean, CanonicalGreenBackground.lean and CanonicalGreenMarker.lean. RG-0 is reused for the logically required metric and summability proofs; proof irrelevance leaves the synthesis values unchanged in the native environment.

import Definitions.Def_ConnesGreen_actual_pair_columns
import Theorems.Thm_ConnesGreen_canonical_Green_realization_and_synthesis
set_option autoImplicit false

open Complex ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp ENNReal Classical

noncomputable section
namespace WeilDefect.ConnesNative

variable {ι H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Auxiliary norm sequence for a supplied column family. This records a
summability proof; it does not change the columns or the physical carrier. -/
def columnNormCoefficients (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2)) : ℓ²(ι, ℂ) :=
  ⟨fun i => (‖v i‖ : ℂ), memℓp_gen (by
    simpa [Complex.norm_real, Real.norm_eq_abs, Real.rpow_natCast] using hv)⟩

lemma columnSeries_norm_summable (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (u : ℓ²(ι, ℂ)) : Summable (fun i => ‖u i • v i‖) := by
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa using Real.HolderConjugate.two_two
  have hh := (lp.tsum_mul_le_mul_norm hp u (columnNormCoefficients v hv)).1
  simpa [norm_smul, columnNormCoefficients, Complex.norm_real, Real.norm_eq_abs] using hh

lemma columnSeries_summable (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (u : ℓ²(ι, ℂ)) : Summable (fun i => u i • v i) :=
  (columnSeries_norm_summable v hv u).of_norm

lemma columnSeries_bound (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (u : ℓ²(ι, ℂ)) :
    ‖∑' i, u i • v i‖ ≤ ‖columnNormCoefficients v hv‖ * ‖u‖ := by
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa using Real.HolderConjugate.two_two
  have hh := lp.tsum_mul_le_mul_norm hp u (columnNormCoefficients v hv)
  calc
    _ ≤ ∑' i, ‖u i • v i‖ := norm_tsum_le_tsum_norm (columnSeries_norm_summable v hv u)
    _ = ∑' i, ‖u i‖ * ‖columnNormCoefficients v hv i‖ := by
      simp [norm_smul, columnNormCoefficients, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖u‖ * ‖columnNormCoefficients v hv‖ := hh.2
    _ = _ := mul_comm _ _

/-- Bounded synthesis of EXACTLY the supplied columns, with the ordinary l2
coefficient carrier. This is the extension of their finite linear combinations,
not a replacement for a native metric or a postulated bounded operator. -/
def columnSynthesis (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2)) :
    ℓ²(ι, ℂ) →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun u => ∑' i, u i • v i
      map_add' := fun u w => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (columnSeries_summable v hv u).tsum_add (columnSeries_summable v hv w)
      map_smul' := fun c u => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_smul]
        simpa only [smul_smul, smul_eq_mul, RingHom.id_apply] using
          (columnSeries_summable v hv u).tsum_const_smul c }
    ‖columnNormCoefficients v hv‖ (columnSeries_bound v hv)

theorem columnSynthesis_apply (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (u : ℓ²(ι, ℂ)) : columnSynthesis v hv u = ∑' i, u i • v i := rfl

theorem columnNormCoefficients_norm_sq (v : ι → H)
    (hv : Summable (fun i => ‖v i‖ ^ 2)) :
    ‖columnNormCoefficients v hv‖ ^ 2 = ∑' i, ‖v i‖ ^ 2 := by
  have hh := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (columnNormCoefficients v hv)
  simpa [columnNormCoefficients, Real.rpow_two, Complex.norm_real] using hh

theorem columnSynthesis_norm_sq_le (v : ι → H)
    (hv : Summable (fun i => ‖v i‖ ^ 2)) :
    ‖columnSynthesis v hv‖ ^ 2 ≤ ∑' i, ‖v i‖ ^ 2 := by
  have hb : ‖columnSynthesis v hv‖ ≤ ‖columnNormCoefficients v hv‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    exact columnSeries_bound v hv
  rw [← columnNormCoefficients_norm_sq v hv]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

theorem columnSynthesis_single (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (i : ι) (c : ℂ) : columnSynthesis v hv (lp.single 2 i c) = c • v i := by
  classical
  rw [columnSynthesis_apply]
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    simp [lp.single_apply, Pi.single_apply, hj]

/-- The adjoint coordinates are the inner products with the ORIGINAL columns. -/
theorem columnSynthesis_adjoint_coordinate (v : ι → H)
    (hv : Summable (fun i => ‖v i‖ ^ 2)) (h : H) (i : ι) :
    (ContinuousLinearMap.adjoint (columnSynthesis v hv)) h i = ⟪v i, h⟫_ℂ := by
  have hh := ContinuousLinearMap.adjoint_inner_right (columnSynthesis v hv)
    (lp.single 2 i (1 : ℂ)) h
  rw [columnSynthesis_single, one_smul] at hh
  simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using hh

/-- Parseval for the constructed adjoint: the exact column norm identity is
proved, not supplied as an arithmetic attachment premise. -/
theorem columnSynthesis_adjoint_norm_sq (v : ι → H)
    (hv : Summable (fun i => ‖v i‖ ^ 2)) (h : H) :
    ‖(ContinuousLinearMap.adjoint (columnSynthesis v hv)) h‖ ^ 2 =
      ∑' i, ‖⟪v i, h⟫_ℂ‖ ^ 2 := by
  have hh := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    ((ContinuousLinearMap.adjoint (columnSynthesis v hv)) h)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    columnSynthesis_adjoint_coordinate] using hh

/-- Custody/uniqueness: a supplied native synthesis with the same columns is
the constructed extension. No freedom to change the physical operator remains. -/
theorem columnSynthesis_unique [DecidableEq ι] (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2))
    (S : ℓ²(ι, ℂ) →L[ℂ] H)
    (hcolumns : ∀ i, S (lp.single 2 i (1 : ℂ)) = v i) : S = columnSynthesis v hv := by
  ext u
  have hs := S.hasSum (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) u)
  have heq : (fun i => S (lp.single 2 i (u i))) = fun i => u i • v i := by
    funext i
    have hh : lp.single (E := fun _ : ι => ℂ) 2 i (u i) =
        u i • lp.single (E := fun _ : ι => ℂ) 2 i (1 : ℂ) := by
      simpa using (lp.single_smul (E := fun _ : ι => ℂ) 2 i (u i) (1 : ℂ))
    rw [hh, map_smul, hcolumns]
  rw [heq] at hs
  exact hs.tsum_eq.symm

end WeilDefect.ConnesNative

namespace WeilDefect.ConnesNative
open ConnesRZFrontier
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem Green_pair_column_energy (v : CriticalZeros → H) (ρ : CriticalZeros) :
    ‖positiveGreenColumn v ρ‖ ^ 2 + ‖negativeGreenColumn v ρ‖ ^ 2 =
      (‖weightedGreenColumn v ρ‖ ^ 2 + ‖weightedGreenColumn v (reflectedZero ρ)‖ ^ 2) / 2 := by
  have hp := parallelogram_law_with_norm ℂ (weightedGreenColumn v ρ)
    (weightedGreenColumn v (reflectedZero ρ))
  unfold positiveGreenColumn negativeGreenColumn
  simp only [norm_smul, mul_pow]
  norm_num
  nlinarith [hp]
end WeilDefect.ConnesNative

namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative
-- Same statement and pair normalization as native; the already accepted RG-0
-- aggregate supplies both the exact actual-zero metric and summability.
theorem canonical_actor_columns_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun ρ => ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ‖ ^ 2) ∧
    Summable (fun ρ => ‖negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ‖ ^ 2) := by
  have rg := canonical_Green_realization_and_synthesis t ht
  let v := fun τ => sourceEmbed t (actualGreenSource τ)
  have hs : Summable (fun ρ => ‖weightedGreenColumn v ρ‖ ^ 2) := by
    have he : (fun ρ => ‖weightedGreenColumn v ρ‖ ^ 2) = weightedEnergy t := by
      funext ρ
      simp only [weightedGreenColumn, norm_smul, mul_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (Nat.cast_nonneg _)]
      change (zeroMult ρ.1 : ℝ) * ‖sourceEmbed t (actualGreenSource ρ)‖ ^ 2 = _
      rw [(rg.2.1 ρ).2.2.2.2]
      rfl
    rw [he]
    exact rg.2.2.2.1
  have hr : Summable (fun ρ : CriticalZeros => ‖weightedGreenColumn v (reflectedZero ρ)‖ ^ 2) :=
    hs.comp_injective (fun a b h => by
      have hh := congrArg reflectedZero h
      simpa only [reflectedZero_involutive] using hh)
  have hb : Summable (fun ρ => ‖positiveGreenColumn v ρ‖ ^ 2 + ‖negativeGreenColumn v ρ‖ ^ 2) := by
    simp_rw [Green_pair_column_energy]
    exact (hs.add hr).div_const 2
  exact ⟨Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun _ => le_add_of_nonneg_right (sq_nonneg _)) hb,
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun _ => le_add_of_nonneg_left (sq_nonneg _)) hb⟩

def canonicalPositiveSynthesis (t : ℝ) (ht : 0 < t) :
    ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t :=
  columnSynthesis (positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)))
    (canonical_actor_columns_summable t ht).1

def canonicalSelectedSynthesis (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t :=
  columnSynthesis (fun ρ => negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1)
    ((canonical_actor_columns_summable t ht).2.comp_injective Subtype.val_injective)

/-- Every original negative actor outside the selected packet, on the same carrier. -/
def canonicalBackgroundSynthesis (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ℓ²({ρ : CriticalZeros // ρ ∉ S}, ℂ) →L[ℂ] Physical t :=
  columnSynthesis (fun ρ => negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1)
    ((canonical_actor_columns_summable t ht).2.comp_injective Subtype.val_injective)

def canonicalNegativeSynthesis (t : ℝ) (ht : 0 < t) :
    ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t :=
  columnSynthesis (negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)))
    (canonical_actor_columns_summable t ht).2

theorem canonicalPositiveSynthesis_single (t : ℝ) (ht : 0 < t) (ρ : CriticalZeros) :
    canonicalPositiveSynthesis t ht (lp.single 2 ρ (1 : ℂ)) =
      positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ := by
  convert (columnSynthesis_single (positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)))
    (canonical_actor_columns_summable t ht).1 ρ (1 : ℂ)).trans (one_smul ℂ _) using 1
  congr 1
  ext τ
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs <;> rfl

theorem canonicalSelectedSynthesis_single (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (ρ : {ρ : CriticalZeros // ρ ∈ S}) :
    canonicalSelectedSynthesis t ht S (lp.single 2 ρ (1 : ℂ)) =
      negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1 := by
  convert (columnSynthesis_single
    (fun τ : {τ : CriticalZeros // τ ∈ S} =>
      negativeGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1)
    ((canonical_actor_columns_summable t ht).2.comp_injective Subtype.val_injective)
    ρ (1 : ℂ)).trans (one_smul ℂ _) using 1
  congr 1
  ext τ
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs <;> rfl

theorem canonicalPositiveSynthesis_unique (t : ℝ) (ht : 0 < t)
    (T : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t)
    (hc : ∀ ρ, T (lp.single 2 ρ (1 : ℂ)) =
      positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) :
    T = canonicalPositiveSynthesis t ht := columnSynthesis_unique _ _ T hc

theorem canonicalSelectedSynthesis_unique (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (T : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t)
    (hc : ∀ ρ, T (lp.single 2 ρ (1 : ℂ)) =
      negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) :
    T = canonicalSelectedSynthesis t ht S := columnSynthesis_unique _ _ T hc

theorem canonicalBackgroundSynthesis_single (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (ρ : {ρ : CriticalZeros // ρ ∉ S}) :
    canonicalBackgroundSynthesis t ht S (lp.single 2 ρ (1 : ℂ)) =
      negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1 := by
  convert (columnSynthesis_single
    (fun τ : {τ : CriticalZeros // τ ∉ S} =>
      negativeGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1)
    ((canonical_actor_columns_summable t ht).2.comp_injective Subtype.val_injective)
    ρ (1 : ℂ)).trans (one_smul ℂ _) using 1
  congr 1
  ext τ
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs <;> rfl

theorem canonicalBackgroundSynthesis_unique (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (T : ℓ²({ρ : CriticalZeros // ρ ∉ S}, ℂ) →L[ℂ] Physical t)
    (hc : ∀ ρ, T (lp.single 2 ρ (1 : ℂ)) =
      negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) :
    T = canonicalBackgroundSynthesis t ht S := columnSynthesis_unique _ _ T hc

def canonicalPositiveCovariance (t : ℝ) (ht : 0 < t) : Physical t →L[ℂ] Physical t :=
  canonicalPositiveSynthesis t ht ∘L (canonicalPositiveSynthesis t ht).adjoint

def canonicalTailCovariance (t : ℝ) (ht : 0 < t) (F : Finset CriticalZeros) :
    Physical t →L[ℂ] Physical t :=
  canonicalBackgroundSynthesis t ht F ∘L (canonicalBackgroundSynthesis t ht F).adjoint

end ConnesGreen


