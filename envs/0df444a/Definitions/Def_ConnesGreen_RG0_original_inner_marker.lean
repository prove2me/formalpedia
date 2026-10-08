-- Prove2me | Definitions.Def_ConnesGreen_RG0_original_inner_marker
-- name    : ConnesGreen_RG0_original_inner_marker
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-07T22:32:04.514984+00:00
-- url     : https://prove2.me/theorems/2c05f376-d94d-41ca-8242-2c7ffb281437
-- title:
--   Original actual-zero regularized and Picard marker interfaces
-- statement:
--   For the unchanged original positive and selected-negative Green syntheses on the completed physical carrier, define the original regularized marker and its uniquely determined positive-regularization norm limit. The finite actual-zero coefficient subtype is retained. The already accepted finite-dimensional marker-limit theorem proves existence, nonnegativity, the identity upper bound and the infimum characterization. The regularized and Picard definitions are the exact native declaration bodies; the total positive-window notation has the same unused zero branch outside positive windows. This interface does not identify a prescribed critical endpoint or assume an arithmetic jump bound, neutral attainment, global Weil positivity or RH.
-- source:
--   Exact native declarations at 4ba3a3a569d72a0d5af2ba6ea320f948030dcca5, CanonicalGreenMarker.lean, CanonicalGreenMarkerLimit.lean, CanonicalGreenSupportLimit.lean; original actor definitions and accepted finite_selected_marker_norm_limit are imported.

import Definitions.Def_ConnesGreen_RG0_original_actors
import Theorems.Thm_WeilDefect_MarkerStability_finite_selected_marker_norm_limit
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Complex ConnesRZ ConnesRZFrontier
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
noncomputable section
namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability

/-- Original selected marker, before taking either of the two endpoint limits. -/
def canonicalRegularizedMarker (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) (ε : ℝ) :
    ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) :=
  marker (canonicalPositiveCovariance t ht + ε • 1) (canonicalSelectedSynthesis t ht S)

/-- Finite dimensionality is proved by the coordinate injection of the ORIGINAL
selected coefficient space, without replacing that space by a surrogate. -/
theorem canonical_selected_coefficient_finiteDimensional (S : Finset CriticalZeros) :
    FiniteDimensional ℂ ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) := by
  letI := Fintype.ofFinite {ρ : CriticalZeros // ρ ∈ S}
  let e : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →ₗ[ℂ]
      ({ρ : CriticalZeros // ρ ∈ S} → ℂ) :=
    { toFun := fun a => fun j => a j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact FiniteDimensional.of_injective e (by
    intro a b hab
    ext j
    exact congrFun hab j)

/-- Every finite original actual-zero packet has an original marker norm limit
as positive regularization tends to zero; no arithmetic premise is used. -/
theorem canonical_actual_zero_picard_limit (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) :
    ∃ G₀ : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ),
      0 ≤ G₀ ∧ G₀ ≤ 1 ∧
      IsGLB ((fun ε : ℝ => canonicalRegularizedMarker t ht S ε) '' Ioi 0) G₀ ∧
      Tendsto (fun ε : ℝ => canonicalRegularizedMarker t ht S ε)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds G₀) := by
  letI := canonical_selected_coefficient_finiteDimensional S
  apply finite_selected_marker_norm_limit (canonicalPositiveCovariance t ht) _
    (canonicalSelectedSynthesis t ht S)
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_self_comp_adjoint _)

/-- The norm limit of the original markers on the original selected packet. -/
def canonicalPicardMarker (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) :=
  Classical.choose (canonical_actual_zero_picard_limit t ht S)

theorem canonicalPicardMarker_spec (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    0 ≤ canonicalPicardMarker t ht S ∧ canonicalPicardMarker t ht S ≤ 1 ∧
    IsGLB ((fun ε : ℝ => canonicalRegularizedMarker t ht S ε) '' Ioi 0)
      (canonicalPicardMarker t ht S) ∧
    Tendsto (fun ε : ℝ => canonicalRegularizedMarker t ht S ε)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (canonicalPicardMarker t ht S)) :=
  Classical.choose_spec (canonical_actual_zero_picard_limit t ht S)

theorem canonicalPicardMarker_unique (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (G₀ : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))
    (hlim : Tendsto (fun ε : ℝ => canonicalRegularizedMarker t ht S ε)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds G₀)) :
    G₀ = canonicalPicardMarker t ht S :=
  tendsto_nhds_unique hlim (canonicalPicardMarker_spec t ht S).2.2.2

theorem canonicalPicardMarker_selfAdjoint (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    IsSelfAdjoint (canonicalPicardMarker t ht S) :=
  ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (canonicalPicardMarker_spec t ht S).1).isSelfAdjoint

/-- Total notation outside positive windows; all limit statements below stay
strictly in positive original windows, so this zero branch is never used. -/
def positiveWindowPicardMarker (t : ℝ) (S : Finset CriticalZeros) :
    ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) :=
  if ht : 0 < t then canonicalPicardMarker t ht S else 0

@[simp] theorem positiveWindowPicardMarker_eq (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    positiveWindowPicardMarker t S = canonicalPicardMarker t ht S := by
  simp [positiveWindowPicardMarker, ht]

end ConnesGreen


