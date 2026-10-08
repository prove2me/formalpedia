-- Prove2me | Definitions.Def_ConnesGreen_RG0_original_support_right_marker
-- name    : ConnesGreen_RG0_original_support_right_marker
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-07T23:46:01.554419+00:00
-- url     : https://prove2.me/theorems/f087e6ac-d25d-460c-92fc-453d38c16fac
-- title:
--   Original actual-zero prescribed support-right marker and exact limit custody
-- statement:
--   Define the ORIGINAL support-right marker as the witness chosen from the ACCEPTED original ordered-limit theorem, for a nonnegative endpoint and unchanged finite actual-zero packet. The definition is exactly the native canonicalSupportRightMarker body. Its nonnegativity, identity upper bound, supremum characterization and norm-limit specification are proved, and uniqueness holds for any original support-right norm limit. Positive regularization tends to zero first; original support then tends to the endpoint from the right. No limit exchange, arithmetic half-bound, critical-endpoint identification, neutral attainment, global positivity or RH is assumed.
-- source:
--   Native CanonicalGreenSupportLimit.lean at dfaa61225f3d5a1d5b94a14884b96a18ae82816b, canonicalSupportRightMarker/spec/unique exact declaration bodies. Constructor premise is the independently checked and ACCEPTED original ordered-limit theorem, not a postulate.

import Theorems.Thm_ConnesGreen_canonical_actual_zero_support_right_limit
open Complex ConnesRZ ConnesRZFrontier ConnesGreen
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
noncomputable section
namespace ConnesGreen
def canonicalSupportRightMarker (c : ℝ) (hc : 0 ≤ c) (S : Finset CriticalZeros) :
    ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) :=
  Classical.choose (canonical_actual_zero_support_right_limit c hc S)

theorem canonicalSupportRightMarker_spec (c : ℝ) (hc : 0 ≤ c) (S : Finset CriticalZeros) :
    0 ≤ canonicalSupportRightMarker c hc S ∧ canonicalSupportRightMarker c hc S ≤ 1 ∧
    IsLUB ((fun t => positiveWindowPicardMarker t S) '' Ioi c) (canonicalSupportRightMarker c hc S) ∧
    Tendsto (fun t => positiveWindowPicardMarker t S)
      (nhdsWithin c (Ioi c)) (nhds (canonicalSupportRightMarker c hc S)) :=
  Classical.choose_spec (canonical_actual_zero_support_right_limit c hc S)

theorem canonicalSupportRightMarker_unique (c : ℝ) (hc : 0 ≤ c) (S : Finset CriticalZeros)
    (Gplus : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ))
    (hlim : Tendsto (fun t => positiveWindowPicardMarker t S)
      (nhdsWithin c (Ioi c)) (nhds Gplus)) :
    Gplus = canonicalSupportRightMarker c hc S :=
  tendsto_nhds_unique hlim (canonicalSupportRightMarker_spec c hc S).2.2.2


end ConnesGreen


