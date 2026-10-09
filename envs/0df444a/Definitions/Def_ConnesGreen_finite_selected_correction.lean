-- Prove2me | Definitions.Def_ConnesGreen_finite_selected_correction
-- name    : ConnesGreen_finite_selected_correction
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-08T22:22:49.32377+00:00
-- url     : https://prove2.me/theorems/391a1a04-e1ab-4366-9f69-dc63aa4c8d8a
-- title:
--   Finite positive synthesis and correction on the original selected coefficient space
-- statement:
--   For finite actual-zero packet F, define P_F by the existing column-synthesis constructor applied to exactly the original positive F columns on the original physical carrier. Keep N as the original selected negative synthesis for packet S. With C=P_F* N and B=P_F* P_F + δI, define the selected coefficient correction D_S=δI−N* N+C* Ring.inverse(B) C on the ORIGINAL selected coefficient space. The inverse is the existing ring inverse; for δ>0 its coefficient covariance is proved strictly positive in subsequent theorems. No full positive actor, negative packet, zero subtype, multiplicity, carrier, or test predicate is replaced. No positivity assertion is embedded in this definition bundle.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/FiniteSelectedCertificates.lean at d28908eb3d61a4a81d7b4a5aff70ea26b6680897

import Definitions.Def_ConnesGreen_integral_certificate_kernel
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
namespace ConnesGreen
/-- Auxiliary finite synthesis of the ORIGINAL positive F columns on the
ORIGINAL physical carrier. The full positive actor remains unchanged. -/
def canonicalFinitePositiveSynthesis (t : ℝ) (F : Finset CriticalZeros) :
    ℓ²({ρ : CriticalZeros // ρ ∈ F}, ℂ) →L[ℂ] Physical t :=
  columnSynthesis
    (fun ρ => positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1)
    (by exact Summable.of_finite)

/-- Exact finite correction on the ORIGINAL selected negative coefficient space.
Only the positive coefficient covariance is inverted, with positive δI. -/
def canonicalFiniteSelectedCorrection (t : ℝ) (ht : 0 < t)
    (S F : Finset CriticalZeros) (δ : ℝ) :
    ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) :=
  let P := canonicalFinitePositiveSynthesis t F
  let N := canonicalSelectedSynthesis t ht S
  δ • 1 - N.adjoint ∘L N + (P.adjoint ∘L N).adjoint ∘L
    Ring.inverse (P.adjoint ∘L P + δ • 1) ∘L (P.adjoint ∘L N)


end ConnesGreen


