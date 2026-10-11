-- Prove2me | Definitions.Def_WeilMarker_regularized_cost
-- name    : WeilMarker_regularized_cost
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-07T05:23:19.910984+00:00
-- url     : https://prove2.me/theorems/95ef2878-4536-4aed-87ab-9055f68b5b23
-- title:
--   Native selected inverse cost and regularized marker
-- statement:
--   For complete complex Hilbert spaces $H$ and $K$, a bounded physical operator $A:H\to H$ and selected synthesis $N:K\to H$, retain the native canonical ring inverse and set
--   $$S(A,N)=N^*A^{-1}N,\qquad \Gamma(A,N)=(I+S(A,N))^{-1}.$$
--   The inverse is totalized by zero for nonunits; the associated stability theorems prove strict positivity and invertibility of every operator actually inverted. On strictly positive operators this is the usual bounded inverse. These are the same selected-cost and marker formulas used in the arithmetic transfer checkpoint. Instantiation on the certified actual-zeta Green carrier is a separate theorem; these definitions do not assume RH or supply an arithmetic half-threshold inequality.
-- source:
--   monocap-tech/weil, WeilDefect/Screening/ShortedCovariance.lean (operatorInverse), WeilDefect/Screening/MarkerStability.lean (selectedCost, marker), and provenance/rh/checkpoints/RH_ZERO_PROV_4_INFINITE_NBR_DIAGONAL_MARKER_STABILITY_20260920.md, equations (3)-(8). Native base commit b019d40205680f9761a4b0a80cbcad56ee1b606b; exact new source is in Connes_Weil_Green_Marker_Recovery.zip.
--
--   Literature/source audit addendum (2026-10-11; COR-19): Exact native software custody, independently verified from retained local Git objects: monocap-tech/weil b019d40205680f9761a4b0a80cbcad56ee1b606b, WeilDefect/Screening/ShortedCovariance.lean, SHA256 f5b021a49d5bdab27134e46e072df5ea07ec3296687b8d8bf3b09880b4e56cf1; monocap-tech/weil d73d0e7f1477c934a3a8f8b01012852128b977bb, WeilDefect/Screening/MarkerStability.lean, SHA256 e6dc1688e5576e682510174da81ff772aaea9ea6b2a0a4beea9e1de405d8fa53. Public availability of these historical pins has not been checked; this addendum verifies local source bytes and preserves the original source ancestry. The unchanged graph RHS values were checked against native definitions by Lean rfl. This is source/value custody, not an assertion that contextual literature supplies the whole definition bundle.

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
set_option autoImplicit false
noncomputable section
namespace WeilDefect.WDT13
/-- The original native canonical ring inverse. -/
def operatorInverse {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) : E →L[ℂ] E := Ring.inverse T
end WeilDefect.WDT13
namespace WeilDefect.MarkerStability
open WeilDefect.WDT13
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
def selectedCost (A : H →L[ℂ] H) (N : K →L[ℂ] H) : K →L[ℂ] K :=
  N.adjoint ∘L operatorInverse A ∘L N
def marker (A : H →L[ℂ] H) (N : K →L[ℂ] H) : K →L[ℂ] K :=
  operatorInverse (1 + selectedCost A N)
end WeilDefect.MarkerStability


