-- Prove2me | Definitions.Def_ConnesGreen_selected_loss_covariance
-- name    : ConnesGreen_selected_loss_covariance
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-09T05:51:59.495589+00:00
-- url     : https://prove2.me/theorems/b7083c65-38a5-4333-9c4d-d3f512d97464
-- title:
--   Original selected loss covariance with the complete positive actor
-- statement:
--   The original selected loss covariance $A=N_SN_S^*-PP^*$ on the ORIGINAL completed physical carrier, for one unchanged finite actual-zero selected packet. The full original positive actor, multiplicities, physical norm and all existing finite corrections are retained. This auxiliary operator records selected loss; it does not assert RH, positivity or spectral attainment.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/ThresholdSpectrum.lean, compiling source ab20377e04b8056e6db154b7054f60e0ce0a8f00

import Definitions.Def_ConnesGreen_sharp_certificate_threshold
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
namespace ConnesGreen
def canonicalLossCovariance (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    Physical t →L[ℂ] Physical t :=
  canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint -
    canonicalPositiveCovariance t ht
end ConnesGreen


