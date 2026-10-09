-- Prove2me | Definitions.Def_ConnesGreen_positive_endpoint_support
-- name    : ConnesGreen_positive_endpoint_support
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-09T06:27:09.477244+00:00
-- url     : https://prove2.me/theorems/9db0e8f1-bdc0-4f4a-83c9-d52faa02e563
-- title:
--   Original maximizing eigenspace and exact sharp shifted margin
-- statement:
--   Two auxiliary data definitions on the unchanged original physical carrier: the actual maximizing eigenspace $E=\ker(N_SN_S^*-PP^*-\mu I)$ and the exact sharp shifted analysis margin $\|P^*x\|^2-\|N_S^*x\|^2+\mu\|x\|^2$. All actual zero multiplicities, selected actors, full positive analysis and original finite corrections are retained. These definitions assert no spectral gap, finite-support property, certificate existence or RH.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/PositiveEndpointSupport.lean, compiling source c9aab301faeba96dcda203002677d6cf2cf396c6

import Definitions.Def_ConnesGreen_selected_loss_covariance
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
namespace ConnesGreen
def canonicalMaximizingSpace (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    Submodule ℂ (Physical t) :=
  Module.End.eigenspace (canonicalLossCovariance t ht S).toLinearMap
    (canonicalCertificateThreshold t ht S : ℂ)
def canonicalSharpMargin (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (x : Physical t) : ℝ :=
  ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
    ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 +
      canonicalCertificateThreshold t ht S * ‖x‖ ^ 2
end ConnesGreen


