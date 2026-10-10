-- Prove2me | Definitions.Def_ConnesGreen_integral_sampling_row
-- name    : ConnesGreen_integral_sampling_row
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-09T17:05:35.871723+00:00
-- url     : https://prove2.me/theorems/c3812fd1-4d37-486e-92f3-2df10d68d108
-- title:
--   Original actual-positive integral sampling row
-- statement:
--   An auxiliary function name for the EXISTING exact integral positive sampling row against the unchanged tagged actor family: original positive $F$ columns first and selected negative $S$ columns second. It uses the existing $\mathrm{canonicalPairGramKernel}$ with row sign $+1$ and column signs $+1,-1$, preserving actual zeta-zero indices, analytic multiplicities and original pair normalization. No uniqueness, finite determination, positivity or RH property is asserted.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/FiniteSamplingWitness.lean, compiling source a5af8470c9220c0783752dac5c5a25fc842dbe0d

import Definitions.Def_ConnesGreen_integral_certificate_kernel

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
namespace ConnesGreen
def canonicalIntegralSamplingRow (t : ℝ) (S F : Finset CriticalZeros) (ρ : CriticalZeros) :
    ({σ : CriticalZeros // σ ∈ F} ⊕ {σ : CriticalZeros // σ ∈ S}) → ℂ :=
  Sum.elim
    (fun σ => canonicalPairGramKernel t 1 1 ρ σ.1)
    (fun σ => canonicalPairGramKernel t 1 (-1) ρ σ.1)
end ConnesGreen


