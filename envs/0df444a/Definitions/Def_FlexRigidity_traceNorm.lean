-- Prove2me | Definitions.Def_FlexRigidity_traceNorm
-- name    : FlexRigidity_traceNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:47.831043+00:00
-- url     : https://prove2.me/theorems/f801cbc6-edc8-496d-ac4c-163a4cb03bb8
-- title:
--   Trace norm $\|X\|_1$
-- statement:
--   The **trace norm** of an operator $X$ is $\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Definitions 2.5–2.6, p. 19

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Trace norm** `‖X‖₁ = Tr √(X†X)` (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, Definitions 2.5–2.6, p. 19). -/
def traceNorm {I : Type} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) : ℝ :=
  tr (spectralPower (Xᴴ * X) (1 / 2))

end FlexRigidity


