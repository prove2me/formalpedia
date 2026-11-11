-- Prove2me | Definitions.Def_FlexRigidity_RoundO
-- name    : FlexRigidity_RoundO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:55.397794+00:00
-- url     : https://prove2.me/theorems/e1539133-4864-4544-b701-558b8df466df
-- title:
--   Round records $(u_i,x_i,y_i,a_i,b_i)$
-- statement:
--   The classical record of a round of Protocol 2: $u_i\in\{\mathrm{test},\mathrm{gen}\}$ (Lean: `true` = test), the inputs $x_i$, $y_i$ and outputs $a_i$, $b_i$, with $y_i=b_i=\varnothing$ on generation rounds.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Protocol 2, p. 41; §5.3.1, pp. 43–44

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

/-- **The classical round record `(u_i, x_i, y_i, a_i, b_i)`** of Protocol 2 (Arqand–Kundu–Tan,
*Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 41 and §5.3.1, pp. 43–44):
`u_i` is `true` for a test round and `false` for a generation round; `y_i` and `b_i` are `none`
(the empty value `∅`) in a generation round. -/
abbrev RoundO (X Y A B : Type) : Type :=
  Bool × X × Option Y × A × Option B

end FlexRigidity


