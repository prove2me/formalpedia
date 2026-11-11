-- Prove2me | Definitions.Def_FlexRigidity_blockC
-- name    : FlexRigidity_blockC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:58.228203+00:00
-- url     : https://prove2.me/theorems/2aae0343-15fa-428c-8790-49223e947cce
-- title:
--   The $C_i=c$ block of a round output
-- statement:
--   For an operator on $R\,Z\,W$ whose classical register $Z$ determines the record $C$, keep the entries whose row and column both have record $c$. For a state classical on $Z$ this is the partial state $\sigma_{\wedge(C_i=c)}$ of Definition 2.3.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), §4.1, pp. 29–30

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

/-- **The `C_i = c` block** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact
sha256 8c67699d…, §4.1, pp. 29–30): for an operator on `R × (Z × W)` whose register `Z` determines
the record `C` through `cOf : Z → C`, keep the entries whose row and column both have record `c`
(the partial state `σ_{∧(C_i = c)}` of Definition 2.3 for a state classical on `Z`). -/
def blockC {R Z W C : Type} [DecidableEq C] (cOf : Z → C) (c : C)
    (X : Matrix (R × (Z × W)) (R × (Z × W)) ℂ) : Matrix (R × (Z × W)) (R × (Z × W)) ℂ :=
  Matrix.of fun i j => if cOf i.2.1 = c ∧ cOf j.2.1 = c then X i j else 0

end FlexRigidity


