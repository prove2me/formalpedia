-- Prove2me | Definitions.Def_FlexRigidity_weightBlocks
-- name    : FlexRigidity_weightBlocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:47.469803+00:00
-- url     : https://prove2.me/theorems/66adaa12-83b7-4c33-ac5a-861405faf6c6
-- title:
--   Block weighting by $2^{f(c)}$, eq. (17)
-- statement:
--   For an operator $X$ on $ZW$ with record $C$ determined by $Z$ and a real function $f$ on $C$, $\sum_c2^{f(c)}\Pi_cX\Pi_c$, where $\Pi_c$ projects onto the records $C=c$. Applied after $\mathcal P_i$ it is the CP map $\mathcal P^f_i$ with $\mathcal F^f_i=\mathcal T_i\circ\mathcal P^f_i\circ\mathcal G_i$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (17), p. 29

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

/-- **Block weighting by `2^{f(c)}`, eq. (17)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 29): for an operator on `Z × W` with record
`cOf : Z → C`, `Σ_c 2^{f(c)} Π_c X Π_c`, where `Π_c` projects onto the records `C = c`. Applied
after `P_i` it gives the CP map `P^f_i` with `F^f_i = T_i ∘ P^f_i ∘ G_i`. -/
def weightBlocks {Z W C : Type} [DecidableEq C] (cOf : Z → C) (f : C → ℝ)
    (X : Matrix (Z × W) (Z × W) ℂ) : Matrix (Z × W) (Z × W) ℂ :=
  Matrix.of fun i j => if cOf i.1 = cOf j.1 then (((2 : ℝ) ^ f (cOf i.1) : ℝ) : ℂ) * X i j else 0

end FlexRigidity


