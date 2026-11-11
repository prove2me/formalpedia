-- Prove2me | Definitions.Def_FlexRigidity_IsIsometry
-- name    : FlexRigidity_IsIsometry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:47.982206+00:00
-- url     : https://prove2.me/theorems/06444ff1-3798-4dc0-8341-194677fefa99
-- title:
--   Isometries $V^\dagger V=I$
-- statement:
--   A linear map $V:M\to SQ$ between finite registers is an **isometry** when $V^\dagger V=I_M$. Isometries appear as the local extraction maps $V^{\mathrm A}:M_{\mathrm A}\to S_{\mathrm A}Q_{\mathrm A}$, $V^{\mathrm B}:M_{\mathrm B}\to S_{\mathrm B}Q_{\mathrm B}$ of the self-testing postulate.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Postulate Set 5.3(iii), p. 39

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

/-- **Isometries** `V : M → S Q` (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, Postulate Set 5.3(iii), p. 39, and the proof of Lemma 3.5, p. 26):
`V†V = I`. -/
def IsIsometry {ι κ : Type} [Fintype κ] [DecidableEq ι] (V : Matrix κ ι ℂ) : Prop :=
  Vᴴ * V = 1

end FlexRigidity


