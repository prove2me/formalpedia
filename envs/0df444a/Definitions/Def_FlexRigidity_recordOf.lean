-- Prove2me | Definitions.Def_FlexRigidity_recordOf
-- name    : FlexRigidity_recordOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:18.71576+00:00
-- url     : https://prove2.me/theorems/a0fe9a3c-7291-46ff-8884-6a91609bdf09
-- title:
--   The score record $c_i=g(u_i,x_i,y_i,a_i,b_i)$
-- statement:
--   $c_i=\mathrm{gen}$ on a generation round and $c_i=V(x_i,y_i,a_i,b_i)\in\{0,1\}$ on a test round. The alphabet $C=\{\mathrm{gen},0,1\}$ is encoded as `Option Bool` (`none` = gen).
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), p. 44

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Game
import Definitions.Def_FlexRigidity_RoundO
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The record `c_i = g(u_i, x_i, y_i, a_i, b_i)`** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 44): `gen` in a generation round and
`V(x_i, y_i, a_i, b_i)` in a test round. The record alphabet `C = {gen, 0, 1}` is `Option Bool`:
`none` is `gen`, `some true` is `1`, `some false` is `0`.

**Formalization Note** Records `(true, x, none, a, _)` or `(true, x, _, a, none)` never occur
(their blocks are zero); they are sent to `gen`. -/
def recordOf {X Y A B : Type} (G : Game X Y A B) (o : RoundO X Y A B) : Option Bool :=
  match o with
  | (true, x, some y, a, some b) => some (G.V x y a b)
  | _ => none

end FlexRigidity


