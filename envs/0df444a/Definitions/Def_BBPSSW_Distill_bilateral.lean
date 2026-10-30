-- Prove2me | Definitions.Def_BBPSSW_Distill_bilateral
-- name    : BBPSSW_Distill_bilateral
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:07.392998+00:00
-- url     : https://prove2.me/theorems/ec9cd5f0-5c99-4666-bfb8-dfb9cce38ea8
-- title:
--   Bilateral operation $U\otimes U$
-- statement:
--   For a one-spin operator $U$ (a $2\times2$ complex matrix), its bilateral application to a pair is $U\otimes U$: Alice applies $U$ to her particle and Bob applies the same $U$ to his.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 2 ("applying it locally to both members of the pair"; bilateral rotations)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

open QAlgorithms.Papers.Independent.Information100.P21 (QQ)

namespace BBPSSW.Distill

/-- **Bilateral application `U ⊗ U` of a one-spin operator.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 2: "a random bilateral rotation on each shared pair, choosing a random SU(2) rotation
… and applying it locally to both members of the pair", and the bilateral rotations Bx, By, Bz.

`bilateral U = U ⊗ U` acting on a pair indexed by (Alice's spin, Bob's spin). -/
def bilateral (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix QQ QQ ℂ :=
  Matrix.kronecker U U

end BBPSSW.Distill


