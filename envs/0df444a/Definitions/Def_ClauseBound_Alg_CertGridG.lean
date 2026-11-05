-- Prove2me | Definitions.Def_ClauseBound_Alg_CertGridG
-- name    : ClauseBound_Alg_CertGridG
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:10:18.811207+00:00
-- url     : https://prove2.me/theorems/1d27f4c3-4988-48c1-be8a-cf0faf7106dc
-- title:
--   Cert Grid G
-- statement:
--   Definitions and structural lemmas for Cert Grid G, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]
section Step
variable {s : α → Step} (hs : PolyT s)
include hs
end Step
section Pieces
variable {P : PiecesF} (K : P.Keeps)
include K
def rectG (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ) (q : FQ) (i i' : ℕ) : ℤ :=
  (if q.1.1 < q.1.2 then P.top else P.bot) ((pad, tr),
    (h, digG P d tr h ℓ y (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2)) (tri i i')),
    (heG p d ℓ q.2.1 i (nodeG d tr q.1.2 i'), heG p d ℓ q.2.1 i' (nodeG d tr q.1.2 i),
     chunkAt (lenG P d tr h ℓ y (tri (min q.1.1 q.1.2) (max q.1.1 q.1.2))) (tri i i') (q.2.2.drop (nMemb p d tr * ℓ))))
end Pieces
end ClauseBound.Alg.CertGridG


