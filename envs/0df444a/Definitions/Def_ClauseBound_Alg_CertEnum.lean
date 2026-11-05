-- Prove2me | Definitions.Def_ClauseBound_Alg_CertEnum
-- name    : ClauseBound_Alg_CertEnum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:41:45.736581+00:00
-- url     : https://prove2.me/theorems/bbdfebff-0bb8-44d1-bcb8-1292b921f8ba
-- title:
--   Cert Enum
-- statement:
--   Definitions and structural lemmas for Cert Enum, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Alg.CertEnum
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertNet
variable {α : Type} [Enc α] {C : Type} [Enc C] {F : FNet C}
def chunkCut (g : ℕ) (F : FNet C) (c : C) (j : ℕ) (w : List Bool) : List Bool :=
  (w.drop ((List.range (min j (g * g))).map (enumLen g F c)).sum).take (enumLen g F c j)
def enumCut (pad : U) (g : ℕ) (F : FNet C) (c : C) : ℤ :=
  sumF (2 ^ enumBits g F c) pad fun t =>
    prodL g fun a => sumF (2 ^ F.n c a) pad fun zi =>
      F.W (c, (a, toWord (F.n c a) zi)) * prodL g fun b =>
        if b = a then 1
        else F.f (c, ((a, b), (toWord (F.n c a) zi, chunkCut g F c (min a b * g + max a b) (toWord (enumBits g F c) t))))
end ClauseBound.Alg.CertEnum


