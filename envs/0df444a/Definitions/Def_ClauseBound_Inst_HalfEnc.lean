-- Prove2me | Definitions.Def_ClauseBound_Inst_HalfEnc
-- name    : ClauseBound_Inst_HalfEnc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:43:48.1812+00:00
-- url     : https://prove2.me/theorems/c463117b-9b00-4d63-8d6e-b89397c4ce03
-- title:
--   Half Enc
-- statement:
--   Definitions and structural lemmas for Half Enc, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Theorems.Thm_ClauseBound_Inst_Half_length_allTab_getD
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_ofWord_lt
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Inst.Half
open Groundwork ClauseBound.Alg
variable {lam h W : ℕ}
theorem ofWord_bitsOf_lt (x : Pieces.Bits lam) : ofWord (bitsOf x) < 2 ^ lam := by
  have h1 := ofWord_lt (bitsOf x)
  rwa [bitsOf, List.length_ofFn] at h1
theorem ofWord_bitsOf_lt_length (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    ofWord (bitsOf x) < ((allTab W).getD h []).length := by
  rw [length_allTab_getD hW]
  exact (ofWord_bitsOf_lt x).trans_le hp
end ClauseBound.Inst.Half


