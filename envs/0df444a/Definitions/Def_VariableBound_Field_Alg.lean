-- Prove2me | Definitions.Def_VariableBound_Field_Alg
-- name    : VariableBound_Field_Alg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:46:52.092824+00:00
-- url     : https://prove2.me/theorems/59834862-70a2-4c6a-b55f-fbc21b860093
-- title:
--   Alg
-- statement:
--   Definitions and structural lemmas for Alg, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Alg.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Mathlib.RingTheory.AdjoinRoot
set_option autoImplicit false
section
section
namespace VariableBound.Fld
open Polynomial
def bitR (R : Type) [CommRing R] (b : Bool) : R := if b then 1 else 0
def decR {R : Type} [CommRing R] (r : R) : List Bool → R
  | [] => 0
  | b :: w => bitR R b + r * decR r w
noncomputable def polyW (w : List Bool) : (ZMod 2)[X] := decR X w
noncomputable def modP (g : List Bool) : (ZMod 2)[X] := X ^ g.length + polyW g
abbrev FW (g : List Bool) : Type := AdjoinRoot (modP g)
noncomputable def decW (g w : List Bool) : FW g := decR (AdjoinRoot.root (modP g)) w
end VariableBound.Fld


