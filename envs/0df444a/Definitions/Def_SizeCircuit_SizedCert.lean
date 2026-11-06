-- Prove2me | Definitions.Def_SizeCircuit_SizedCert
-- name    : SizeCircuit_SizedCert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:31:19.735586+00:00
-- url     : https://prove2.me/theorems/eb6f3345-56fe-44f7-ad7d-dc8758a6b582
-- title:
--   Sized Cert
-- statement:
--   Definitions and structural lemmas for Sized Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/SizedCert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight
end SizeCircuit


