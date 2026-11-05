-- Prove2me | Definitions.Def_PaddedDescent_F_Price
-- name    : PaddedDescent_F_Price
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:06:06.103954+00:00
-- url     : https://prove2.me/theorems/1ee933a5-70c1-4663-beb7-6dfb6c6f7c8e
-- title:
--   Price
-- statement:
--   Definitions and structural lemmas for Price, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Price.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
set_option autoImplicit false
section
section
@[expose] section
set_option exponentiation.threshold 1024
namespace PaddedDescent.F.Price
open Groundwork Groundwork.Prog Groundwork.Grid
end PaddedDescent.F.Price


