-- Prove2me | Definitions.Def_OccurM_Prep
-- name    : OccurM_Prep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:37:45.330194+00:00
-- url     : https://prove2.me/theorems/c5d28226-26b6-416d-8d96-f4c65427644e
-- title:
--   Prep
-- statement:
--   Definitions and structural lemmas for Prep, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Prep.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Mathlib.SetTheory.Cardinal.Finite
set_option autoImplicit false
section
section
@[expose] section
namespace OccurM
open Groundwork MainTheoremForms ClausesOccur VariableBound.Rename
open Sat3 (CNF)
end OccurM
namespace ClausesOccur
open MainTheoremForms
open Sat3 (CNF)
end ClausesOccur


