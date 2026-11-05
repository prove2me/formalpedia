-- Prove2me | Definitions.Def_ThmVariables_EveryMachine
-- name    : ThmVariables_EveryMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:56:02.829089+00:00
-- url     : https://prove2.me/theorems/598b597a-2a92-4635-89cd-91428b739770
-- title:
--   Every Machine
-- statement:
--   Definitions and structural lemmas for Every Machine, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/EveryMachine.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_ThmVariables_Bound
import Definitions.Def_ThmVariables_PartA
set_option autoImplicit false
section
section
@[expose] section
namespace ThmVariables
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms
end ThmVariables


