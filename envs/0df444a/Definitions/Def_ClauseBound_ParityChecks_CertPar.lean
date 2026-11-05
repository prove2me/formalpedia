-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_CertPar
-- name    : ClauseBound_ParityChecks_CertPar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:03:27.197531+00:00
-- url     : https://prove2.me/theorems/272061c0-e79a-4393-b288-b7071307f6d9
-- title:
--   Cert Par
-- statement:
--   Definitions and structural lemmas for Cert Par, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks.CertPar
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
section
variable {q : α → Par} (hq : QU q)
include hq
end
end ClauseBound.ParityChecks.CertPar


