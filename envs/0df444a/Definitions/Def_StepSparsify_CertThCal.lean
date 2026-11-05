-- Prove2me | Definitions.Def_StepSparsify_CertThCal
-- name    : StepSparsify_CertThCal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:25:10.942394+00:00
-- url     : https://prove2.me/theorems/30c56807-dc50-4ddd-8344-1376764065b6
-- title:
--   Cert Th Cal
-- statement:
--   Definitions and structural lemmas for Cert Th Cal, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CertThCal.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Mathlib.Data.Nat.Choose.Central
set_option autoImplicit false
section
section
@[expose] section
namespace StepSparsify.CertThCal
open Groundwork SparsificationLemma ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
end StepSparsify.CertThCal


