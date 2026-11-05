-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_CertLib
-- name    : ClauseBound_ParityChecks_CertLib
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:11:08.953858+00:00
-- url     : https://prove2.me/theorems/0730efb5-e32b-4a85-b8d3-fe4b5c988353
-- title:
--   Cert Lib
-- statement:
--   Definitions and structural lemmas for Cert Lib, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
structure QU (q : α → Par) : Prop where
  m : Unary fun x => (q x).m
  nb : Unary fun x => (q x).nb
  r : Unary fun x => (q x).r
  i₀ : Unary fun x => (q x).i₀
  β : Unary fun x => (q x).β
end ClauseBound.ParityChecks.CertLib


