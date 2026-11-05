-- Prove2me | Definitions.Def_StepSparsify_CertWalk
-- name    : StepSparsify_CertWalk
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:22:28.017199+00:00
-- url     : https://prove2.me/theorems/aa8ee4ec-b83c-4e6e-8e6d-fc2130c127ce
-- title:
--   Cert Walk
-- statement:
--   Definitions and structural lemmas for Cert Walk, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CertWalk.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_CountKSatRate_Cert
set_option autoImplicit false
section
section
@[expose] section
namespace StepSparsify
open Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert UniformInK SparsificationLemma
end StepSparsify


