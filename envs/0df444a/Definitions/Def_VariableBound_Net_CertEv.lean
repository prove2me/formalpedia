-- Prove2me | Definitions.Def_VariableBound_Net_CertEv
-- name    : VariableBound_Net_CertEv
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:05:36.870918+00:00
-- url     : https://prove2.me/theorems/fa0f1ec7-14e5-41a2-b401-6bf7d80444be
-- title:
--   Cert Ev
-- statement:
--   Definitions and structural lemmas for Cert Ev, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertEv.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_PaddedDescent_F_CertEval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Theorems.Thm_PaddedDescent_F_Mark_Cert_qv_unary
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.qv_unary


set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Net.CertEv
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertEval ClauseBound.Alg ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
open PaddedDescent.F.Mark (qv nProf)
open PaddedDescent.F.Mark.Cert (qv_unary)
variable {α : Type} [Enc α]
end VariableBound.Net.CertEv
namespace VariableBound.Net
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.CertPar VariableBound.Net.CertEv
end VariableBound.Net


