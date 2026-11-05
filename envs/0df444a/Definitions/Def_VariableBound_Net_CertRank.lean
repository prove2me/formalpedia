-- Prove2me | Definitions.Def_VariableBound_Net_CertRank
-- name    : VariableBound_Net_CertRank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:07:17.270626+00:00
-- url     : https://prove2.me/theorems/cea3c150-69d6-4395-9e4c-a52e8ead1403
-- title:
--   Cert Rank
-- statement:
--   Definitions and structural lemmas for Cert Rank, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertRank.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Rank
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Net
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
namespace CertRank
def stepR (b : Bool) (c : List Bool × ℕ) : List Bool × ℕ := (b :: c.1, (bif b then c.1.length.choose (c.1.count true + 1) else 0) + c.2)
end CertRank
open CertRank
end VariableBound.Net


