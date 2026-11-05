-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_BridgeInc
-- name    : ClauseBound_ParityChecks_BridgeInc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:01:06.463896+00:00
-- url     : https://prove2.me/theorems/a0c351f1-58d6-4f2f-975f-204abcd3f32e
-- title:
--   Bridge Inc
-- statement:
--   Definitions and structural lemmas for Bridge Inc, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
@[expose] section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
namespace ClauseBound.ParityChecks.BridgeInc
@[expose] def xi {n r : ℕ} (σ : Fin (n + r) → Bool) : Fin n → Bool := fun v => σ (Fin.castAdd r v)
@[expose] def yy {n r : ℕ} (σ : Fin (n + r) → Bool) : Fin r → Bool := fun j => σ (Fin.natAdd n j)
@[expose] def cnt (τ : ℕ → Bool) (ψ : Fml) (Lam : List (List ℕ)) (j : ℕ) : ℕ := (Lam.getD j []).countP fun e => vio τ (ψ.getD e [])
@[expose] def J1 (r j : ℕ) : Finset (Fin r) := univ.filter fun j' => j'.val < j
@[expose] def J2 (r j : ℕ) : Finset (Fin r) := univ.filter fun j' => j'.val = j
end ClauseBound.ParityChecks.BridgeInc


