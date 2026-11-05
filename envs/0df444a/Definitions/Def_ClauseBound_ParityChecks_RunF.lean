-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_RunF
-- name    : ClauseBound_ParityChecks_RunF
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:06:18.495652+00:00
-- url     : https://prove2.me/theorems/f4beeea7-a8a5-46e0-80de-0c8a4b1bb69e
-- title:
--   Run F
-- statement:
--   Definitions and structural lemmas for Run F, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
@[expose] def runToC (Ls : List Chk) (e : ℕ) : Chk := (List.range e).foldl (fun cur x => cap pad [] (q.decide1 oA oB Ls cur x)) (cap pad [] [])
@[expose] def runC : List Chk := (List.range q.r).foldl (fun Ls _ => cap pad [] (Ls ++ [runToC pad q oA oB Ls q.m])) (cap pad [] [])
@[expose] def lenChk (m : ℕ) : ℕ := m * (3 * Nat.size m + 4) + 2
variable {pad q oA oB}
variable {Idx : Type} [Enc Idx] (S : Solver Idx) (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (q : Par) (ψ : Fml)
end ClauseBound.ParityChecks.RunF


