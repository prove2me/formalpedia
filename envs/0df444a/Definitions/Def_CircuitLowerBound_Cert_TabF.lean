-- Prove2me | Definitions.Def_CircuitLowerBound_Cert_TabF
-- name    : CircuitLowerBound_Cert_TabF
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:29:39.350095+00:00
-- url     : https://prove2.me/theorems/8f68cd3c-e94e-47c5-ba78-ec1abf09c0bd
-- title:
--   Tab F
-- statement:
--   Definitions and structural lemmas for Tab F, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
@[expose] section
namespace CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]
@[expose] def clipE (e : MCode) (L : ℕ) : MCode := (min (kb e) L, min (lam e) L, tab e)
section
variable {e : α → MCode} {L P : α → ℕ} (he : PolyT e) (hk : Unary fun x => kb (e x)) (hl : Unary fun x => lam (e x)) (hL : Unary L) (hP : PolyT P)
include he hk hl hL
include hP
end
@[expose] def G (p : (MCode × List Unit × ℕ) × List Unit) : Cnf :=
  (List.range (min (2 ^ nb (clipE p.1.1 p.1.2.1.length) p.1.2.1.length) p.2.length)).map
    (clauseAt (clipE p.1.1 p.1.2.1.length) p.1.2.1.length p.1.2.2)
@[expose] def tryAll (N : ℕ) (φ : Cnf) : Bool := (List.range N).any fun α => φ.all fun D => D.any fun l => α.testBit l.1 == l.2
@[expose] def fb (u : List Unit) : Bool :=
  decide (Fits (codeOf (nu u.length)) (min (2 ^ nu u.length) u.length) (2 ^ nu u.length)) &&
    tryAll (pos u.length)
      (G ((codeOf (nu u.length), List.replicate (min (2 ^ nu u.length) u.length) (), 2 ^ nu u.length), List.replicate ((2 * u.length + 1) * u.length) ()))
end CircuitLowerBound.TabF
namespace CircuitLowerBound
open ENP Groundwork TabF
end CircuitLowerBound


