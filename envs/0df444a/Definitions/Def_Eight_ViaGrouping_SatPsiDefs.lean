-- Prove2me | Definitions.Def_Eight_ViaGrouping_SatPsiDefs
-- name    : Eight_ViaGrouping_SatPsiDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:53:35.409514+00:00
-- url     : https://prove2.me/theorems/8395a4a5-1b54-4ee4-b45d-13105a190e32
-- title:
--   Sat Psi Defs
-- statement:
--   Definitions and structural lemmas for Sat Psi Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsiDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecProof_NetworkDefs
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks
def restr (g k : ℕ) (Φ : Fml) (a b : ℕ) (z : List Bool) : List Bool :=
  if a < b then (links g k Φ a b).map fun p => z.getD p.1 false else (links g k Φ b a).map fun p => z.getD p.2 false
def satPsi (g k : ℕ) (Φ : Fml) (q : PsiQ) : ℤ := if restr g k Φ q.1.1 q.1.2 q.2.1 = restr g k Φ q.1.2 q.1.1 q.2.2 then 1 else 0
def satPsiM (g k : ℕ) : Stepped (Fml × PsiQ) ℤ := Stepped.ofFun fun x => satPsi g k x.1 x.2
def satPf (g k : ℕ) (Φ : Fml) : ℕ := max 1 (2 * k * mu g Φ)
def satProcs (g k : ℕ) : Procs Fml := ofProcs (satP g k) (satPf g k) (satPsiM g k)
def satNet (g k : ℕ) (Φ : Fml) : Net g := ofNetwork (wordNet g k Φ) fun _ => mu g Φ * k
end Eight.ViaGrouping


