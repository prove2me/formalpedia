-- Prove2me | Definitions.Def_Eight_SecCrossing_Identity
-- name    : Eight_SecCrossing_Identity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:27:57.869515+00:00
-- url     : https://prove2.me/theorems/7c667644-afea-498d-a78b-678ea89035e5
-- title:
--   Sec Crossing Identity
-- statement:
--   Definitions and structural lemmas for Sec Crossing Identity, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
section
@[expose] section
namespace Eight
open Finset
@[expose] def lin1 (p : Block) : ℕ := p.1.toNat + p.2.1.toNat * p.2.2.toNat
@[expose, inherit_doc lin1] def lin2 (p : Block) : ℕ := p.1.toNat + p.2.1.toNat + p.1.toNat * p.2.2.toNat
@[expose, inherit_doc lin1] def lin3 (p : Block) : ℕ := p.1.toNat + p.2.1.toNat + p.2.2.toNat + p.1.toNat * p.2.1.toNat
@[expose] def phiQ (p q : Block) : ℕ :=
  p.1.toNat * q.1.toNat + p.1.toNat * q.2.1.toNat + p.1.toNat * q.2.2.toNat + p.2.1.toNat * q.2.1.toNat + p.2.1.toNat * q.2.2.toNat
    + p.2.2.toNat * q.2.2.toNat
@[expose] def phi1 (p q : Block) : ℕ := q.1.toNat * p.2.1.toNat * p.2.2.toNat
@[expose, inherit_doc phi1] def phi2 (p q : Block) : ℕ := p.1.toNat * q.2.1.toNat * p.2.2.toNat
@[expose, inherit_doc phi1] def phi3 (p q : Block) : ℕ := p.1.toNat * p.2.1.toNat * q.2.2.toNat
@[expose] def chg1 (p d : Block) : ℕ := d.1.toNat * (p.2.1.toNat * d.2.2.toNat + d.2.1.toNat * p.2.2.toNat + d.2.1.toNat * d.2.2.toNat)
@[expose, inherit_doc chg1] def chg2 (p d : Block) : ℕ := d.2.1.toNat * (p.1.toNat * d.2.2.toNat + d.1.toNat * p.2.2.toNat + d.1.toNat * d.2.2.toNat)
@[expose, inherit_doc chg1] def chg3 (p d : Block) : ℕ := d.2.2.toNat * (p.1.toNat * d.2.1.toNat + d.1.toNat * p.2.1.toNat + d.1.toNat * d.2.1.toNat)
variable {S : Type} [CommRing S]
end Eight


