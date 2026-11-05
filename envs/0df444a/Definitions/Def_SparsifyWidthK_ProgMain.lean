-- Prove2me | Definitions.Def_SparsifyWidthK_ProgMain
-- name    : SparsifyWidthK_ProgMain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:33:33.668196+00:00
-- url     : https://prove2.me/theorems/2083fb71-952f-4bc7-831c-4e6dc79d9971
-- title:
--   Prog Main
-- statement:
--   Definitions and structural lemmas for Prog Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
set_option autoImplicit false
section
section
namespace WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
section asm
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}
def G (Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop) (ψ s : PFml) (p t : ℕ) : Prop :=
  NF s ∧ Node (toFin ψ) (toFin s) p t
end asm
def litsBelow (n : ℕ) : Finset PLit := Finset.range n ×ˢ (Finset.univ : Finset Bool)
def Ok (k n : ℕ) (F₀ : Finset (Finset PLit)) : Prop := ∀ C ∈ F₀, C ⊆ litsBelow n ∧ C.Nonempty ∧ C.card ≤ k
end WidthK.ProgMain
namespace WidthK
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
end WidthK


