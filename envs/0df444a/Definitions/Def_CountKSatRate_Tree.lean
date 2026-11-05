-- Prove2me | Definitions.Def_CountKSatRate_Tree
-- name    : CountKSatRate_Tree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:29:57.065121+00:00
-- url     : https://prove2.me/theorems/a372d086-8725-4808-9d86-39e9b9748778
-- title:
--   Tree
-- statement:
--   Definitions and structural lemmas for Tree, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Tree.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace CountKSatRate
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat WidthK.Prog
open WidthK (theta bsum leafC Iface Refines)
namespace Tree
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}
def SideT (n k q : ℕ) (X : PFml) (t : ℕ) : Prop :=
  X.length * q ≤ n * q + k * t ∧ (∀ C ∈ X, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ C ∈ taut n, C ∈ X) ∧ ∀ C ∈ X, C ∈ taut n ∨ ∃ l, C = [l]
def GT (Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop) (ψ : PFml) (n k q : ℕ) (x : CNode) (p t : ℕ) : Prop :=
  WidthK.ProgMain.G Node ψ x.1 p t ∧ SideT n k q x.2 t
end Tree
end CountKSatRate


