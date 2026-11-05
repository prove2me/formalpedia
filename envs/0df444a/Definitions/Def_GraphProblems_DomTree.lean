-- Prove2me | Definitions.Def_GraphProblems_DomTree
-- name    : GraphProblems_DomTree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:35:06.466382+00:00
-- url     : https://prove2.me/theorems/98ea20b2-6d15-448e-b81c-dd1272cdafa7
-- title:
--   Dom Tree
-- statement:
--   Definitions and structural lemmas for Dom Tree, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
namespace GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}
def Hit (a : Fin n → Bool) (D : List ℕ) : Prop := ∃ u ∈ D, ext a u = true
def Sat (a : Fin n → Bool) (ψ : Fml) : Prop := ∀ C ∈ ψ, ∃ l ∈ C, ext a l.1 = l.2
def Inv (n s w : ℕ) (x : DNode) (p t : ℕ) : Prop :=
  x.1 = (List.replicate n (), s) ∧ ∃ (a : ℕ) (V : Finset ℕ), a + x.2.1.length ≤ n ∧ p ≤ a + t ∧ t + #V ≤ n ∧ (∀ u ∈ V, u < n) ∧
    (∀ D ∈ x.2.1, D.Nodup ∧ ∀ u ∈ D, u ∈ V) ∧ x.2.2.length ≤ a + t ∧ Shaped w n x.2.2
end GraphProblems.DomTree
namespace GraphProblems
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset DomTree
end GraphProblems


