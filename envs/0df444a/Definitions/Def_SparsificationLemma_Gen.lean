-- Prove2me | Definitions.Def_SparsificationLemma_Gen
-- name    : SparsificationLemma_Gen
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:15:18.777457+00:00
-- url     : https://prove2.me/theorems/901227af-8081-414e-9c6f-cf9b68729c7c
-- title:
--   Gen
-- statement:
--   Definitions and structural lemmas for Gen, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Gen.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_SparsificationLemma_Iface
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
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
@[expose] section
namespace SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)
namespace Gen
variable {k τ n D : ℕ} {θ β : ℕ → ℕ} {ψ : PFml}
def InvL (θ : ℕ → ℕ) (k τ n : ℕ) (ψ : PFml) (x : CNode) (p t : ℕ) : Prop :=
  CountKSatRate.Tree.GT (fun F₀ F p t => ProgMain.Ok k n F₀ ∧ NodeU θ k τ F₀ F p t) ψ n k τ x p t ∧ x.1.length ≤ ψ.length
end Gen
end SparsificationLemma


