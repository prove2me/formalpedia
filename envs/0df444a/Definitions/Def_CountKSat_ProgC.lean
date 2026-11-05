-- Prove2me | Definitions.Def_CountKSat_ProgC
-- name    : CountKSat_ProgC
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:45:12.255772+00:00
-- url     : https://prove2.me/theorems/97510579-4075-48d9-9da5-21cdf5214d6b
-- title:
--   Prog C
-- statement:
--   Definitions and structural lemmas for Prog C, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Ring
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
namespace ProgC
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}
def SideOK (n k : ℕ) (X : PFml) (p : ℕ) : Prop :=
  X.length ≤ n + k * p ∧ (∀ C ∈ X, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ taut n, C ∈ X
def GC (Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop) (ψ : PFml) (n k : ℕ) (x : CNode) (p t : ℕ) : Prop :=
  ProgMain.G Node ψ x.1 p t ∧ SideOK n k x.2 p
end ProgC
end CountKSat


