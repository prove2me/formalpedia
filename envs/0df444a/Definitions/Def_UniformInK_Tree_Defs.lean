-- Prove2me | Definitions.Def_UniformInK_Tree_Defs
-- name    : UniformInK_Tree_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:48:42.549064+00:00
-- url     : https://prove2.me/theorems/bf9a1e1e-34e5-42a3-a100-d452379649e2
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Tree/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_ClauseBound_TopN_Defs
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace UniformInK
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F CountKSatRate
open PaddedDescent.F.Mark (occ)
def stackLenCU (k τ n m : ℕ) : ℕ :=
  (bsumU τ k * n + 1) * (2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8) + 3 * n + 16
def StTreeU : Prop := ∀ (k τ n : ℕ), 1 ≤ k → k ^ 2 ≤ τ → 8 * k ≤ τ → ∀ ψ : PFml, (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
  (leaves (stepC (thetaU τ) k) (bsumU τ k * n) (rootC (List.replicate n (), ψ))).length ≤ ∑ j ∈ range (k * n / τ + 1), (bsumU τ k * n).choose j ∧
  (∀ x ∈ leaves (stepC (thetaU τ) k) (bsumU τ k * n) (rootC (List.replicate n (), ψ)),
    stepC (thetaU τ) k x = none ∧ (leafF x).length ≤ (leafCU τ k + 2) * n ∧
      (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ v, (occ x.1 v).length ≤ leafCU τ k) ∧
      ∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) ∧
  cntN n ψ = ((leaves (stepC (thetaU τ) k) (bsumU τ k * n) (rootC (List.replicate n (), ψ))).map fun x => cntN n (leafF x)).sum ∧
  ∀ i, ((round (stepC (thetaU τ) k))^[i] ([rootC (List.replicate n (), ψ)], [])).1.length ≤ bsumU τ k * n + 1 ∧
    ∀ x ∈ ((round (stepC (thetaU τ) k))^[i] ([rootC (List.replicate n (), ψ)], [])).1,
      x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n
def StStateLenU : Prop := ∀ (k τ n m c : ℕ) (st : List CNode), st.length ≤ bsumU τ k * n + 1 →
  (∀ x ∈ st, x.1.length ≤ m * 2 ^ k ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n) →
  c < 2 ^ (n + 1) → len (st, c) ≤ stackLenCU k τ n m
end UniformInK


