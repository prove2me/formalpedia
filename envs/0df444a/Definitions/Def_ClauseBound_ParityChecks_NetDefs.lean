-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_NetDefs
-- name    : ClauseBound_ParityChecks_NetDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:59:46.408199+00:00
-- url     : https://prove2.me/theorems/d877b0b2-64aa-40ea-89e5-17cc0e7a51c5
-- title:
--   Net Defs
-- statement:
--   Definitions and structural lemmas for Net Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/NetDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_EvalW
import Definitions.Def_ParityChecksStatement
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace ClauseBound.ParityChecks
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.TopN.EvalW
def incL (n : ℕ) (ψ : Fml) (Lam : List (List ℕ)) (j : ℕ) : Fml :=
  ((List.range j).flatMap fun j' => (Lam.getD j' []).map fun e => ψ.getD e [] ++ [(n + j', false)]) ++
    (Lam.getD j []).map fun e => ψ.getD e []
def sumB (n r nb M i : ℕ) (ψ : Fml) (Lam : List (List ℕ)) (j t : ℕ) : ℤ :=
  truncW (n + r) [1, -2, 1] [nb + 1, 0, i] [nb + 1, M, i] [ψ, incL n ψ Lam j, ψ.drop t]
def sumA (n r nb M : ℕ) (ψ : Fml) (Lam : List (List ℕ)) (j : ℕ) : ℤ :=
  truncW (n + r) [1, -2] [nb + 1, 0] [nb + 1, M] [ψ, incL n ψ (Lam.take j) j]
def sumF3 (n r nb M : ℕ) (ψ : Fml) (Lam : List (List ℕ)) : ℤ :=
  truncW (n + r) [-1, -2] [0, 0] [nb, M] [ψ, incL n ψ (Lam.take r) r]
def Vof {n : ℕ} (ψ : Fml) (ξ : Fin n → Bool) : Finset (Fin ψ.length) := Finset.univ.filter fun e => vio (Mark.ext ξ) (ψ.getD e.val []) = true
def Lof (ψ : Fml) (Lam : List (List ℕ)) (j : ℕ) : Finset (Fin ψ.length) := Finset.univ.filter fun e => e.val ∈ Lam.getD j []
def Dof (ψ : Fml) (t : ℕ) : Finset (Fin ψ.length) := Finset.univ.filter fun e => t ≤ e.val
def WfC (ψ : Fml) (r : ℕ) (Lam : List (List ℕ)) : Prop := Lam.length = r ∧ ∀ L ∈ Lam, L.Nodup ∧ ∀ e ∈ L, e < ψ.length
def StBridgeB : Prop := ∀ (n r nb M i j t : ℕ) (ψ : Fml) (Lam : List (List ℕ)), (∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) → WfC ψ r Lam → j < r →
  sumB n r nb M i ψ Lam j t ≡ 2 ^ r * _root_.ParityChecks.Bint (Vof (n := n) ψ) nb i j (Lof ψ Lam) (Dof ψ t) [ZMOD 2 ^ (M + 1)]
def StBridgeA : Prop := ∀ (n r nb M j : ℕ) (ψ : Fml) (Lam : List (List ℕ)), (∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) → WfC ψ r Lam → j ≤ r →
  sumA n r nb M ψ Lam j ≡ 2 ^ r * _root_.ParityChecks.Aint (Vof (n := n) ψ) nb j (Lof ψ Lam) [ZMOD 2 ^ (M + 1)]
def StBridgeF : Prop := ∀ (n r nb M : ℕ) (ψ : Fml) (Lam : List (List ℕ)), (∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) → WfC ψ r Lam →
  _root_.ParityChecks.Good (Vof (n := n) ψ) nb r (Lof ψ Lam) →
  sumF3 n r nb M ψ Lam ≡ 2 ^ r * (nSat n ψ : ℤ) [ZMOD 2 ^ (M + 1)]
end ClauseBound.ParityChecks


