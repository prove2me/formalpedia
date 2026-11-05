-- Prove2me | Definitions.Def_VariableBound_Search_Defs
-- name    : VariableBound_Search_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:47:18.946205+00:00
-- url     : https://prove2.me/theorems/83c05f35-2eb5-4336-89a3-4374d5c2375a
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Definitions.Def_VariableBound_Field_Defs
import Definitions.Def_PaddedDescent_F_Fuel
import Theorems.Thm_Groundwork_PolyT_contains
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.contains
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace VariableBound
open Groundwork PaddedDescent.F AppVariables
def chksD (m : ℕ) (L : List (List ℕ)) : List (Finset (Fin m)) := L.map (Fld.setD m)
def loadSum (m : ℕ) (L : List (List ℕ)) : ℕ := ((List.range m).map fun E => 2 ^ (L.filter fun l => l.contains E).length).sum
def upsNum (m nb β rb tb : ℕ) (x : ℤ) (L : List (List ℕ)) : ℤ :=
  4 ^ L.length * 2 ^ tb * (15 * nb) ^ (rb - L.length) * x + 3 ^ L.length * 2 ^ (β - 1) * (15 * nb + 16) ^ (rb - L.length) * loadSum m L
def argminD (key : List ℕ → ℤ) (fam : List (List ℕ)) : List ℕ :=
  (fam.foldl (fun (best : Option (List ℕ × ℤ)) l => match best with
    | none => some (l, key l)
    | some b => if key l < b.2 then some (l, key l) else some b) none).elim [] fun b => b.1
def roundD (evX : List (List ℕ) → ℤ) (fam : List (List ℕ)) (m nb β rb tb : ℕ) (L : List (List ℕ)) : List (List ℕ) :=
  if evX L = 0 then L else L ++ [argminD (fun l => upsNum m nb β rb tb (evX (L ++ [l])) (L ++ [l])) fam]
def searchD (pad : U) (evX : List (List ℕ) → ℤ) (fam : List (List ℕ)) (m nb β rb tb : ℕ) : List (List ℕ) :=
  (List.range rb).foldl (fun L _ => cap pad [] (roundD evX fam m nb β rb tb L)) (cap pad [] [])
def StructD (m nb rb tb : ℕ) (L : List (List ℕ)) : Prop :=
  L.length ≤ rb ∧ (∀ l ∈ L, l.Pairwise (· < ·) ∧ (∀ E ∈ l, E < m) ∧ nb * l.length ≤ 16 * m) ∧ ∀ E < m, (L.filter fun l => l.contains E).length ≤ tb + 2
def StSearchD : Prop := ∀ (X : Type) [Fintype X] (m : ℕ) (V : X → Finset (Fin m)) (n nb rb tb : ℕ) (pad : U) (evX : List (List ℕ) → ℤ) (fam : List (List ℕ)),
  Fintype.card X ≤ 2 ^ n → 1 ≤ nb → IsRb (beta n m nb) rb → IsTb m nb rb tb →
  fam ≠ [] → (∀ l ∈ fam, l.Pairwise (· < ·) ∧ ∀ E ∈ l, E < m) →
  IsFamily nb (Finset.univ : Finset (Fin fam.length)) (fun i => Fld.setD m (fam.get i)) →
  (∀ L, StructD m nb rb tb L → evX L = Xsum V nb (chksD m L)) → (∀ L, StructD m nb rb tb L → len L ≤ pad.length) →
  StructD m nb rb tb (searchD pad evX fam m nb (beta n m nb) rb tb) ∧ Xsum V nb (chksD m (searchD pad evX fam m nb (beta n m nb) rb tb)) = 0
def StCertSearchD : Prop := ∀ (α : Type) [Enc α] (pad : α → U) (evX : α → List (List ℕ) → ℤ) (fam : α → List (List ℕ)) (m nb β rb tb : α → ℕ),
  PolyT pad → (PolyT fun p : α × List (List ℕ) => evX p.1 p.2) → PolyT fam → Unary m → Unary nb → Unary β → Unary rb → Unary tb →
  PolyT fun x => searchD (pad x) (evX x) (fam x) (m x) (nb x) (β x) (rb x) (tb x)
end VariableBound


