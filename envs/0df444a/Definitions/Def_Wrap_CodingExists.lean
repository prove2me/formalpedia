-- Prove2me | Definitions.Def_Wrap_CodingExists
-- name    : Wrap_CodingExists
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:26:59.470138+00:00
-- url     : https://prove2.me/theorems/1389710d-d165-422d-bfec-758f7ca99db3
-- title:
--   Coding Exists
-- statement:
--   Definitions and structural lemmas for Coding Exists, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Data.Finite.Sigma
import Mathlib.Tactic.Linarith
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
@[expose] section
namespace Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
noncomputable def num {α : Type} [Finite α] (x : α) : ℕ := (Finite.equivFin α x).val
variable (M : TM2ComputableAux Bool Bool)
noncomputable def ks : List M.tm.K := Finset.univ.toList
theorem mem_ks (k : M.tm.K) : k ∈ ks M := Finset.mem_toList.2 (Finset.mem_univ k)
def top (c : M.tm.Cfg) : M.tm.Cfg := ⟨c.l, c.var, fun k => (c.stk k).take (dep M)⟩
variable [∀ i, Finite (M.tm.Γ i)]
noncomputable def sym (k : M.tm.K) (x : M.tm.Γ k) : ℕ := num (⟨k, x⟩ : Σ k, M.tm.Γ k)
noncomputable def bnd : ℕ := Nat.size (Nat.card (Option M.tm.Λ) + Nat.card M.tm.σ + Nat.card (Σ k, M.tm.Γ k)) + 1
noncomputable def repOf (c : M.tm.Cfg) : Rep :=
  ((num c.l, num c.var), (ks M).map fun k => (c.stk k).map (sym M k))
def key (d : ℕ) (r : Rep) : Rep := (r.1, r.2.map fun l => l.take d)
noncomputable def keys : List Rep :=
  (Finite.exists_univ_list (Case M)).choose.map fun γ => repOf M ⟨γ.1, γ.2.1, fun k => pref (List.ofFn (γ.2.2 k))⟩
noncomputable def entry (r : Rep) : Rep := repOf M (stay M (Function.invFun (repOf M) r))
noncomputable def tab (r : Rep) : Rep := PolyT.lookup (entry M) ((0, 0), []) (keys M) r
noncomputable def stepOf (r : Rep) : Rep :=
  ((tab M (key (dep M) r)).1, ((tab M (key (dep M) r)).2.zip (r.2.map fun l => l.drop (dep M))).map fun p => p.1 ++ p.2)
noncomputable def inSym (b : Bool) : ℕ := sym M M.tm.k₀ (M.inputAlphabet.invFun b)
noncomputable def initOf (x : List Bool) : Rep :=
  ((num (some M.tm.main), num M.tm.initialState),
    (ks M).map fun k => if k = M.tm.k₀ then x.map (inSym M) else [])
noncomputable def outIdx : ℕ := (List.mem_iff_getElem?.1 (mem_ks M M.tm.k₁)).choose
noncomputable def bitOf (n : ℕ) : Bool :=
  haveI : Nonempty (M.tm.Γ M.tm.k₁) := ⟨M.outputAlphabet.symm false⟩
  PolyT.lookup (fun n => M.outputAlphabet (Function.invFun (sym M M.tm.k₁) n)) false (List.range (Nat.card (Σ k, M.tm.Γ k))) n
noncomputable def outOf (r : Rep) : Option (List Bool) :=
  if r.1.1 = num (none : Option M.tm.Λ) then some ((r.2.getD (outIdx M) []).map fun n => bitOf M n) else none
end Wrap.Conf
namespace Wrap
open Turing Groundwork CircuitLowerBound.Tab Conf
end Wrap


