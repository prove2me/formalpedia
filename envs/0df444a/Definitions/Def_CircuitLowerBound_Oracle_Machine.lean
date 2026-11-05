-- Prove2me | Definitions.Def_CircuitLowerBound_Oracle_Machine
-- name    : CircuitLowerBound_Oracle_Machine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:55:39.204218+00:00
-- url     : https://prove2.me/theorems/09253095-096d-4c71-ab58-b6acbf3f88a2
-- title:
--   Machine
-- statement:
--   Definitions and structural lemmas for Machine, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_TM_Run
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_TM_Run_one
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit


set_option autoImplicit false
section
section
namespace CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
inductive NS | io | ans | sp
  deriving DecidableEq
instance : Fintype NS := ⟨{.io, .ans, .sp}, fun x => by cases x <;> simp⟩
inductive Ctl | cpA | mvA | sep | mvX | cpX | after | ask | yes | no | drX | drA | fin
  deriving DecidableEq
instance : Fintype Ctl := ⟨{.cpA, .mvA, .sep, .mvX, .cpX, .after, .ask, .yes, .no, .drX, .drA, .fin}, fun x => by cases x <;> simp⟩
variable (M : TM2ComputableAux Bool Bool)
abbrev Γ' : M.tm.K ⊕ NS → Type
  | .inl k => M.tm.Γ k
  | .inr _ => Bool
abbrev Λ' : Type := M.tm.Λ ⊕ Ctl
abbrev σ' : Type := M.tm.σ × Option Bool
abbrev St : Type := TM2.Stmt (Γ' M) (Λ' M) (σ' M)
abbrev Cf : Type := TM2.Cfg (Γ' M) (Λ' M) (σ' M)
def lift : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ → St M
  | .push k f q => .push (.inl k) (fun v => f v.1) (lift q)
  | .peek k f q => .peek (.inl k) (fun v o => (f v.1 o, v.2)) (lift q)
  | .pop k f q => .pop (.inl k) (fun v o => (f v.1 o, v.2)) (lift q)
  | .load f q => .load (fun v => (f v.1, v.2)) (lift q)
  | .branch p q₁ q₂ => .branch (fun v => p v.1) (lift q₁) (lift q₂)
  | .goto l => .goto fun v => .inl (l v.1)
  | .halt => .goto fun _ => .inr .after
def mvS (s d : NS) (me nx : Λ' M) : St M :=
  .pop (.inr s) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2.isSome)
      (.push (.inr d) (fun v => v.2.getD false) <| .load (fun v => (v.1, none)) <| .goto fun _ => me)
      (.goto fun _ => nx)
def drS (s : NS) (me nx : Λ' M) : St M :=
  .pop (.inr s) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2.isSome) (.load (fun v => (v.1, none)) <| .goto fun _ => me) (.goto fun _ => nx)
def cpS (s d : NS) (mark : Bool) (me nx : Λ' M) : St M :=
  .pop (.inr s) (fun v o => (v.1, o)) <|
    .branch (fun v => v.2.isSome)
      (.push (.inr d) (fun v => v.2.getD false) <| .push (.inl M.tm.k₀) (fun v => M.inputAlphabet.invFun (v.2.getD false)) <|
        .branch (fun _ => mark)
          (.push (.inl M.tm.k₀) (fun _ => M.inputAlphabet.invFun true) <| .load (fun v => (v.1, none)) <| .goto fun _ => me)
          (.load (fun v => (v.1, none)) <| .goto fun _ => me))
      (.goto fun _ => nx)
def prog : Λ' M → St M
  | .inl l => lift M (M.tm.m l)
  | .inr .cpA => cpS M .ans .sp false (.inr .cpA) (.inr .mvA)
  | .inr .mvA => mvS M .sp .ans (.inr .mvA) (.inr .sep)
  | .inr .sep => .push (.inl M.tm.k₀) (fun _ => M.inputAlphabet.invFun false) <| .goto fun _ => .inr .mvX
  | .inr .mvX => mvS M .io .sp (.inr .mvX) (.inr .cpX)
  | .inr .cpX => cpS M .sp .io true (.inr .cpX) (.inl M.tm.main)
  | .inr .after => .pop (.inl M.tm.k₁) (fun v o => (v.1, o.map M.outputAlphabet)) <|
      .branch (fun v => v.2 == some true) (.load (fun v => (v.1, none)) <| .goto fun _ => .inr .ask)
        (.load (fun v => (v.1, none)) <| .goto fun _ => .inr .drX)
  | .inr .ask => .halt
  | .inr .yes => .push (.inr .ans) (fun _ => true) <| .goto fun _ => .inr .cpA
  | .inr .no => .push (.inr .ans) (fun _ => false) <| .goto fun _ => .inr .cpA
  | .inr .drX => drS M .io (.inr .drX) (.inr .drA)
  | .inr .drA => drS M .ans (.inr .drA) (.inr .fin)
  | .inr .fin => .pop (.inl M.tm.k₁) (fun v o => (v.1, o.map M.outputAlphabet)) <|
      .push (.inr .io) (fun v => v.2.getD false) <| .load (fun v => (v.1, none)) .halt
def tm' : FinTM2 where
  K := M.tm.K ⊕ NS
  kFin := by haveI := M.tm.kFin; infer_instance
  k₀ := .inr .io
  k₁ := .inr .io
  Γ := Γ' M
  Λ := Λ' M
  main := .inr .cpA
  ΛFin := by haveI := M.tm.ΛFin; infer_instance
  σ := σ' M
  initialState := (M.tm.initialState, none)
  σFin := by haveI := M.tm.σFin; infer_instance
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog M
def otm : OTM where
  tm := tm' M
  inp := Equiv.refl Bool
  out := Equiv.refl Bool
  q := .inl M.tm.k₁
  qry := M.outputAlphabet
  ask := .inr .ask
  yes := .inr .yes
  no := .inr .no
noncomputable def stp (O : Lang) : Cf M → Option (Cf M) := (otm M).step O
def stk (T : ∀ k, List (M.tm.Γ k)) (n : NS → List Bool) : ∀ k, List (Γ' M k)
  | .inl k => T k
  | .inr j => n j
variable {M}
def ns (a b c : List Bool) : NS → List Bool
  | .io => a
  | .ans => b
  | .sp => c
section
variable (a b c w : List Bool)
end
def one (k : M.tm.K) (w : List (M.tm.Γ k)) : ∀ k', List (M.tm.Γ k') := Function.update (fun _ => []) k w
def liftCfg (n : NS → List Bool) (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) : Cf M :=
  ⟨c.l.elim (some (.inr .after)) fun l => some (.inl l), (c.var, none), stk M c.stk n⟩
end CircuitLowerBound.Oracle


