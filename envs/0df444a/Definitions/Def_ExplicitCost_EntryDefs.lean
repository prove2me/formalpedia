-- Prove2me | Definitions.Def_ExplicitCost_EntryDefs
-- name    : ExplicitCost_EntryDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:36:31.730628+00:00
-- url     : https://prove2.me/theorems/abaf2a87-185a-4b98-ab76-8b66dfa3f92e
-- title:
--   Entry Defs
-- statement:
--   Definitions and structural lemmas for Entry Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/EntryDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
abbrev DataInput : Type := (List Unit × List Unit) × NetInput
def askedData : ProcsQ NetQuery ℤ DataInput where
  P c := asked.P c.2
  B c := asked.B c.2
  len c := asked.len c.2
  cap c := asked.cap c.2
  mem := QueryMachine.mapOut (QueryMachine.query fun x => Sum.inl x.2) fun v => decide (v ≠ 0)
  W := QueryMachine.query fun x => Sum.inr (Sum.inl x.2)
  Ψ := QueryMachine.query fun x => Sum.inr (Sum.inr (Sum.inl x.2))
  f := QueryMachine.query fun x => Sum.inr (Sum.inr (Sum.inr x.2))
def kOf (u : X0 DataInput) : ℕ := u.1.1.1.1.length
def gOf (u : X0 DataInput) : ℕ := u.1.1.1.2.length
def wData : QueryMachine NetQuery ℤ ((X0 DataInput × ℕ) × ℕ) ℤ :=
  QueryMachine.gated (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qW (kOf u.1.1) (gOf u.1.1) askedData.under.toPaperNetwork u) askedData.mem)
    (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qW (kOf u.1.1) (gOf u.1.1) askedData.under.toPaperNetwork u) askedData.W)
def psiData : QueryMachine NetQuery ℤ ((X0 DataInput × ℕ) × ℕ) ℤ :=
  QueryMachine.gated (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qW (kOf u.1.1) (gOf u.1.1) askedData.under.toPaperNetwork u) askedData.mem)
    (QueryMachine.gated (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qMb (kOf u.1.1) (gOf u.1.1) askedData.under u) askedData.mem)
      (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qPsi (kOf u.1.1) (gOf u.1.1) askedData.under u) askedData.Ψ))
def fData : QueryMachine NetQuery ℤ ((X0 DataInput × ℕ) × ℕ) ℤ :=
  QueryMachine.gated (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qW (kOf u.1.1) (gOf u.1.1) askedData.under.toPaperNetwork u) askedData.mem)
    (QueryMachine.mapIn (fun u : (X0 DataInput × ℕ) × ℕ => qF (kOf u.1.1) (gOf u.1.1) askedData.under.toPaperNetwork u) askedData.f)
def termData : QueryMachine NetQuery ℤ ((X0 DataInput × ℕ) × ℕ) ℤ :=
  QueryMachine.ite (fun u : (X0 DataInput × ℕ) × ℕ => isOne (kOf u.1.1) (gOf u.1.1) u) (QueryMachine.const 1)
    (QueryMachine.ite (fun u : (X0 DataInput × ℕ) × ℕ => isW (gOf u.1.1) u) wData (QueryMachine.ite (fun u : (X0 DataInput × ℕ) × ℕ => isPsi (kOf u.1.1) (gOf u.1.1) u) psiData fData))
def entryData : QueryMachine NetQuery ℤ (X0 DataInput) ℤ :=
  QueryMachine.ite (fun u : X0 DataInput => validB (kOf u) (gOf u) askedData.under.toPaperNetwork u)
    (QueryMachine.sumRange (fun u : X0 DataInput => nStates (kOf u) (gOf u) askedData.under.toPaperNetwork u) (QueryMachine.prodRange (fun v : X0 DataInput × ℕ => nPairs (gOf v.1) v) termData)) (QueryMachine.const 0)
def dataInput (K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ) : DataInput := ((unary K, unary g), netInput N P B)
def EntryCostExplicit : Prop := ∃ c₁ : ℕ, ∀ (K g : ℕ) (hK0 : 0 < K) (N : Net g) (P B τ : ℕ), K ≤ g → N.Is P B → 1 ≤ τ →
  ∀ x < K ^ g, ∀ L ≤ 2 * (g * P), (∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) → (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * L),
      entryData.Within (netOracle N) (fun _ => τ) ((dataInput K N P B, x), toLists K L (γ.val, Θ)) (2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁) ((g * (P + B)) ^ c₁)
        ((Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ) ∧
      |(Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ| < 2 ^ bitsOut K g P B
def EntryPoly : Prop := entryData.PolyTimeSteps
def EntrySameRuns : Prop := ∀ (K g : ℕ) (O : NetQuery → Option ℤ) (c : NetInput) (x : ℕ) (q : IQ) (own S : ℕ) (L : List NetQuery) (b : ℤ),
  (tableQ K g asked).Runs O ((c, x), q) own L S b → entryData.Runs O ((((unary K, unary g), c), x), q) own L (S + 4 * (2 * K + 2 * g + 2)) b
end ExplicitCost


