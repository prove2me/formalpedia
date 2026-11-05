-- Prove2me | Definitions.Def_CountedRecursion_SolverDefs
-- name    : CountedRecursion_SolverDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:47:24.665804+00:00
-- url     : https://prove2.me/theorems/ac472895-89ac-4c3b-9142-b9bc6490f010
-- title:
--   Solver Defs
-- statement:
--   Definitions and structural lemmas for Solver Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridProcedures
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_Tower_Defs
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
abbrev SolQuery : Type := Ctx ⊕ UpQuery
abbrev Stage₁ : Type := Head × (List Unit × List Unit)
abbrev Stage₂ : Type := Stage₁ × List ℤ
abbrev Stage₃ : Type := Stage₂ × ℤ
abbrev Stage₄ : Type := Stage₃ × List ℕ
abbrev Ready : Type := Stage₄ × List ℕ
def rHead (s : Ready) : Head := s.1.1.1.1.1
def rK (s : Ready) : ℕ := s.1.1.1.1.2.2.length
def rG (s : Ready) : ℕ := s.1.1.1.1.2.1.length * s.1.1.1.1.2.2.length
def rD (s : Ready) : ℤ := s.1.1.2
def rLists (s : Ready) : Lists := (s.1.1.1.2, s.1.2, s.2)
def rRect (s : Ready) : ℕ := nRectG (rG s) (rG s)
def nPatterns (s : Ready) : ℕ := (rLists s).1.length ^ rRect s
def direction (v : Ready × ℕ) : Bool :=
  decide (totalG (listsAsPieces (rLists v.1)) (rG v.1) (rG v.1) true 0 (hLam (rHead v.1)) v.2 < totalG (listsAsPieces (rLists v.1)) (rG v.1) (rG v.1) false 0 (hLam (rHead v.1)) v.2)
def parentAt (v : Ready × ℕ) (x : ℕ) : Parent :=
  ((v.1.1.1.1.1.2.2, unary (rG v.1)), (rHead v.1).2, rLists v.1, (direction v, v.2, x))
def searchInput (c : ℕ) (v : Ready × ℕ) : GroupingInput := ((1, 2 ^ (hLev (rHead v.1) + 4)), netData c (parentAt v 0))
def child (z : (Ready × ℕ) × CliqueCall) : Ctx := (((rHead z.1.1).1.tail, z.2.2.2.1, z.2.2.2.2), some (parentAt z.1 z.2.1))
def patternValue (c : ℕ) : QueryMachine SolQuery Ans (Ready × ℕ) ℤ :=
  QueryMachine.mapIn (fun v : Ready × ℕ => (v, searchInput c v)) (groupingCall.subst (askInt fun z : (Ready × ℕ) × CliqueCall => (Sum.inl (child z) : SolQuery)))
def capsLoop {σ : Type} [HasSize σ] (tr : Bool) (lamU : σ → List Unit) (idx : σ → List ℤ) : QueryMachine SolQuery Ans σ (List ℕ) :=
  QueryMachine.foldRange (fun s : σ => (idx s).length) (askInt fun v : σ × ℕ => Sum.inr (Sum.inr (lamU v.1, .inr (.inr (.inl (tr, (idx v.1).getD v.2 0))))))
    (fun acc _ (b : ℤ) => acc ++ [b.toNat]) fun _ => []
def sumAndDivide (c : ℕ) : QueryMachine SolQuery Ans Ready ℤ :=
  QueryMachine.bind (QueryMachine.sumRange nPatterns (patternValue c)) (QueryMachine.lift (Stepped.ofFun fun p : Ready × ℤ => p.2 / (((rD p.1).toNat ^ rRect p.1 : ℕ) : ℤ)))
def levelSolver (c x₀ : ℕ) : QueryMachine SolQuery Ans Head ℤ :=
  QueryMachine.bind (QueryMachine.lift (Stepped.mapIn (fun a : Head => a.1.tail) (numbersM x₀)))
    (QueryMachine.bind (askList fun s : Stage₁ => Sum.inr (Sum.inr (s.1.2.1, .inr (.inl ()))))
      (QueryMachine.bind (askInt fun s : Stage₂ => Sum.inr (Sum.inr (s.1.1.2.1, .inl ())))
        (QueryMachine.bind (capsLoop false (fun s : Stage₃ => s.1.1.1.2.1) fun s : Stage₃ => s.1.2)
          (QueryMachine.bind (capsLoop true (fun s : Stage₄ => s.1.1.1.1.2.1) fun s : Stage₄ => s.1.1.2) (sumAndDivide c)))))
def baseSolver (x₀ : ℕ) : QueryMachine SolQuery Ans Head ℤ :=
  QueryMachine.mapIn (fun a : Head => a.2) (readAs asInt (QueryMachine.mapAsk (fun q : TableQuery => (Sum.inr (Sum.inl q) : SolQuery)) (bruteMachine (2 ^ x₀))))
def solver (c x₀ : ℕ) : QueryMachine SolQuery Ans Ctx Ans :=
  QueryMachine.mapOut (QueryMachine.mapIn Prod.fst (QueryMachine.ite (fun a : Head => a.1.isEmpty) (baseSolver x₀) (levelSolver c x₀))) Sum.inl
def recursion (c x₀ : ℕ) : QueryMachine UpQuery Ans Ctx Ans := Tower.tower (solver c x₀) (procedure c)
def recursionWith (c x₀ : ℕ) (Alg : Stepped PieceQuery Ans) : QueryMachine TableQuery Ans Ctx Ans := PiecesCounted.withAlgorithm (recursion c x₀) Alg
def cliqueMachine (c x₀ : ℕ) (Alg : Stepped PieceQuery Ans) : QueryMachine TableQuery ℤ Head ℤ :=
  QueryMachine.mapOut (QueryMachine.mapIn (fun h : Head => ((h, none) : Ctx)) (readAs Sum.inl (recursionWith c x₀ Alg))) asInt
end ExplicitCost


