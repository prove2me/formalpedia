-- Prove2me | Definitions.Def_CircuitLowerBoundStatement
-- name    : CircuitLowerBoundStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:32:08.116865+00:00
-- url     : https://prove2.me/theorems/7673d54d-1f29-45f3-9c40-b3a724d3c514
-- title:
--   Circuit Lower Bound Statement
-- statement:
--   Definitions and structural lemmas for Circuit Lower Bound Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/CircuitLowerBoundStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Computability.TuringMachine.Computable
set_option autoImplicit false
section
section
namespace ENP
open Turing
abbrev Lang : Type := List Bool → Prop
structure Gate where
  op : Bool → Bool → Bool
  in₁ : ℕ
  in₂ : ℕ
abbrev Circuit : Type := List Gate
def wires (x : List Bool) (C : Circuit) : List Bool := C.foldl (fun w G => w ++ [G.op (w.getD G.in₁ false) (w.getD G.in₂ false)]) x
def eval (C : Circuit) (x : List Bool) : Bool := (wires x C).getLastD false
def HasCircuits (L : Lang) (s : ℕ → ℕ) : Prop := ∀ n : ℕ, ∃ C : Circuit, C.length ≤ s n ∧ ∀ x : List Bool, x.length = n → (eval C x = true ↔ L x)
def HasLinearCircuits (L : Lang) : Prop := ∃ c : ℕ, HasCircuits L fun n => c * (n + 1)
abbrev Cnf : Type := List (List (ℕ × Bool))
def Sat (φ : Cnf) : Prop := ∃ a : ℕ → Bool, ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2
def encLit (l : ℕ × Bool) : List Bool := true :: (List.replicate l.1 true ++ [false, l.2])
def encCnf (φ : Cnf) : List Bool := φ.flatMap (fun C => C.flatMap encLit ++ [false, true]) ++ [false, false]
def SAT : Lang := fun w => ∃ φ : Cnf, w = encCnf φ ∧ Sat φ
structure OTM where
  tm : FinTM2
  inp : tm.Γ tm.k₀ ≃ Bool
  out : tm.Γ tm.k₁ ≃ Bool
  q : tm.K
  qry : tm.Γ q ≃ Bool
  ask : tm.Λ
  yes : tm.Λ
  no : tm.Λ
open Classical in
/-- One step with the oracle O. At «ask»: the word on the query stack, top first, is handed to the
oracle, the query stack is emptied, and the machine goes on at «yes» or at «no». Otherwise: a step
of the machine. -/
noncomputable def OTM.step (M : OTM) (O : Lang) (c : M.tm.Cfg) : Option M.tm.Cfg :=
  if c.l = some M.ask then some ⟨some (if O ((c.stk M.q).map M.qry) then M.yes else M.no), c.var, Function.update c.stk M.q []⟩
  else M.tm.step c
def OTM.Outputs (M : OTM) (O : Lang) (x : List Bool) (b : Bool) (T : ℕ) : Prop :=
  Nonempty (StateTransition.EvalsToInTime (M.step O) (initList M.tm (x.map M.inp.symm)) (some (haltList M.tm [M.out.symm b])) T)
def InENP (L : Lang) : Prop :=
  ∃ (M : OTM) (c : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧ ∀ x : List Bool, ∃ b : Bool, (b = true ↔ L x) ∧ M.Outputs SAT x b (2 ^ (c * (x.length + 1)))
def CorCircuits : Prop := ∃ L : Lang, InENP L ∧ ¬HasLinearCircuits L
def roundInput (x ans : List Bool) : List Bool := x.flatMap (fun b => [true, b]) ++ false :: ans
def Round (M : TM2ComputableAux Bool Bool) (T : ℕ) (x ans w : List Bool) : Prop :=
  Nonempty (TM2OutputsInTime M.tm ((roundInput x ans).map M.inputAlphabet.invFun) (some (w.map M.outputAlphabet.invFun)) T)
open Classical in
/-- After the answers «ans», and within r more queries, the result is b. A round returns 0b (the
result is b) or 1w (the query w); every round takes at most T steps. -/
inductive Protocol (M : TM2ComputableAux Bool Bool) (T : ℕ) (x : List Bool) (b : Bool) : List Bool → ℕ → Prop
  | done {ans : List Bool} {r : ℕ} : Round M T x ans [false, b] → Protocol M T x b ans r
  | query {ans w : List Bool} {r : ℕ} : Round M T x ans (true :: w) → Protocol M T x b (ans ++ [decide (SAT w)]) r → Protocol M T x b ans (r + 1)
def InENP' (L : Lang) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
    ∀ x : List Bool, ∃ b : Bool, (b = true ↔ L x) ∧ Protocol M (2 ^ (c * (x.length + 1))) x b [] (2 ^ (c * (x.length + 1)))
def CorCircuits' : Prop := ∃ L : Lang, InENP' L ∧ ¬HasLinearCircuits L
end ENP


