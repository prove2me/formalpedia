-- Prove2me | Definitions.Def_CircuitLowerBound_Defs
-- name    : CircuitLowerBound_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:49:11.346755+00:00
-- url     : https://prove2.me/theorems/160f7951-0a10-458b-9f6d-d4b9299ab4a3
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundStatement
import Definitions.Def_StepMachines_Prog_Chunks
set_option autoImplicit false
section
section
namespace CircuitLowerBound
open ENP Groundwork
abbrev TLit : Type := ℕ × ℕ × ℕ × ℕ × Bool
abbrev TCl : Type := TLit × TLit × TLit
abbrev MCode : Type := ℕ × ℕ × List TCl
def kb (e : MCode) : ℕ := e.1
def lam (e : MCode) : ℕ := e.2.1
def tab (e : MCode) : List TCl := e.2.2
def bt (e : MCode) (L : ℕ) : ℕ := (L - kb e - lam e - 2) / 2
def bq (e : MCode) (L : ℕ) : ℕ := bt e L + lam e
def rb (e : MCode) : ℕ := Nat.size (tab e).length
def nb (e : MCode) (L : ℕ) : ℕ := rb e + bt e L + bq e L
def tval (b t mode : ℕ) : ℕ := if mode % 4 = 0 then 0 else if mode % 4 = 1 then t else if mode % 4 = 2 then t + 1 else 2 ^ b
def qval (P q mode : ℕ) : ℕ := if mode % 4 = 0 then 0 else if mode % 4 = 1 then q else P
def vidx (e : MCode) (L P t q : ℕ) (l : TLit) : ℕ :=
  ((l.1 % 2 ^ kb e) * 2 ^ (bt e L + 1) + tval (bt e L) t l.2.1) * 2 ^ (bq e L + 1) + (qval P q l.2.2.1 + l.2.2.2.1) % 2 ^ (bq e L + 1)
def litAt (e : MCode) (L P t q : ℕ) (l : TLit) : ℕ × Bool := (vidx e L P t q l, l.2.2.2.2)
def zeroCl : TCl := ((0, 0, 0, 0, false), (0, 0, 0, 0, false), (0, 0, 0, 0, false))
def clauseAt (e : MCode) (L P j : ℕ) : List (ℕ × Bool) :=
  [litAt e L P (j / 2 ^ bq e L % 2 ^ bt e L) (j % 2 ^ bq e L) ((tab e).getD (j / 2 ^ (bt e L + bq e L)) zeroCl).1,
   litAt e L P (j / 2 ^ bq e L % 2 ^ bt e L) (j % 2 ^ bq e L) ((tab e).getD (j / 2 ^ (bt e L + bq e L)) zeroCl).2.1,
   litAt e L P (j / 2 ^ bq e L % 2 ^ bt e L) (j % 2 ^ bq e L) ((tab e).getD (j / 2 ^ (bt e L + bq e L)) zeroCl).2.2]
def tabF (e : MCode) (L P : ℕ) : Cnf := (List.range (2 ^ nb e L)).map (clauseAt e L P)
def Fits (e : MCode) (L P : ℕ) : Prop := kb e + lam e + 4 ≤ L ∧ P + 2 ≤ 2 ^ bt e L
instance (e : MCode) (L P : ℕ) : Decidable (Fits e L P) := by unfold Fits; infer_instance
def ones (x : List Bool) : ℕ := (x.takeWhile id).length
def rest (x : List Bool) : List Bool := (x.dropWhile id).tail
def fld (W : ℕ) (w : List Bool) (i : ℕ) : ℕ := ofWord (block W i w)
def litOf (W : ℕ) (w : List Bool) (i : ℕ) : TLit := (fld W w i, fld W w (i + 1), fld W w (i + 2), fld W w (i + 3), decide (fld W w (i + 4) ≠ 0))
def codeOfWord (u : List Bool) : MCode :=
  (fld (ones u) (rest u) 0, fld (ones u) (rest u) 1,
    (List.range (((rest u).length - 2 * ones u) / (15 * ones u))).map fun r =>
      (litOf (ones u) (rest u) (2 + 15 * r), litOf (ones u) (rest u) (2 + 15 * r + 5), litOf (ones u) (rest u) (2 + 15 * r + 10)))
def codeOf (a : ℕ) : MCode := codeOfWord (rest (Nat.bits a))
def nu (m : ℕ) : ℕ := ((Nat.bits m).takeWhile fun b => !b).length
def pos (m : ℕ) : ℕ := m / 2 ^ nu m / 2
def next (m : ℕ) : ℕ := m + 2 ^ (nu m + 1)
def top (a : ℕ) : ℕ := 2 ^ 2 ^ 2 ^ a
open Classical in
/-- The formulas. Before the last place of chain a: the formula of table a with the parameter
`next m`. At the last place: a formula that is satisfiable if and only if the formula of table a for
the first number 2^a of the chain is not.
Everywhere else, and where there is no room: the empty formula. -/
noncomputable def Phi (m : ℕ) : Cnf :=
  if pos m < top (nu m) then (if Fits (codeOf (nu m)) m (next m) then tabF (codeOf (nu m)) m (next m) else [])
  else if pos m = top (nu m) then (if Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m)) then [[]] else [])
  else []
def units (w : List Bool) : Cnf := (List.range w.length).map fun i => [(i, w.getD i false)]
open Classical in
/-- The values of the first j variables in the search that sets each variable to 0 if that can still
be continued to a satisfying assignment, and to 1 if not. -/
noncomputable def greedy (φ : Cnf) : ℕ → List Bool
  | 0 => []
  | j + 1 => greedy φ j ++ [!decide (Sat (φ ++ units (greedy φ j ++ [false])))]
def L0 : Lang := fun x => (greedy (Phi x.length) (ofWord x + 1)).getD (ofWord x) false = true
def unary (P : ℕ) : List Bool := List.replicate P true ++ [false]
def Outputs (N : Turing.TM2ComputableAux Bool Bool) (x y : List Bool) (T : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun) (some (y.map N.outputAlphabet.invFun)) T)
def Acc (N : Turing.TM2ComputableAux Bool Bool) (P T : ℕ) : Prop := ∃ y : List Bool, Outputs N (unary P ++ y) [true] T
end CircuitLowerBound


