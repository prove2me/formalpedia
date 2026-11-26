-- Prove2me | Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
-- name    : Scott1976_DataTypesAsLattices_Lambda
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:54:05.058534+00:00
-- url     : https://prove2.me/theorems/1ea35eb9-e5fe-40c7-bb44-ec232c3602f7
-- title:
--   Lambda
-- statement:
--   Definitions and structural lemmas for Lambda, from Lars Warren Ericson (catskillsresearch/scott1976; original Lean code Apache-2.0; non-Lean reference PDF excluded per NOTICE)'s pinned Dana Scott's Data Types as Lattices (1976): Pomega, continuous functions, fixed points, and lambda models development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
set_option autoImplicit true
namespace Scott1976.DataTypesAsLattices
def ofNat (n : ℕ) : Pomega := {n}
def minExtend (p : ℕ → Pomega) (x : Pomega) : Pomega :=
  ⋃ n ∈ x, p n
def maxExtend (p : ℕ → Pomega) (x : Pomega) : Pomega :=
  {k | (x = ∅ ∧ ∀ n, k ∈ p n) ∨
    (∃ n, x = ofNat n ∧ k ∈ p n) ∨
    (x ≠ ∅ ∧ ∀ n, x ≠ ofNat n)}
def succSet (x : Pomega) : Pomega :=
  {k | ∃ n ∈ x, k = n + 1}
def predSet (x : Pomega) : Pomega :=
  {k | k + 1 ∈ x}
def condSet (z x y : Pomega) : Pomega :=
  {n | n ∈ x ∧ 0 ∈ z} ∪ {m | m ∈ y ∧ ∃ k, k + 1 ∈ z}
inductive Term where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
  | pred : Term → Term
  | cond : Term → Term → Term → Term
  | app : Term → Term → Term
  | lam : ℕ → Term → Term
def envSet (ρ : ℕ → Pomega) (i : ℕ) (v : Pomega) : ℕ → Pomega :=
  Function.update ρ i v
def interp : Term → (ℕ → Pomega) → Pomega
  | .var i, ρ => ρ i
  | .zero, _ => ofNat 0
  | .succ t, ρ => succSet (interp t ρ)
  | .pred t, ρ => predSet (interp t ρ)
  | .cond z x y, ρ => condSet (interp z ρ) (interp x ρ) (interp y ρ)
  | .app u x, ρ => funOf (interp u ρ) (interp x ρ)
  | .lam i body, ρ => graph (fun v => interp body (envSet ρ i v))
def curry2 (f : Pomega → Pomega → Pomega)
    (_hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (_hfy : ∀ x, IsScottContinuous (fun y => f x y)) : Pomega :=
  graph (fun x => graph (fun y => f x y))
def zeroC : Pomega := ofNat 0
def sucC : Pomega := graph succSet
def predC : Pomega := graph predSet
def condC : Pomega :=
  graph (fun x => graph (fun y => graph (fun z => condSet z x y)))
def Kcomb : Pomega := graph (fun x => graph (fun _ => x))
def Scomb : Pomega :=
  graph (fun u => graph (fun v => graph (fun x => funOf (funOf u x) (funOf v x))))
inductive IsCombinatory : Pomega → Prop
  | zero : IsCombinatory zeroC
  | suc : IsCombinatory sucC
  | pred : IsCombinatory predC
  | cond : IsCombinatory condC
  | K : IsCombinatory Kcomb
  | S : IsCombinatory Scomb
  | app {u v} : IsCombinatory u → IsCombinatory v → IsCombinatory (funOf u v)
def omegaComb (u : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf x x))
def Ycomb : Pomega :=
  graph (fun u => funOf (omegaComb u) (omegaComb u))
def seq0 : Pomega := botElem
def seq1 (x : Pomega) : Pomega :=
  graph (fun z => condSet z x botElem)
def seq2 (x y : Pomega) : Pomega :=
  graph (fun z => condSet z x (condSet (predSet z) y botElem))
end Scott1976.DataTypesAsLattices


