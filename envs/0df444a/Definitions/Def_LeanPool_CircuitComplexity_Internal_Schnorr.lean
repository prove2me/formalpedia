-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
-- name    : LeanPool_CircuitComplexity_Internal_Schnorr
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:10:40.232426+00:00
-- url     : https://prove2.me/theorems/62b059b4-2917-40f1-b38d-53864cd0de6d
-- title:
--   Schnorr
-- statement:
--   Definitions and structural lemmas for Schnorr, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Schnorr.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.IntervalCases
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
namespace Schnorr
def insertAt {N : Nat} (x : BitString N) (a : Fin (N + 1)) (b : Bool) :
    BitString (N + 1) := fun j =>
  if h1 : j.val < a.val then x ⟨j.val, by have := a.isLt; omega⟩
  else if h2 : j.val = a.val then b
  else x ⟨j.val - 1, by have := a.isLt; have := j.isLt; omega⟩
def remapWireR {N s : Nat} (a : Fin (N + 1)) (b : Bool) (g : Fin s)
    (wi : Fin (N + 1 + s)) (ni : Bool) : Fin (N + s) × Bool :=
  if h1 : wi.val = a.val then (⟨N + g.val, by omega⟩, ni.xor b)
  else if h2 : wi.val < a.val then (⟨wi.val, by omega⟩, ni)
  else (⟨wi.val - 1, by have := wi.isLt; omega⟩, ni)
def restrictD {N s : Nat} (d : CircDesc (N + 1) s) (a : Fin (N + 1)) (b : Bool) :
    CircDesc N s := fun g =>
  let slot := d g
  let (w1', n1') := remapWireR a b g slot.2.1.1 slot.2.2.1
  let (w2', n2') := remapWireR a b g slot.2.1.2 slot.2.2.2
  (slot.1, (w1', w2'), (n1', n2'))
inductive GateRedirect (W : Nat) where
  | const (c : Bool)
  | wire (w : Fin W) (flip : Bool)
def remapWireE {N s : Nat} (g : Fin (s + 1)) (rd : GateRedirect (N + s))
    (i : Fin s) (wi : Fin (N + (s + 1))) (ni : Bool) : Fin (N + s) × Bool :=
  if h1 : wi.val < N then (⟨wi.val, by omega⟩, ni)
  else if h2 : wi.val = N + g.val then
    if i.val < g.val then
      -- Forward reference to g: was false in old circuit, keep as self-ref (also false)
      (⟨N + i.val, by omega⟩, ni)
    else
      -- Back reference to g: redirect per rd
      match rd with
      | .const c => (⟨N + i.val, by omega⟩, ni.xor c)
      | .wire w' flip => (w', ni.xor flip)
  else if h3 : wi.val < N + g.val then (⟨wi.val, by omega⟩, ni)
  else (⟨wi.val - 1, by omega⟩, ni)
def elimGateD {N s : Nat} (d : CircDesc N (s + 1)) (g : Fin (s + 1))
    (rd : GateRedirect (N + s)) : CircDesc N s := fun i =>
  let oldIdx : Fin (s + 1) :=
    if h : i.val < g.val then ⟨i.val, by omega⟩
    else ⟨i.val + 1, by omega⟩
  let slot := d oldIdx
  let (w1', n1') := remapWireE g rd i slot.2.1.1 slot.2.2.1
  let (w2', n2') := remapWireE g rd i slot.2.1.2 slot.2.2.2
  (slot.1, (w1', w2'), (n1', n2'))
def liftWireE {N s : Nat} (g : Fin (s + 1)) (w : Fin (N + s)) : Fin (N + (s + 1)) :=
  if w.val < N + g.val then ⟨w.val, by omega⟩ else ⟨w.val + 1, by omega⟩
end Schnorr
end CircuitComplexity


