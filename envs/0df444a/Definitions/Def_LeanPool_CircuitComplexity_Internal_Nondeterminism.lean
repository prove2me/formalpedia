-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Internal_Nondeterminism
-- name    : LeanPool_CircuitComplexity_Internal_Nondeterminism
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:14:07.28193+00:00
-- url     : https://prove2.me/theorems/68b8b40e-bb8c-41f3-8849-22a792e89b48
-- title:
--   Nondeterminism
-- statement:
--   Definitions and structural lemmas for Nondeterminism, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Nondeterminism.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_andOr2_fanIn
public import Theorems.Thm_CircuitComplexity_existQuantify_const_false
public import Theorems.Thm_CircuitComplexity_existQuantify_const_true
public import Theorems.Thm_CircuitComplexity_existQuantify_eq_true
public import Theorems.Thm_CircuitComplexity_forallQuantify_const_false
public import Theorems.Thm_CircuitComplexity_forallQuantify_const_true
public import Theorems.Thm_CircuitComplexity_forallQuantify_eq_true
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth
attribute [local simp] CircuitComplexity.existQuantify_const_false
attribute [local simp] CircuitComplexity.existQuantify_const_true
attribute [local simp] CircuitComplexity.existQuantify_eq_true
attribute [local simp] CircuitComplexity.forallQuantify_const_false
attribute [local simp] CircuitComplexity.forallQuantify_const_true
attribute [local simp] CircuitComplexity.forallQuantify_eq_true


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
variable {k m : Nat}
def mkConstGateP {G : Nat} [NeZero m] (val : Bool) (bound : Nat) :
    { g : Gate Basis.andOr2 (k + m + G) //
      ∀ j : Fin g.fanIn, (g.inputs j).val < k + m + bound } :=
  have hW : 0 < k + m + G := by have := NeZero.ne m; omega
  have hB : 0 < k + m + bound := by have := NeZero.ne m; omega
  if val then
    ⟨{ op := .or, fanIn := 2, arityOk := rfl,
       inputs := fun _ => ⟨0, hW⟩,
       negated := fun i => if i.val = 0 then false else true },
     fun _ => by dsimp; exact hB⟩
  else
    ⟨{ op := .and, fanIn := 2, arityOk := rfl,
       inputs := fun _ => ⟨0, hW⟩,
       negated := fun i => if i.val = 0 then false else true },
     fun _ => by dsimp; exact hB⟩
def mkIdentGateP {G : Nat} (op : AONOp) (w : Fin (k + m + G)) (neg : Bool) (bound : Nat)
    (hw : w.val < k + m + bound) :
    { g : Gate Basis.andOr2 (k + m + G) //
      ∀ j : Fin g.fanIn, (g.inputs j).val < k + m + bound } :=
  ⟨{ op := op, fanIn := 2, arityOk := rfl,
     inputs := fun _ => w, negated := fun _ => neg },
   fun _ => by dsimp; exact hw⟩
def restrictGateP {G : Nat} [NeZero m] (b : Bool)
    (g : Gate Basis.andOr2 ((k + 1) + m + G))
    (hfanIn : g.fanIn = 2)
    (bound : Nat)
    (hbound : ∀ j : Fin g.fanIn, (g.inputs j).val < (k + 1) + m + bound) :
    { g' : Gate Basis.andOr2 (k + m + G) //
      ∀ j : Fin g'.fanIn, (g'.inputs j).val < k + m + bound } :=
  let w0 := g.inputs ⟨0, by omega⟩
  let w1 := g.inputs ⟨1, by omega⟩
  let n0 := g.negated ⟨0, by omega⟩
  let n1 := g.negated ⟨1, by omega⟩
  let eff0 := b.xor n0
  let eff1 := b.xor n1
  have hw0_bound := hbound ⟨0, by omega⟩
  have hw1_bound := hbound ⟨1, by omega⟩
  if hw0 : w0.val = 0 then
    if hw1 : w1.val = 0 then
      let result := match g.op with
        | .and => eff0 && eff1
        | .or => eff0 || eff1
      mkConstGateP (k := k) (m := m) (G := G) result bound
    else
      let w1' : Fin (k + m + G) := ⟨w1.val - 1, by omega⟩
      have hw1'_bound : w1'.val < k + m + bound := by simp [w1']; omega
      match g.op with
      | .and =>
        if eff0 then mkIdentGateP .and w1' n1 bound hw1'_bound
        else mkConstGateP (k := k) (m := m) (G := G) false bound
      | .or =>
        if eff0 then mkConstGateP (k := k) (m := m) (G := G) true bound
        else mkIdentGateP .or w1' n1 bound hw1'_bound
  else
    if hw1 : w1.val = 0 then
      let w0' : Fin (k + m + G) := ⟨w0.val - 1, by omega⟩
      have hw0'_bound : w0'.val < k + m + bound := by simp [w0']; omega
      match g.op with
      | .and =>
        if eff1 then mkIdentGateP .and w0' n0 bound hw0'_bound
        else mkConstGateP (k := k) (m := m) (G := G) false bound
      | .or =>
        if eff1 then mkConstGateP (k := k) (m := m) (G := G) true bound
        else mkIdentGateP .or w0' n0 bound hw0'_bound
    else
      ⟨{ op := g.op, fanIn := 2, arityOk := rfl,
         inputs := fun i => if i.val = 0 then ⟨w0.val - 1, by omega⟩
                             else ⟨w1.val - 1, by omega⟩,
         negated := fun i => if i.val = 0 then n0 else n1 },
       fun j => by simp only; split_ifs <;> simp <;> omega⟩
def restrictCircuit {G : Nat} [NeZero m] (b : Bool)
    (c : Circuit Basis.andOr2 ((k + 1) + m) 1 G) :
    Circuit Basis.andOr2 (k + m) 1 G where
  gates i := (restrictGateP (k := k) (m := m) b (c.gates i) (andOr2_fanIn (c.gates i))
    i.val (fun j => c.acyclic i j)).val
  outputs j := (restrictGateP (k := k) (m := m) b (c.outputs j) (andOr2_fanIn (c.outputs j))
    G (fun j' => by have := ((c.outputs j).inputs j').isLt; omega)).val
  acyclic i := (restrictGateP (k := k) (m := m) b (c.gates i) (andOr2_fanIn (c.gates i))
    i.val (fun j => c.acyclic i j)).property
def prependInput (b : Bool) (x : BitString (k + m)) :
    BitString ((k + 1) + m) :=
  fun i => if h : i.val = 0 then b else x ⟨i.val - 1, by omega⟩
end CircuitComplexity


