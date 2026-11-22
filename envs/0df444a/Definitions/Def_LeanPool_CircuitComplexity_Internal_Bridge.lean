-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Internal_Bridge
-- name    : LeanPool_CircuitComplexity_Internal_Bridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:11:10.448941+00:00
-- url     : https://prove2.me/theorems/21426121-9e1f-4fa2-86cb-9a23a57c8bd7
-- title:
--   Bridge
-- statement:
--   Definitions and structural lemmas for Bridge, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Bridge.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Schnorr
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Theorems.Thm_CircuitComplexity_andOr2_fanIn

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
def encodeGate {W W' : Nat} (g : Gate Basis.andOr2 W) (hW : W ≤ W') : GateSlot W' :=
  have h2 := andOr2_fanIn g
  (match g.op with | .and => true | .or => false,
   (⟨(g.inputs ⟨0, by omega⟩).val, by omega⟩,
    ⟨(g.inputs ⟨1, by omega⟩).val, by omega⟩),
   (g.negated ⟨0, by omega⟩, g.negated ⟨1, by omega⟩))
def circuitToDesc {N G : Nat} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) : CircDesc N (G + 1) := fun i =>
  if h : i.val < G then
    encodeGate (c.gates ⟨i.val, h⟩) (by omega : N + G ≤ N + (G + 1))
  else
    encodeGate (c.outputs 0) (by omega : N + G ≤ N + (G + 1))
def padDesc {N s : Nat} (d : CircDesc N s) (s' : Nat) (hs : 0 < s) (h : s ≤ s') :
    CircDesc N s' := fun i =>
  if hi : i.val < s then
    let slot := d ⟨i.val, hi⟩
    (slot.1,
     (⟨slot.2.1.1.val, by omega⟩, ⟨slot.2.1.2.val, by omega⟩),
     slot.2.2)
  else
    -- Copy gate: OR(last_original_output, last_original_output)
    (false, (⟨N + s - 1, by omega⟩, ⟨N + s - 1, by omega⟩), (false, false))
end CircuitComplexity


