-- Prove2me | Definitions.Def_CutwidthCircuitLB_B2Circuit_IsRead
-- name    : CutwidthCircuitLB_B2Circuit_IsRead
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:20.850305+00:00
-- url     : https://prove2.me/theorems/7dce544f-2256-4806-b543-48bf742a1855
-- title:
--   Read signals of a $B_2$-circuit
-- statement:
--   The variables and the gates of a circuit are its **signals**. A signal is **read** if it has a directed path to the output gate. Inductively: the output gate is read, and both predecessors of a read gate are read.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 3, p.8

import Mathlib
import Definitions.Def_CutwidthCircuitLB_B2Circuit

namespace CutwidthCircuitLB

/-- A **signal** (a variable `Sum.inl j` or a gate `Sum.inr g`) of a B₂-circuit is **read** if it
has a directed path to the output gate (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §3, p.8): the output gate is read, and every
predecessor of a read gate is read.

**Formalization Note** The output gate is the last gate (`B2Circuit`); a predecessor
`Sum.inr k : Fin n ⊕ Fin g` of gate `g` is the gate with index `k` of the circuit. -/
inductive B2Circuit.IsRead {n : ℕ} (C : B2Circuit n) : Fin n ⊕ Fin C.size → Prop
  /-- the output gate is read -/
  | output : C.IsRead (Sum.inr ⟨C.size - 1, Nat.sub_lt C.size_pos Nat.one_pos⟩)
  /-- the first predecessor of a read gate is read -/
  | pred₁ (g : Fin C.size) : C.IsRead (Sum.inr g) →
      C.IsRead (Sum.map id (fun k : Fin g.val => ⟨k.val, k.isLt.trans g.isLt⟩) (C.pred₁ g))
  /-- the second predecessor of a read gate is read -/
  | pred₂ (g : Fin C.size) : C.IsRead (Sum.inr g) →
      C.IsRead (Sum.map id (fun k : Fin g.val => ⟨k.val, k.isLt.trans g.isLt⟩) (C.pred₂ g))

end CutwidthCircuitLB


