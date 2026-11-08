-- Prove2me | Definitions.Def_AffDisp4n_Acyclic_gateVal
-- name    : AffDisp4n_Acyclic_gateVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:18.109936+00:00
-- url     : https://prove2.me/theorems/751392bf-4d15-4758-91f5-4121014dcd95
-- title:
--   Gate values of a straight-line circuit
-- statement:
--   Given an assignment $x : V \to \mathbb F_2$ of the inputs, the **value of gate $g$** is $\mathrm{op}_g(a_1, a_2)$, where $a_1, a_2$ are the values of its two inputs: the constant itself, the input value $x_v$, or the value of an earlier gate. The values are computed along the topological order. The companion `prevVal` lists the values of the gates before $g$.
--
--   This is the evaluation of "a simple program for computing a Boolean function: each instruction of the program is a binary Boolean operation whose inputs are either input variables or the results of the previous instructions" (p.12).
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.1, p.12

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic

namespace AffDisp4n

/-- The **value of gate `g`** of a straight-line B₂-circuit `C` on the input assignment
`x : V → 𝔽₂` (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.1, p.12: "each instruction of the program is a binary Boolean operation whose
inputs are either input variables or the results of the previous instructions"). It is the operation
of `g` applied to the values of its two inputs, defined by recursion along the topological order. -/
def Acyclic.gateVal {V : Type} (C : Acyclic V) (x : V → ZMod 2) (g : Fin C.size) : ZMod 2 :=
  C.op g ((C.in₁ g).val x (fun j => C.gateVal x ⟨j.val, j.isLt.trans g.isLt⟩))
    ((C.in₂ g).val x (fun j => C.gateVal x ⟨j.val, j.isLt.trans g.isLt⟩))
termination_by g.val
decreasing_by all_goals exact j.isLt

/-- The values of the gates before gate `g`, as read by gate `g`. -/
def Acyclic.prevVal {V : Type} (C : Acyclic V) (x : V → ZMod 2) (g : Fin C.size) :
    Fin g.val → ZMod 2 :=
  fun j => C.gateVal x ⟨j.val, j.isLt.trans g.isLt⟩

end AffDisp4n


