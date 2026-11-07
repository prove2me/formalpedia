-- Prove2me | Definitions.Def_DDNNFNeg_NNF_eval
-- name    : DDNNFNeg_NNF_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:08.502823+00:00
-- url     : https://prove2.me/theorems/1234c82b-b1b6-4fb7-a7ec-df2311eb6fe1
-- title:
--   Value of a gate of an NNF on an assignment
-- statement:
--   For an NNF $C$ and an assignment $x \in \{0,1\}^X$, the value of gate $k$ is defined by recursion on $k$: a literal $v$ takes the value $x(v)$, a literal $\neg v$ the value $1 - x(v)$, a constant its own value, and an $\wedge$-gate (resp. $\vee$-gate) the conjunction (resp. disjunction) of the values of its two children.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.1, p.8

import Mathlib
import Definitions.Def_DDNNFNeg_NNF

namespace DDNNFNeg

/-- The value of gate `k` of the NNF `C` on the assignment `x : X → Bool`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.1, p.8): a literal `v` evaluates to `x v`, a literal `¬v` to `!x v`, a constant
to itself, and an `∧` (`∨`) gate to the conjunction (disjunction) of its children. -/
def NNF.eval {X : Type*} (C : NNF X) (x : X → Bool) (k : Fin C.size) : Bool :=
  match h : C.gate k with
  | .lit v pos => if pos then x v else !x v
  | .const b => b
  | .and i j =>
      have hij := C.wf k i j (Or.inl h)
      C.eval x i && C.eval x j
  | .or i j =>
      have hij := C.wf k i j (Or.inr h)
      C.eval x i || C.eval x j
termination_by k.val
decreasing_by
  · exact hij.1
  · exact hij.2
  · exact hij.1
  · exact hij.2

end DDNNFNeg


