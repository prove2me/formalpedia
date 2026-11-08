-- Prove2me | Definitions.Def_AffDisp4n_Acyclic_eval
-- name    : AffDisp4n_Acyclic_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:33.346141+00:00
-- url     : https://prove2.me/theorems/00b45ce6-1235-4c07-859b-b6f1f93b233a
-- title:
--   Output value $C(x)$ of a straight-line circuit
-- statement:
--   The **value computed** by a straight-line $B_2$-circuit $C$ on the input assignment $x$ is the value of its output: the constant, or the literal $t + \varepsilon$ of the output input or gate $t$. For a $B_2$-circuit on $n$ inputs this is $C(x)$, $x \in \mathbb F_2^n$. For a fair semi-circuit it is the value of the acyclic part once the auxiliary variables have been solved.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.1, pp.12–13

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_gateVal

namespace AffDisp4n

/-- The **value computed** by a straight-line B₂-circuit `C` on the input assignment `x`
(Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.1, pp.12–13): the value of its output, a constant or a literal of an input or a gate. -/
def Acyclic.eval {V : Type} (C : Acyclic V) (x : V → ZMod 2) : ZMod 2 :=
  C.out.val x (C.gateVal x) + C.outNeg

end AffDisp4n


