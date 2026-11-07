-- Prove2me | Definitions.Def_KarpLiptonOM_Circuit_eval
-- name    : KarpLiptonOM_Circuit_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:13.790699+00:00
-- url     : https://prove2.me/theorems/3bd44f61-f040-417f-967c-94f616973bff
-- title:
--   Value $C(x)$ of a circuit
-- statement:
--   The **value** $C(x)$ of a circuit $C$ with $n$ inputs on $x \in \{0,1\}^n$ is obtained by evaluating the gates in order, each on the inputs and the values of the earlier gates; it is the value of the last gate. A circuit computes $L$ on $\{0,1\}^n$ if $C(x) = 1 \iff x \in L$ for every $x$ of length $n$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit

namespace KarpLiptonOM

/-- The value `C(x)` of a circuit on an input `x ∈ {0,1}ⁿ` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20): the gates are
evaluated in order on the wire values (inputs, then earlier gates); the output is the last gate's
value (`false` for a circuit without gates). -/
def Circuit.eval {n : ℕ} (C : Circuit n) (x : List Bool) : Bool :=
  ((C.gates.foldl (fun vals g => vals ++ [match g with
      | .const b => b
      | .not i => !(vals.getD i false)
      | .and i j => vals.getD i false && vals.getD j false
      | .or i j => vals.getD i false || vals.getD j false]) x).drop x.length).getLastD false

end KarpLiptonOM


