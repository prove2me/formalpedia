-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_Lin2Inst
-- name    : HeilmanMax3Cut_Supplement_Lin2Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:04:52.4502+00:00
-- url     : https://prove2.me/theorems/55f38be7-3ba4-41e0-92dc-3f192c0f81f5
-- title:
--   An instance of MAX-2-LIN(3) in difference form
-- statement:
--   An instance of MAX-2-LIN(3) in difference form: a number $n$ of variables and a finite list of equations $x_i-x_j=c \bmod 3$, repetitions allowed (an equation listed $r$ times counts $r$ times).
--
--   **Formalization Note** Only difference equations are represented; the hardness of Theorem 1.5 for them implies it for general two-term equations.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem 1.5, p.4; p.5

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Supplement_Lin2Eq

namespace HeilmanMax3Cut.Supplement

/-- **An instance of MAX-2-LIN(3) in difference form.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem 1.5, p.4: a list of two-term
equations `x_i − x_j = c mod 3` in indeterminates `x_1, …, x_n` (p.4–5, "Suppose we are given `m`
two-term linear equations in indeterminates `x_1, …, x_n` of the form `x_i − x_j = c_ij mod p`").

**Formalization Note.** The list may repeat an equation (an equation listed `r` times counts `r`
times), which is the paper's "number of satisfied equations" for a multiset of equations. -/
structure Lin2Inst where
  /-- the number of variables -/
  n : ℕ
  /-- the equations, with repetitions -/
  eqs : List (Lin2Eq n)

end HeilmanMax3Cut.Supplement


