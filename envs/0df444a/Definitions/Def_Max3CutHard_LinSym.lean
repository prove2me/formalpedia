-- Prove2me | Definitions.Def_Max3CutHard_LinSym
-- name    : Max3CutHard_LinSym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:43.288254+00:00
-- url     : https://prove2.me/theorems/1930575d-cf47-41eb-9857-452604ba45fb
-- title:
--   Alphabet for encoding 3Lin($\mathbb Z_3$) instances
-- statement:
--   The finite alphabet $\{\mathtt{one},\mathtt{sep},\mathtt t_0,\mathtt t_1,\mathtt t_2\}$ used to encode instances of 3Lin($\mathbb Z_3$). Numbers are written in unary with $\mathtt{one}$ and terminated by $\mathtt{sep}$; the symbol $\mathtt t_j$ records an equation of type $j$.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Theorem 2.1, p.4

import Mathlib

namespace Max3CutHard

/-- **Alphabet for encoding 3Lin(ℤ₃) instances.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Theorem 2.1, p.4 (the input of the
problem). `one` and `sep` write numbers in unary; `t0`, `t1`, `t2` write the type of an equation. -/
inductive LinSym where
  | one
  | sep
  | t0
  | t1
  | t2
  deriving DecidableEq

instance : Fintype LinSym where
  elems := {LinSym.one, LinSym.sep, LinSym.t0, LinSym.t1, LinSym.t2}
  complete := by intro x; cases x <;> simp

end Max3CutHard


