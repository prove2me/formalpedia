-- Prove2me | Definitions.Def_Max3CutHard_Eqn
-- name    : Max3CutHard_Eqn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:40.545226+00:00
-- url     : https://prove2.me/theorems/9400f95b-6c55-46f4-a49b-f5f38a75389d
-- title:
--   An equation $u_e+w_e+w'_e=t_e$ of a role-separated 3Lin($\mathbb Z_3$) instance
-- statement:
--   Given disjoint variable sets $U$ and $W$, an equation $e$ of a role-separated instance of 3Lin($\mathbb Z_3$) has the form
--
--   $$u_e+w_e+w'_e=t_e\quad\text{over }\mathbb Z_3,$$
--
--   with $u_e\in U$, two **distinct** variables $w_e\ne w'_e$ in $W$, and a right-hand side $t_e\in\mathbb Z_3$, the **type** of $e$.
--
--   These are the equations of Håstad's PCP to which the reduction is applied.
--
--   **Formalization Note** $U$ and $W$ are two types, so role separation is built in; the distinctness is a field of the structure.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Håstad's equations, p.4

import Mathlib

namespace Max3CutHard

/-- **An equation of a role-separated 3Lin(ℤ₃) instance.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Håstad's equations,
p.4: "equations `e` of the form `u_e + w_e + w′_e = t_e` over `ℤ₃`, with `u_e ∈ U`, distinct
`w_e, w′_e ∈ W`, `t_e ∈ ℤ₃` (the type of `e`)".

**Formalization Note.** The variable sets `U` and `W` are two types, so they are disjoint (role
separation) by construction; `hne` is the printed "distinct `w_e, w′_e`". -/
structure Eqn (U W : Type) where
  /-- the `U`-variable `u_e` -/
  u : U
  /-- the first `W`-variable `w_e` -/
  w : W
  /-- the second `W`-variable `w′_e` -/
  w' : W
  /-- the type (right-hand side) `t_e ∈ ℤ₃` -/
  t : ZMod 3
  /-- `w_e ≠ w′_e` -/
  hne : w ≠ w' 

end Max3CutHard


