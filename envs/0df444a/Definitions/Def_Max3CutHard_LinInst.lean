-- Prove2me | Definitions.Def_Max3CutHard_LinInst
-- name    : Max3CutHard_LinInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:45.199034+00:00
-- url     : https://prove2.me/theorems/99269ee8-9267-4701-bda7-8e2254115ace
-- title:
--   Encodable 3Lin($\mathbb Z_3$) instance: a list of equally weighted equations
-- statement:
--   An **encodable instance** consists of numbers $n_U,n_W$, the variable sets $U=\{0,\dots,n_U-1\}$ and $W=\{0,\dots,n_W-1\}$, and a finite list of $m$ role-separated equations $u_e+w_e+w'_e=t_e$, repetitions allowed. Each listed equation has weight $1/m$, so an equation listed $r$ times has weight $r/m$.
--
--   This is the input form of the instances in Håstad's theorem for a fixed $\varepsilon$: a finite set of tests with rational probabilities.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Håstad's equations and Theorem 2.1, p.4

import Mathlib
import Definitions.Def_Max3CutHard_Eqn

namespace Max3CutHard

/-- **An encodable instance of 3Lin(ℤ₃): a list of equations of equal weight.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402,
Section 2, Håstad's equations and Theorem 2.1, p.4.

**Formalization Note.** `U = Fin nU`, `W = Fin nW`. The list may repeat equations; each of its
`m` entries carries weight `1/m` (`LinInst.toWInst`), so an equation listed `r` times has weight
`r/m`. This is the input form of Håstad's instances for a fixed `ε` (finitely many tests with
rational probabilities). -/
structure LinInst where
  /-- number of `U`-variables -/
  nU : ℕ
  /-- number of `W`-variables -/
  nW : ℕ
  /-- the equations, with repetitions -/
  eqs : List (Eqn (Fin nU) (Fin nW))

end Max3CutHard


