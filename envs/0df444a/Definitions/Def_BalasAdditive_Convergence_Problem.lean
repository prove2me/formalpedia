-- Prove2me | Definitions.Def_BalasAdditive_Convergence_Problem
-- name    : BalasAdditive_Convergence_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:02:49.339599+00:00
-- url     : https://prove2.me/theorems/22910bff-23a1-4352-be47-6ed258c4810d
-- title:
--   Balas's problem P with nonnegative objective coefficients
-- statement:
--   **Problem $P$** is the finite zero-one linear program with objective coefficients $c_j\ge 0$ for every binary coordinate $j$. There is no sign or integrality restriction on the entries of $A$ or $b$.
--
--   $$\min_{J\subseteq N}\ \sum_{j\in J}c_j\quad\text{subject to}\quad b_i-\sum_{j\in J}a_{ij}\ge 0\quad(i\in M).$$
--
--   The nonnegative-cost condition is the standing assumption under which the paper defines and analyzes its additive algorithm.
-- source:
--   Balas, An additive algorithm for solving linear programs with zero-one variables, Oper. Res. 13 (1965), p. 519, problem P, Eqs. (1)–(4), DOI 10.1287/opre.13.4.517

import Mathlib
import Definitions.Def_BalasAdditive_Convergence_BinaryLP

set_option autoImplicit false

namespace BalasAdditive.Convergence

/-- Balas's problem P: a zero-one program with nonnegative objective coefficients. -/
structure Problem (n m : ℕ) where
  lp : BinaryLP n m
  hc : ∀ j, 0 ≤ lp.c j

end BalasAdditive.Convergence


