-- Prove2me | Definitions.Def_HLambdaG_Main_TimeChange
-- name    : HLambdaG_Main_TimeChange
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:07:03.442777+00:00
-- url     : https://prove2.me/theorems/b3a3507e-0e20-40a5-87b4-47283ee69f48
-- title:
--   §1–§2, pp. 635, 638 — time change T(s)
-- statement:
--   A **time change** $T$ is a finite, nonnegative, nondecreasing, right-continuous function on $[0,\infty)$ such that
--   $$
--   T(s)\longrightarrow\infty\quad(s\to\infty).
--   $$
--
--   This general object relates customer index to elapsed time. The paper uses two independent time changes, $T_1$ and $T_2$, which may have the same asymptotic rate without being the same function.
--
--   **Formalization Note** Nonnegative reals make $T$ finite and nonnegative by type. Right continuity is continuity relative to $[s,\infty)$ at each $s$.
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), pp. 635, 638, §1 display (2) and §2 opening; https://doi.org/10.1287/opre.37.4.634

import Mathlib

open scoped NNReal

namespace HLambdaG.Main

open Filter Topology

/-- A nonnegative, finite, nondecreasing right-continuous time change tending to infinity. -/
structure TimeChange where
  T : ℝ≥0 → ℝ≥0
  mono : Monotone T
  rcont : ∀ s, ContinuousWithinAt T (Set.Ici s) s
  tendsto : Tendsto T atTop atTop

end HLambdaG.Main


