-- Prove2me | Definitions.Def_TheoryOfGames_Utility_intervalMap
-- name    : TheoryOfGames_Utility_intervalMap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T00:58:07.820199+00:00
-- url     : https://prove2.me/theorems/8b09c87a-6047-4b61-b9bc-978e4ea4b22e
-- title:
--   The interval function $f_{u_0,v_0}$ of (A:D)
-- statement:
--   Let $U$ be a system of utilities satisfying (3:A)–(3:C), and fix $u_0, v_0 \in U$ with $u_0 < v_0$. For $u_0 \leqq w \leqq v_0$ the numerical function $f(w) = f_{u_0,v_0}(w)$ is defined by
--
--   1. $f(u_0) = 0$;
--   2. $f(v_0) = 1$;
--   3. for $u_0 < w < v_0$, $f(w)$ is the number $\alpha$ in $0 < \alpha < 1$ with
--   $$w = (1-\alpha)u_0 + \alpha v_0 ,$$
--   which exists and is unique by (A:B) and (A:C).
--
--   The function $f_{u_0,v_0}$ is the first numerical representation of utilities constructed in the Appendix: it measures a utility between $u_0$ and $v_0$ by the weight that produces it as a combination of the two endpoints. The later functions $g$ and $h$ are built from it.
--
--   **Formalization Note** The Lean function is total on $U$. For $w$ strictly between $u_0$ and $v_0$ it returns a weight $\alpha$ with $(1-\alpha)u_0 + \alpha v_0 = w$, chosen with `Classical.choose`; it is the unique such weight once (A:B) is proved. Outside the interval $u_0 \leqq w \leqq v_0$ (where the book does not define $f$) it returns the placeholder $0$, and every statement about $f$ restricts $w$ to the interval.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 620, (A:D)

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

namespace TheoryOfGames.Utility

open Classical in
/-- The numerical function `f(w) = f_{u₀,v₀}(w)` of (A:D), for fixed `u₀ < v₀`:
(i) `f(u₀) = 0`; (ii) `f(v₀) = 1`; (iii) for `u₀ < w < v₀`, `f(w)` is the number `α` in
`0 < α < 1` with `w = (1 − α)u₀ + αv₀` (the correspondence of (A:B), (A:C)).
The book defines `f` only on `u₀ ≦ w ≦ v₀`; outside that interval (and if no such `α`
exists) the value `0` is a placeholder that no statement about `f` uses. -/
noncomputable def intervalMap {U : Type*} (S : UtilitySystem U) (u₀ v₀ w : U) : ℝ :=
  if w = u₀ then 0
  else if w = v₀ then 1
  else if h : ∃ α : OpenUnit, S.cmb α u₀ v₀ = w then ((Classical.choose h : OpenUnit) : ℝ)
  else 0

end TheoryOfGames.Utility


