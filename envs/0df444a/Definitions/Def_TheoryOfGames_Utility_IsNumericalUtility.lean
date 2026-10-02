-- Prove2me | Definitions.Def_TheoryOfGames_Utility_IsNumericalUtility
-- name    : TheoryOfGames_Utility_IsNumericalUtility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T00:51:56.756115+00:00
-- url     : https://prove2.me/theorems/24c41f95-5e0c-4045-a685-19f52ba7a227
-- title:
--   Numerical utility: properties (3:1:a), (3:1:b) in the form of (A:V)
-- statement:
--   Let $U$ be a system of utilities with relation $>$ and operation $\alpha u + (1-\alpha)v$ satisfying (3:A)–(3:C). A mapping $w \mapsto \mathrm v(w)$ of all utilities to real numbers is a **numerical utility** if
--
--   1. **(i) Monotony** (3:1:a): $u > v$ implies $\mathrm v(u) > \mathrm v(v)$;
--   2. **(ii)** (3:1:b), in the form of (A:V)(ii): for $0 < \gamma < 1$ and any $u, v$,
--   $$\mathrm v\big((1-\gamma)u + \gamma v\big) = (1-\gamma)\,\mathrm v(u) + \gamma\,\mathrm v(v).$$
--
--   These are the requirements of 3.5.1 on a correspondence between utilities and numbers: it carries the relation $u > v$ and the operation $\alpha u + (1-\alpha)v$ into the synonymous concepts for numbers. The monotony is strict; with a non-strict version, constant maps would qualify.
--
--   **Formalization Note** Numbers are real numbers. Property (ii) with weight $\gamma$ on $v$ is (3:1:b) with $\alpha = 1-\gamma$; both range over all weights in $(0,1)$, so the two forms are the same condition.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 24, 3.5.1, (3:1:a), (3:1:b); p. 627, (A:V)(i), (ii)

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

namespace TheoryOfGames.Utility

/-- A numerical utility `v : U → ℝ` for a utility system `S` (3.5.1 and (A:V)):
(i) Monotony (3:1:a): `u > v` implies `v(u) > v(v)`;
(ii) (3:1:b), in the form of (A:V)(ii): for `0 < γ < 1` and any `u, v`,
`v((1 − γ)u + γv) = (1 − γ)v(u) + γv(v)`. -/
def IsNumericalUtility {U : Type*} (S : UtilitySystem U) (v : U → ℝ) : Prop :=
  (∀ u w : U, S.gt u w → v w < v u) ∧
    ∀ (γ : OpenUnit) (u w : U),
      v (S.cmb γ u w) = (1 - (γ : ℝ)) * v u + (γ : ℝ) * v w

end TheoryOfGames.Utility


