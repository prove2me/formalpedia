-- Prove2me | Definitions.Def_O3_Stage2RouteC
-- name    : O3_Stage2RouteC
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:04:19.776802+00:00
-- url     : https://prove2.me/theorems/8fcddcb8-f343-430f-8e04-226e55bf2571
-- title:
--   Stage2 Route C
-- statement:
--   Definitions and structural lemmas for Stage2 Route C, from Yuning Yang (yuningyang19/parameter_free_gradient_p; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Parameter-free gradient minimization in l_p geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteC.lean

import Definitions.Def_O3_Geometry
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
set_option autoImplicit true
open scoped BigOperators
namespace O3.Stage2RouteC
noncomputable def BallCarlenLiebStatement : Prop :=
  ∀ (p : ℝ), 1 < p → p ≤ 2 → ∀ (d : ℕ) (u v : O3.Point d),
    (O3.lpNorm p (u + v)) ^ (2 : ℕ) +
        (p - 1) * (O3.lpNorm p (u - v)) ^ (2 : ℕ) ≤
      2 * ((O3.lpNorm p u) ^ (2 : ℕ) + (O3.lpNorm p v) ^ (2 : ℕ))
noncomputable def ExactMidpointStatement : Prop :=
  ∀ (p : ℝ), 1 < p → p ≤ 2 → ∀ (d : ℕ) (x y : O3.Point d),
    (1 / 2 : ℝ) * (O3.lpNorm p ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (O3.lpNorm p x) ^ (2 : ℕ)) +
        (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (O3.lpNorm p y) ^ (2 : ℕ)) -
        (1 / 4 : ℝ) * ((p - 1) / 2) * (O3.lpNorm p (x - y)) ^ (2 : ℕ)
end O3.Stage2RouteC


