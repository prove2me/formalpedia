-- Prove2me | Definitions.Def_RotationLadder_Protocol_IsClosestRule
-- name    : RotationLadder_Protocol_IsClosestRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:35:50.87588+00:00
-- url     : https://prove2.me/theorems/f5ce9f1f-f467-4181-bf8c-bdbc81ff270b
-- title:
--   Closest-level rule
-- statement:
--   A rule $\mathrm{pick}:\mathbb R\to\mathbb N$ chooses a level for each remaining angle. It is a closest rule if for every $r\ne0$ and every level $j$,
--
--   $$\bigl|2\theta_{\mathrm{pick}(r)}-|r|\bigr|\le\bigl|2\theta_j-|r|\bigr| .$$
--
--   Any tie-break between two equally close levels is allowed.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. III, unnumbered, p. 3 and p. 4, step 3

import Mathlib
import Definitions.Def_RotationLadder_Protocol_angle

namespace RotationLadder.Protocol

/-- **Closest-level rules.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. III, p. 3: "apply the `|H_i⟩`-rotation that gets you closest to your target angle"; p. 4,
step 3.

`pick` is a closest rule when, for every nonzero remaining angle `r`, `angle (pick r)` is a closest
angle to `|r|` among all levels.

**Formalization Note.** Every tie-break is allowed, and `pick 0` is unconstrained: a residual `0`
needs no further step. -/
def IsClosestRule (pick : ℝ → ℕ) : Prop :=
  ∀ r : ℝ, r ≠ 0 → ∀ j : ℕ, abs (angle (pick r) - |r|) ≤ abs (angle j - |r|)

end RotationLadder.Protocol


