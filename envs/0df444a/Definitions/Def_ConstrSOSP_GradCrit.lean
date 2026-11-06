-- Prove2me | Definitions.Def_ConstrSOSP_GradCrit
-- name    : ConstrSOSP_GradCrit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:08.426201+00:00
-- url     : https://prove2.me/theorems/35f0fe44-8130-4846-b6ae-21abf8619f1a
-- title:
--   Gradient criteria $|G_x|>\epsilon$ or $|G_y|>\epsilon$
-- statement:
--   At $(x,y)$, $|\partial f/\partial x|>\epsilon$ (Gx criterion) or $|\partial f/\partial y|>\epsilon$ (Gy criterion).
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.4.1, p.32

import Mathlib

namespace ConstrSOSP

/-- **The gradient criteria** (arXiv:2604.02285, 2 Nov 2026, §5.4.1, p.32: "|G_y| > ϵ0, (Gy
criterion) |G_x| > ϵ0, (Gx criterion)", with `G_x = ∂f/∂x`, `G_y = ∂f/∂y`): at `(x, y)`, the
partial derivative of `f` in `x` or in `y` has absolute value greater than `ε`. -/
noncomputable def GradCrit (f : ℝ → ℝ → ℝ) (ε x y : ℝ) : Prop :=
  ε < |deriv (fun s => f s y) x| ∨ ε < |deriv (fun t => f x t) y|

end ConstrSOSP


