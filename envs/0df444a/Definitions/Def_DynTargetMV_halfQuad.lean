-- Prove2me | Definitions.Def_DynTargetMV_halfQuad
-- name    : DynTargetMV_halfQuad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:16.670451+00:00
-- url     : https://prove2.me/theorems/536d5e16-c52e-4443-a5ac-3a39bb5e8aa5
-- title:
--   The quadratic form $\tfrac12 y^\top S y$
-- statement:
--   For an $m\times m$ real matrix $S$ and $y\in\mathbb R^m$, this is the quadratic form
--   $$
--   \tfrac12\, y^\top S\, y .
--   $$
--   It is the common part of the objectives of the quadratic programs (2.10), (B.2), (B.3), (B.4), (C.14), (C.18) and (C.22) of the paper.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.10), p.10; (B.2), p.22

import Mathlib

open Matrix

namespace DynTargetMV

/-- The quadratic form `½ y⊤ S y`, the common part of the objectives of (2.10), (B.2)–(B.4), (C.14),
(C.18) and (C.22). He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.10), p.10 and (B.2), p.22. -/
noncomputable def halfQuad {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (y : Fin m → ℝ) : ℝ :=
  (1 / 2) * (y ⬝ᵥ (S *ᵥ y))

end DynTargetMV


