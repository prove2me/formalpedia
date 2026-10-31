-- Prove2me | Definitions.Def_DynTargetMV_sqNorm
-- name    : DynTargetMV_sqNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:17.618384+00:00
-- url     : https://prove2.me/theorems/5a3317ae-113a-4ab9-9891-9010bb15a17d
-- title:
--   The squared Euclidean norm $\|v\|^2$
-- statement:
--   For a real coordinate vector $v\in\mathbb R^k$, the squared Euclidean norm is
--   $$
--   \|v\|^2=v^\top v=\sum_{i=1}^k v_i^2 .
--   $$
--   All norms in the paper are Euclidean, so this is the quantity in every energy term, such as $\|\sigma(t)^\top v\|^2$.
--
--   **Formalization Note** Mathlib's norm on `Fin k → ℝ` is the sup norm, so it is not used for these quantities.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, §2.1, p.6

import Mathlib

open Matrix

namespace DynTargetMV

/-- The squared Euclidean norm `‖v‖² = v⊤v` of a real coordinate vector. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, §2.1, p.6
("the Euclidean norm of a vector a as ‖a‖").

**Formalization Note** Mathlib's `‖·‖` on `Fin k → ℝ` is the sup norm, not the Euclidean norm of the
source, so every squared norm of the source is written with this definition. -/
noncomputable def sqNorm {k : ℕ} (v : Fin k → ℝ) : ℝ := v ⬝ᵥ v

end DynTargetMV


