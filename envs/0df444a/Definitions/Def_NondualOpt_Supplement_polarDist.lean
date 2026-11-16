-- Prove2me | Definitions.Def_NondualOpt_Supplement_polarDist
-- name    : NondualOpt_Supplement_polarDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:13:03.865115+00:00
-- url     : https://prove2.me/theorems/28932132-23d9-4f73-a2ab-312258bd024f
-- title:
--   The polar distance $\mathrm{dist}_{X^\circ}(x,S)$
-- statement:
--   For $X\subseteq\mathbb R^d$, a point $x\in\mathbb R^d$ and a set $S\subseteq\mathbb R^d$,
--   $$
--   \mathrm{dist}_{X^\circ}(x,S)=\inf_{y\in S}\|y-x\|_{X^\circ},
--   $$
--   the distance from $x$ to $S$ in the polar norm of $X$.
--
--   **Formalization Note** The infimum ranges over the points of $S$ only; it is the true infimum whenever $S$ is nonempty (the values are nonnegative), as for the convex hull of $T\ge2$ samples in Theorem 10.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, §5.1, p.13

import Mathlib
import Definitions.Def_NondualOpt_Supplement_polarNorm

namespace NondualOpt.Supplement

/-- The polar-norm distance `dist_{X°}(x, S) = inf_{y ∈ S} ‖y − x‖_{X°}` from a point `x ∈ ℝ^d` to
a set `S ⊆ ℝ^d`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, §5.1, p.13
(`dist_{‖·‖}(x, S) = inf_{y ∈ S} ‖y − x‖`, `dist_{X°} = dist_{‖·‖_{X°}}`).

**Formalization Note.** The infimum ranges over the subtype `S` (real `iInf`), so no junk value
enters from points outside `S`; every use takes `S` nonempty (the convex hull of `T ≥ 2` samples)
and the values are `≥ 0`, so this is the true infimum. -/
noncomputable def polarDist {d : ℕ} (X : Set (Fin d → ℝ)) (x : Fin d → ℝ)
    (S : Set (Fin d → ℝ)) : ℝ :=
  ⨅ y : S, polarNorm X ((y : Fin d → ℝ) - x)

end NondualOpt.Supplement


