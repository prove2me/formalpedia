-- Prove2me | Definitions.Def_PerspEpi_projC
-- name    : PerspEpi_projC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:31.09893+00:00
-- url     : https://prove2.me/theorems/cd925e14-04b6-4c54-9b74-3456d5638191
-- title:
--   Euclidean projection $P_C$
-- statement:
--   For a set $C$ in a normed space and a point $x$, the **projection** $P_C(x)$ is the point of $C$ nearest to $x$:
--
--   $$
--   P_C(x) \in C,\qquad \|x - P_C(x)\| \le \|x - v\| \quad \text{for all } v \in C .
--   $$
--
--   For a nonempty closed convex subset of a Euclidean space this point exists and is unique. The paper projects onto $\operatorname{cl}(\operatorname{dom} f)$ and onto $\operatorname{epi} f$.
--
--   **Formalization Note** `projC C x` is the unique nearest point when a unique nearest point exists, and `x` otherwise; the second branch never applies to the nonempty closed convex sets of this mission.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §1.2 Notation, p.4

import Mathlib

namespace PerspEpi

/-- **Euclidean projection onto a set.** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §1.2 Notation, p.4: "We denote the
Euclidean projection of x̄ onto C by P_C(x̄)."

`projC C x` is the unique point of `C` nearest to `x`, whenever such a unique nearest point exists.

**Formalization Note.** For a nonempty closed convex subset of a finite-dimensional inner product
space (every set the paper projects onto: `cl dom f` for proper convex `f`, and `epi f` for
`f ∈ Γ0`) the nearest point exists and is unique, so `projC C x` is that point. The fallback
value `x` is used only when there is no unique nearest point, which never happens for the sets of
this mission. -/
noncomputable def projC {F : Type*} [NormedAddCommGroup F] (C : Set F) (x : F) : F := by
  classical exact
    if h : ∃! u, u ∈ C ∧ ∀ v ∈ C, ‖x - u‖ ≤ ‖x - v‖ then h.exists.choose else x

end PerspEpi


