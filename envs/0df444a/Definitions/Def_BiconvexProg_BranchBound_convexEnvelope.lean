-- Prove2me | Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
-- name    : BiconvexProg_BranchBound_convexEnvelope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T17:51:17.834243+00:00
-- url     : https://prove2.me/theorems/8964e600-88ae-49cd-a5ef-4f82d0f120c8
-- title:
--   Convex envelope $\mathrm{Vex}_\Omega f$: the pointwise supremum of all convex functions underestimating $f$ over $\Omega$
-- statement:
--   Let $E$ be a real vector space, $\Omega \subseteq E$ and $f : E \to \mathbb{R}$. The **convex envelope** of $f$ over $\Omega$ is the pointwise supremum of all functions $g$ that are convex on $\Omega$ and underestimate $f$ on $\Omega$:
--
--   $$\mathrm{Vex}_\Omega f(z) = \sup\{\, g(z) : g \text{ convex on } \Omega,\ g(w) \le f(w) \text{ for all } w \in \Omega \,\}.$$
--
--   This is the definition of Al-Khayyal and Falk (following Falk 1969). In their branch-and-bound algorithm the envelope of the bilinear term $x^\top y$ over a box gives the lower-bounding functions of every subproblem.
--
--   **Formalization Note** The supremum is the real `sSup` of the set of values $g(z)$. It is meaningful at points $z \in \Omega$ at which some convex minorant exists: the set is then nonempty and bounded above by $f(z)$. Outside $\Omega$ the values $g(z)$ are unconstrained and `sSup` returns the default value $0$. If $\Omega$ is not convex, no function is `ConvexOn` $\Omega$ and the value is also $0$. The mission only evaluates the envelope at points of boxes, which are convex.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 275, The algorithm (definition of the convex envelope Vex_Ω f)

import Mathlib

namespace BiconvexProg.BranchBound

/-- The convex envelope `Vex_Ω f` of `f` over `Ω` (Al-Khayyal–Falk 1983, p. 275): the pointwise
supremum of all functions `g` that are convex on `Ω` and underestimate `f` on `Ω`.
Evaluated at `z`, it is the real supremum of the values `g z` over all such `g`.

Junk values (real `sSup`): the value is meaningful only at points `z ∈ Ω` where some convex
minorant exists (then the set of values is nonempty and bounded above by `f z`). Off `Ω` the
values `g z` are unconstrained, the set is unbounded, and `sSup` returns `0`; if `Ω` is not
convex, no `g` is `ConvexOn` it and the value is `sSup ∅ = 0`. -/
noncomputable def convexEnvelope {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Ω : Set E) (f : E → ℝ) (z : E) : ℝ :=
  sSup {r : ℝ | ∃ g : E → ℝ, ConvexOn ℝ Ω g ∧ (∀ w ∈ Ω, g w ≤ f w) ∧ r = g z}

end BiconvexProg.BranchBound


