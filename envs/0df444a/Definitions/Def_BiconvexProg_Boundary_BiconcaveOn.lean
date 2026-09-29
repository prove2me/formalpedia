-- Prove2me | Definitions.Def_BiconvexProg_Boundary_BiconcaveOn
-- name    : BiconvexProg_Boundary_BiconcaveOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T17:47:56.939+00:00
-- url     : https://prove2.me/theorems/2022229f-2277-4089-aebf-1473707e37aa
-- title:
--   Biconcavity over a set: $\varphi(\cdot,y)$ and $\varphi(x,\cdot)$ concave on every convex section of $S$
-- statement:
--   Let $E$ and $F$ be real vector spaces, let $S \subseteq E \times F$ be a set (not necessarily convex), and let $\varphi : E \times F \to \mathbb{R}$. We say that $\varphi$ is **biconcave over $S$** when both partial functions are concave wherever they are defined inside $S$:
--
--   1. for every $y \in F$ and every convex set $C \subseteq E$ with $C \times \{y\} \subseteq S$, the function $x \mapsto \varphi(x, y)$ is concave on $C$;
--   2. for every $x \in E$ and every convex set $D \subseteq F$ with $\{x\} \times D \subseteq S$, the function $y \mapsto \varphi(x, y)$ is concave on $D$.
--
--   Equivalently, for every $y$, $\varphi(\cdot, y)$ is concave along every segment of the section $\{x : (x,y) \in S\}$, and symmetrically in $y$:
--
--   $$\varphi\big((1-\lambda)x + \lambda x', y\big) \ge (1-\lambda)\varphi(x, y) + \lambda \varphi(x', y) \quad \text{whenever } [x, x'] \times \{y\} \subseteq S,\ \lambda \in [0,1].$$
--
--   This is the hypothesis of Theorem 1 of Al-Khayyal and Falk, "the functions $\varphi(\cdot, y)$ and $\varphi(x, \cdot)$ are both concave functions", for a function defined over a set $S$ that need not be convex. Joint concavity of $\varphi$ is not assumed.
--
--   **Formalization Note** Since $S$ need not be convex, its sections need not be convex either; concavity is therefore required on every convex subset of a section, which is the same as concavity along every segment contained in the section. Nothing is required of $\varphi$ off $S$.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 274, Theorem 1 (hypothesis 'φ(·, y) and φ(x, ·) are both concave functions')

import Mathlib

namespace BiconvexProg.Boundary

/-- `φ` is biconcave over `S ⊆ E × F` (Al-Khayyal–Falk 1983, Theorem 1, p. 274): for every fixed
`y`, the partial function `x ↦ φ (x, y)` is concave on every convex set of `x` values whose
points `(x, y)` all lie in `S`; and symmetrically, for every fixed `x`, `y ↦ φ (x, y)` is concave
on every convex set of `y` values whose points `(x, y)` all lie in `S`. `S` itself need not be
convex. -/
def BiconcaveOn {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (S : Set (E × F)) (φ : E × F → ℝ) : Prop :=
  (∀ (y : F) (C : Set E), Convex ℝ C → (∀ x ∈ C, (x, y) ∈ S) →
      ConcaveOn ℝ C (fun x => φ (x, y))) ∧
  (∀ (x : E) (D : Set F), Convex ℝ D → (∀ y ∈ D, (x, y) ∈ S) →
      ConcaveOn ℝ D (fun y => φ (x, y)))

end BiconvexProg.Boundary


