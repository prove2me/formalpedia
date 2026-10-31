-- Prove2me | Definitions.Def_ROGCones_IsROG
-- name    : ROGCones_IsROG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:09.061055+00:00
-- url     : https://prove2.me/theorems/2bb780c7-5b6f-4526-874e-5cd3c9b99494
-- title:
--   Rank-one generated (ROG) set: $S = \mathrm{conv}(S \cap \{xx^\top\})$
-- statement:
--   A set $S$ of $n\times n$ real matrices is **rank-one generated (ROG)** if it is the convex hull of its rank-one positive semidefinite elements:
--   $$
--   S = \operatorname{conv}\bigl(S \cap \{xx^\top : x \in \mathbb R^n\}\bigr).
--   $$
--   The paper defines this for closed convex cones $S \subseteq \mathbb S^n_+$; for such a cone, being ROG means that the semidefinite relaxation of any quadratic problem whose lifted feasible set is $S$ loses nothing.
--
--   **Formalization Note** The predicate is stated for any set; every set it is applied to in this mission ($\mathcal S(\mathcal M)$, $\mathcal T(\mathcal M)$, their intersections and faces, the set of Corollary 5) is a closed convex cone in $\mathbb S^n_+$, and Lemma 1 carries these hypotheses explicitly. $\operatorname{conv}$ is `convexHull ℝ` and $xx^\top$ is `Matrix.vecMulVec x x`.
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Definition 1, p.6

import Mathlib

namespace ROGCones

/-- **Rank-one generated (ROG) set of matrices**: `S = conv(S ∩ {xxᵀ : x ∈ ℝⁿ})`.
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Definition 1, p.6: "A closed convex cone
S ⊆ Sⁿ₊ is rank-one generated (ROG) if S = conv(S ∩ {xx⊤ : x ∈ ℝⁿ})."

**Formalization Note.** The predicate is stated for an arbitrary set `S` of `n × n` real
matrices; Definition 1 applies it to closed convex cones in Sⁿ₊, and every set it is applied to
in this development (`𝒮(𝓜)`, `𝒯(𝓜)`, their intersections and faces, the set of Corollary 5) is
one, while Lemma 1 carries the closed-convex-cone hypotheses explicitly. `conv` is
`convexHull ℝ` and `xxᵀ` is `Matrix.vecMulVec x x`. -/
def IsROG {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℝ)) : Prop :=
  S = convexHull ℝ (S ∩ Set.range (fun x : Fin n → ℝ => Matrix.vecMulVec x x))

end ROGCones


