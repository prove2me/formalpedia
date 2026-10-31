-- Prove2me | Definitions.Def_ROGCones_IsExtremeRay
-- name    : ROGCones_IsExtremeRay
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:10.234638+00:00
-- url     : https://prove2.me/theorems/511a4244-f54d-41b6-a1a4-613ba62b421c
-- title:
--   $\mathbb R_+X$ is an extreme ray of $S$
-- statement:
--   For a nonzero matrix $X$, the ray it spans is $\mathbb R_+X = \{\alpha X : \alpha \ge 0\}$. Given a set $S$ of matrices and $X \in S$ with $X \neq 0$, the ray $\mathbb R_+X$ is an **extreme ray** of $S$ if whenever $Y, Z \in S$ satisfy
--   $$
--   X = \tfrac12 (Y + Z),
--   $$
--   both $Y$ and $Z$ lie in $\mathbb R_+X$.
--
--   The paper uses this for closed convex cones $S \subseteq \mathbb S^n_+$ (Lemma 1 characterizes ROG cones by the rank of their extreme rays).
--
--   **Formalization Note** The predicate is stated for any set $S$; the closed-convex-cone context is a hypothesis of the theorems that use it. The ray membership is written out as $\exists a \ge 0,\ Y = aX$.
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Definition 2, p.6

import Mathlib

namespace ROGCones

/-- **`ℝ₊X` is an extreme ray of `S`.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Definition 2, p.6: "For X ∈ Sⁿ nonzero, the ray
spanned by X is ℝ₊X := {αX : α ≥ 0}. Let S ⊆ Sⁿ₊ be a closed convex cone and suppose X ∈ S is
nonzero. We say that ℝ₊X is an extreme ray of S if for any Y, Z ∈ S such that X = (Y + Z)/2, we
must have Y, Z ∈ ℝ₊X."

**Formalization Note.** The predicate is stated for an arbitrary set `S`; the paper's context
(`S` a closed convex cone in Sⁿ₊) is carried as hypotheses by the theorems that use it
(Lemma 1). Membership `Y ∈ ℝ₊X` is written out as `∃ a ≥ 0, Y = a • X`. -/
def IsExtremeRay {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℝ)) (X : Matrix (Fin n) (Fin n) ℝ) :
    Prop :=
  X ≠ 0 ∧ X ∈ S ∧
    ∀ Y ∈ S, ∀ Z ∈ S, X = (1 / 2 : ℝ) • (Y + Z) →
      (∃ a : ℝ, 0 ≤ a ∧ Y = a • X) ∧ (∃ b : ℝ, 0 ≤ b ∧ Z = b • X)

end ROGCones


