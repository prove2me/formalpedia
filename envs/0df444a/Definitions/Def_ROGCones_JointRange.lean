-- Prove2me | Definitions.Def_ROGCones_JointRange
-- name    : ROGCones_JointRange
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:09.784765+00:00
-- url     : https://prove2.me/theorems/43b553c6-cc94-4f00-b087-af8d99780f23
-- title:
--   Joint range $W = \mathrm{span}(\bigcup_{M\in\mathcal M}\mathrm{range}(M))$
-- statement:
--   For a set $\mathcal M$ of $n\times n$ matrices, its **joint range** is the subspace
--   $$
--   W := \operatorname{span}\Bigl(\bigcup_{M \in \mathcal M} \operatorname{range}(M)\Bigr) \subseteq \mathbb R^n,
--   $$
--   where $\operatorname{range}(M)$ is the column space of $M$. Lemma 15 restricts every matrix of $\mathcal M$ to $W$, and Assumption 1 asks that $W = \mathbb R^n$.
--
--   **Formalization Note** $\operatorname{range}(M)$ is `Set.range M.mulVec` and $W$ is a `Submodule ℝ (Fin n → ℝ)`.
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Lemma 15 and Assumption 1, p.16 (also Lemma 7, p.8)

import Mathlib

namespace ROGCones

/-- **The joint range `W = span(⋃_{M ∈ 𝓜} range(M))`.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Lemma 7, p.8, Lemma 15 and Assumption 1, p.16:
"Let W := span(⋃_{M∈𝓜} range(M))".

**Formalization Note.** ℝⁿ is `Fin n → ℝ`; `range(M)` is the column space `Set.range M.mulVec`;
`span` is `Submodule.span ℝ`. -/
def JointRange {n : ℕ} (𝓜 : Set (Matrix (Fin n) (Fin n) ℝ)) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (⋃ M ∈ 𝓜, Set.range M.mulVec)

end ROGCones


