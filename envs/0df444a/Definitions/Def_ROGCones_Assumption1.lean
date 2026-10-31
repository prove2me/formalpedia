-- Prove2me | Definitions.Def_ROGCones_Assumption1
-- name    : ROGCones_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:05.116308+00:00
-- url     : https://prove2.me/theorems/713b9ab3-fef4-453c-ae63-f32327b23fb1
-- title:
--   Assumption 1: the ranges of the matrices in $\mathcal M$ span $\mathbb R^n$
-- statement:
--   A set $\mathcal M$ of $n\times n$ matrices satisfies **Assumption 1** if
--   $$
--   \operatorname{span}\Bigl(\bigcup_{M \in \mathcal M} \operatorname{range}(M)\Bigr) = \mathbb R^n .
--   $$
--   By Lemma 15 every question about $\mathcal T(\{M_1, M_2\})$ reduces to this case; the dimension-by-dimension propositions behind Theorem 4 assume it.
--
--   **Formalization Note** The joint range is `JointRange 𝓜`, and $= \mathbb R^n$ is `= ⊤`.
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Assumption 1, p.16

import Mathlib
import Definitions.Def_ROGCones_JointRange

namespace ROGCones

/-- **Assumption 1**: the ranges of the matrices in `𝓜` jointly span ℝⁿ.
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Assumption 1, p.16: "Assume that
span(⋃_{M∈𝓜} range(M)) = ℝⁿ."

**Formalization Note.** `JointRange 𝓜` is `span(⋃_{M∈𝓜} range(M))` as a submodule of
`Fin n → ℝ`; `= ℝⁿ` is `= ⊤`. -/
def Assumption1 {n : ℕ} (𝓜 : Set (Matrix (Fin n) (Fin n) ℝ)) : Prop :=
  JointRange 𝓜 = ⊤

end ROGCones


