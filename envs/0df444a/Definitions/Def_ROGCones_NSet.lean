-- Prove2me | Definitions.Def_ROGCones_NSet
-- name    : ROGCones_NSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:06.130408+00:00
-- url     : https://prove2.me/theorems/2fe4728c-e112-47b8-ab5d-57e42cc5f4f9
-- title:
--   $\mathcal N(\mathcal M)$: common real zeros of the quadratic forms $x^\top M x$
-- statement:
--   For a set $\mathcal M \subseteq \mathbb S^n$,
--   $$
--   \mathcal N(\mathcal M) := \{ x \in \mathbb R^n : x^\top M x = 0 \ \text{ for all } M \in \mathcal M\}.
--   $$
--   Equivalently, $x \in \mathcal N(\mathcal M)$ exactly when the rank-one matrix $xx^\top$ lies in $\mathcal T(\mathcal M)$. It is the real variety cut out by the quadratic forms of $\mathcal M$.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ` and $x^\top M x$ is `x ⬝ᵥ (M *ᵥ x)`.
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Definition 4, p.11

import Mathlib

open Matrix

namespace ROGCones

/-- **The common real zero set `𝒩(𝓜)` of the quadratic forms `xᵀMx`, `M ∈ 𝓜`.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Definition 4, p.11: "Given 𝓜 ⊆ Sⁿ, we define
𝒩(𝓜) := {x ∈ ℝⁿ : x⊤Mx = 0, ∀M ∈ 𝓜}."

**Formalization Note.** ℝⁿ is `Fin n → ℝ` and `xᵀMx` is `x ⬝ᵥ (M *ᵥ x)`. -/
def NSet {n : ℕ} (𝓜 : Set (Matrix (Fin n) (Fin n) ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ M ∈ 𝓜, x ⬝ᵥ (M *ᵥ x) = 0}

end ROGCones


