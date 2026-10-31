-- Prove2me | Definitions.Def_ROGCones_SCone
-- name    : ROGCones_SCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:07.39635+00:00
-- url     : https://prove2.me/theorems/d21755b3-e1a4-43f2-b5ad-cc7dac66b0df
-- title:
--   $\mathcal S(\mathcal M)$: the PSD cone cut by the LMIs $\langle M, X\rangle \ge 0$, $M \in \mathcal M$
-- statement:
--   Let $\mathbb S^n$ be the space of real symmetric $n\times n$ matrices and $\mathbb S^n_+$ the cone of positive semidefinite ones. For a set $\mathcal M \subseteq \mathbb S^n$,
--   $$
--   \mathcal S(\mathcal M) := \{ X \in \mathbb S^n_+ : \langle M, X\rangle \ge 0 \ \text{ for all } M \in \mathcal M\},
--   $$
--   where $\langle M, X\rangle = \operatorname{tr}(MX)$ is the trace inner product. Each constraint is a **linear matrix inequality (LMI)**; $\mathcal S(\mathcal M)$ is a closed convex cone. It is the object whose rank-one generation the paper studies.
--
--   **Formalization Note** $\mathbb S^n_+$ membership is `Matrix.PosSemidef`, and $\langle M, X\rangle$ is `(M * X).trace`. The standing assumption $\mathcal M \subseteq \mathbb S^n$ is a hypothesis of the theorems, not part of this definition.
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, §2.1, p.6

import Mathlib

namespace ROGCones

/-- **The spectrahedral cone `𝒮(𝓜)` cut out of the PSD cone by the LMIs `⟨M, X⟩ ≥ 0`, `M ∈ 𝓜`.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, §2.1, p.6: "Given 𝓜 ⊆ Sⁿ, define
𝒮(𝓜) := {X ∈ Sⁿ₊ : ⟨M, X⟩ ≥ 0, ∀M ∈ 𝓜}."

**Formalization Note.** Sⁿ₊ membership is Mathlib's `Matrix.PosSemidef` (which includes
symmetry). The trace inner product `⟨M, X⟩` is `(M * X).trace`, which equals `∑ᵢⱼ MᵢⱼXᵢⱼ`
whenever `M` is symmetric. The paper's standing assumption `𝓜 ⊆ Sⁿ` is a hypothesis of every
theorem that uses this set, not part of the definition. -/
def SCone {n : ℕ} (𝓜 : Set (Matrix (Fin n) (Fin n) ℝ)) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.PosSemidef ∧ ∀ M ∈ 𝓜, 0 ≤ (M * X).trace}

end ROGCones


