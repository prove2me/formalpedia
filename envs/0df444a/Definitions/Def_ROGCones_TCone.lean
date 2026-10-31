-- Prove2me | Definitions.Def_ROGCones_TCone
-- name    : ROGCones_TCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:04.63436+00:00
-- url     : https://prove2.me/theorems/e78656e9-bc71-4dee-8fbf-4d00b4c7991e
-- title:
--   $\mathcal T(\mathcal M)$: the PSD cone cut by the LMEs $\langle M, X\rangle = 0$, $M \in \mathcal M$
-- statement:
--   For a set $\mathcal M \subseteq \mathbb S^n$,
--   $$
--   \mathcal T(\mathcal M) := \{ X \in \mathbb S^n_+ : \langle M, X\rangle = 0 \ \text{ for all } M \in \mathcal M\}.
--   $$
--   Each constraint is a **linear matrix equality (LME)**. The paper reduces questions about $\mathcal S(\mathcal M)$ to questions about $\mathcal T(\mathcal M)$; note that $\mathcal T(\mathcal M)$ keeps the positive semidefiniteness constraint.
--
--   **Formalization Note** $\mathbb S^n_+$ membership is `Matrix.PosSemidef` and $\langle M, X\rangle$ is `(M * X).trace`.
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, §2.2, p.7

import Mathlib

namespace ROGCones

/-- **The spectrahedral cone `𝒯(𝓜)` cut out of the PSD cone by the LMEs `⟨M, X⟩ = 0`, `M ∈ 𝓜`.**
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, §2.2, p.7: "𝒯(𝓜) := {X ∈ Sⁿ₊ : ⟨M, X⟩ = 0,
∀M ∈ 𝓜}."

**Formalization Note.** Sⁿ₊ membership is `Matrix.PosSemidef`; `⟨M, X⟩` is `(M * X).trace`.
The PSD constraint is part of the set (𝒯 is not the PSD-free linear variety). -/
def TCone {n : ℕ} (𝓜 : Set (Matrix (Fin n) (Fin n) ℝ)) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.PosSemidef ∧ ∀ M ∈ 𝓜, (M * X).trace = 0}

end ROGCones


