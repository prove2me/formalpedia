-- Prove2me | Definitions.Def_MinRankRecovery_Recovery_ripConst
-- name    : MinRankRecovery_Recovery_ripConst
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:27.983165+00:00
-- url     : https://prove2.me/theorems/360a82b6-ce89-429b-9ef6-cb13af5becc0
-- title:
--   Definition 3.1 — the r-restricted isometry constant δ_r(𝒜)
-- statement:
--   Let $m,n,p$ be natural numbers and let $\mathcal A:\mathbb R^{m\times n}\to\mathbb R^p$ be a linear map. Every such map is determined by $p$ measurement matrices $A_1,\dots,A_p\in\mathbb R^{m\times n}$ through
--   $$\mathcal A(X)_i=\langle A_i,X\rangle=\operatorname{Tr}(A_i^{\top}X),\qquad i=1,\dots,p .$$
--   Write $\|\mathcal A(X)\|$ for the Euclidean norm of the vector $\mathcal A(X)\in\mathbb R^p$ and $\|X\|_F$ for the Frobenius norm of $X$.
--
--   For an integer $r$, the **$r$-restricted isometry constant** $\delta_r(\mathcal A)$ is the smallest number $\delta\ge 0$ such that
--   $$(1-\delta)\,\|X\|_F\;\le\;\|\mathcal A(X)\|\;\le\;(1+\delta)\,\|X\|_F$$
--   holds for every matrix $X\in\mathbb R^{m\times n}$ of rank at most $r$.
--
--   The constant measures how far $\mathcal A$ is from an isometry on the set of matrices of rank at most $r$. It is the quantity in which the paper's recovery guarantees (Theorems 3.2 and 3.3) are stated.
--
--   **Formalization Note** The map $\mathcal A$ is given by its measurement matrices `Xs : Fin p → Matrix (Fin m) (Fin n) ℝ` and evaluated with `observationOp` of the referenced module `HighDimStat_MatrixRank_Core`; `measNorm Xs X` is $\|\mathcal A(X)\|$. `ripConst Xs r` is the infimum of the set of admissible $\delta\ge0$. This set is nonempty (any $\delta\ge\max(1,\|\mathcal A\|)$ belongs to it) and closed, so the infimum is attained and is the paper's "smallest number". The constraint $\delta\ge0$ is part of the set: for $r\ge1$ and $m,n\ge1$ no negative $\delta$ qualifies anyway, and in the degenerate cases ($m=0$, $n=0$ or $r=0$) it prevents the infimum of an unbounded set. The paper defines $\delta_r$ for $1\le r\le m$ under the normalization $m\le n$; here it is defined for every $r$, and for $r\ge\min(m,n)$ the condition covers all matrices. This is needed because Theorem 3.3 uses $\delta_{5r}$, and $5r$ may exceed $m$.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, Definition 3.1 and (3.2), p. 11

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

namespace MinRankRecovery.Recovery

open HighDimStat.MatrixRank

/-- The Euclidean norm `‖𝒜(X)‖` of the measurement vector `𝒜(X) ∈ ℝᵖ`, where the linear map
`𝒜 : ℝ^{m×n} → ℝᵖ` is given by its measurement matrices `Xs`, `𝒜(X)ᵢ = ⟨Xs i, X⟩`. -/
noncomputable def measNorm {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, (observationOp Xs X i) ^ 2)

/-- Definition 3.1, p. 11: the `r`-restricted isometry constant `δ_r(𝒜)`, the smallest
`δ ≥ 0` such that `(1 - δ)‖X‖_F ≤ ‖𝒜(X)‖ ≤ (1 + δ)‖X‖_F` for every matrix `X` of rank at
most `r`. Defined for every `r : ℕ`. -/
noncomputable def ripConst {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) (r : ℕ) : ℝ :=
  sInf {δ : ℝ | 0 ≤ δ ∧ ∀ X : Matrix (Fin m) (Fin n) ℝ, X.rank ≤ r →
    (1 - δ) * frobeniusNorm X ≤ measNorm Xs X ∧ measNorm Xs X ≤ (1 + δ) * frobeniusNorm X}

end MinRankRecovery.Recovery


