-- Prove2me | Definitions.Def_RandomLPIPM_rowSpace
-- name    : RandomLPIPM_rowSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:21.349424+00:00
-- url     : https://prove2.me/theorems/dbc71d69-cc66-40e2-9f34-ef33d1d408b3
-- title:
--   Row space $\operatorname{im}[M^\top]$ of a matrix
-- statement:
--   For $M\in\mathbb R^{d\times n}$, the row space of $M$ is the subspace of $\mathbb R^n$ spanned by the rows of $M$,
--   $$\operatorname{im}[M^\top]=\operatorname{span}\{M_{1,:},\dots,M_{d,:}\}.$$
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (2), p.7

import Mathlib

open Matrix

namespace RandomLPIPM

/-- **Row space `im[Mᵀ]` of a matrix `M ∈ ℝ^{d×n}`**, as a subspace of Euclidean `ℝⁿ`: the span of
the rows of `M`. Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (2) p.7 ("the row space of `M`"). -/
noncomputable def rowSpace {d n : ℕ} (M : Matrix (Fin d) (Fin n) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range fun i => WithLp.toLp 2 (M i))

end RandomLPIPM


