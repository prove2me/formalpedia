-- Prove2me | Definitions.Def_RandomLPIPM_orthProj
-- name    : RandomLPIPM_orthProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:20.898485+00:00
-- url     : https://prove2.me/theorems/fd13f640-1c68-4ef2-816e-dfb16d671ec2
-- title:
--   Orthogonal projector $\Pi_S$ onto a subspace $S\subseteq\mathbb R^n$
-- statement:
--   For a linear subspace $S\subseteq\mathbb R^n$ (with the standard inner product), $\Pi_S v$ is the orthogonal projection of $v$ onto $S$: the unique $w\in S$ with $v-w\perp S$.
--
--   It is used to define the projection $P(M)$ onto a row space and the projection $P(UX)$ under the uniform subspace law.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), §6.3, p.56

import Mathlib

open Matrix

namespace RandomLPIPM

/-- **Orthogonal projector onto a subspace `S ⊆ ℝⁿ`**, applied to a vector. Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), §6.3 p.56
("for a subspace `S ⊆ ℝⁿ` let `Π_S` denote the orthogonal projector onto `S`").

**Formalization Note.** `S` is a subspace of `EuclideanSpace ℝ (Fin n)` (the standard inner
product); the projection is Mathlib's `Submodule.starProjection`, and the result is read back as a
plain vector `Fin n → ℝ`. -/
noncomputable def orthProj {n : ℕ} (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (v : Fin n → ℝ) : Fin n → ℝ :=
  WithLp.ofLp (S.starProjection (WithLp.toLp 2 v))

end RandomLPIPM


