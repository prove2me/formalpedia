-- Prove2me | Definitions.Def_RandomLPIPM_projRow
-- name    : RandomLPIPM_projRow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:12.847311+00:00
-- url     : https://prove2.me/theorems/b2406a6d-3c2b-428d-9cd5-c97fca057ddd
-- title:
--   Projection $P(M)$ onto the row space of $M$
-- statement:
--   For $M\in\mathbb R^{d\times n}$, $P(M)$ is the orthogonal projection matrix of $\mathbb R^n$ onto the row space $\operatorname{im}[M^\top]$. When $M$ has full row rank,
--   $$P(M)=M^\top(MM^\top)^{-1}M ,$$
--   and in general $P(M)=M^\top(MM^\top)^{\dagger}M$.
--
--   The quantity $P(AX_\mu)\mathbf 1_n$ is the logarithmic speed $d\log s_\mu/d\log\mu$ of the central path, and its sup norm is the key quantity of the paper.
--
--   **Formalization Note** Defined directly as the orthogonal projector onto the row space, so it agrees with both printed formulas and has no junk case.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), (2), p.7; §3, p.22

import Mathlib
import Definitions.Def_RandomLPIPM_orthProj
import Definitions.Def_RandomLPIPM_rowSpace

open Matrix

namespace RandomLPIPM

/-- **The projection `P(M)` onto the row space of `M`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), (2) p.7: "`P(M) := Mᵀ(MMᵀ)⁻¹M`
denotes the orthogonal projection matrix onto the row space of `M`"; §3 p.22: `P(A) := Aᵀ(AAᵀ)†A`.

`projRow M v` is the orthogonal projection of `v ∈ ℝⁿ` onto `im[Mᵀ]`.

**Formalization Note.** Defined directly as the orthogonal projector onto the row space. This equals
`Aᵀ(AAᵀ)†A` for every `M`, and `Mᵀ(MMᵀ)⁻¹M` whenever `M` has full row rank, so there is no junk
case. -/
noncomputable def projRow {d n : ℕ} (M : Matrix (Fin d) (Fin n) ℝ) (v : Fin n → ℝ) :
    Fin n → ℝ :=
  orthProj (rowSpace M) v

end RandomLPIPM


