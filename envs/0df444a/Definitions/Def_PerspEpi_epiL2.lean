-- Prove2me | Definitions.Def_PerspEpi_epiL2
-- name    : PerspEpi_epiL2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:31.120043+00:00
-- url     : https://prove2.me/theorems/76056c94-3ac0-4c87-ba31-0df9733f79aa
-- title:
--   Epigraph in the Euclidean space $E\times\mathbb R$
-- statement:
--   The epigraph $\operatorname{epi} f = \{(x,\alpha) \mid f(x) \le \alpha\}$ of $f : E \to \overline{\mathbb R}$, viewed as a subset of the Euclidean space $E \times \mathbb R$ with
--
--   $$
--   \langle (x,\alpha),(y,\beta)\rangle = \langle x,y\rangle + \alpha\beta,\qquad \|(x,\alpha)\|^2 = \|x\|^2 + \alpha^2 .
--   $$
--
--   This is the set onto which Corollary 14 projects; its Euclidean projection and distance are the objects of the goal theorem.
--
--   **Formalization Note** The same set as the published `ShortestGCS.MICP.epigraph f`. The carrier is `WithLp 2 (E × ℝ)`, whose norm is the Euclidean one. Lean's plain `E × ℝ` carries the sup norm, under which the nearest point of the epigraph is a different point (for $f(u)=2u$ at $(1,0)$ the Euclidean projection is $(1/5,2/5)$, the sup-norm one $(1/3,2/3)$).
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §1.2 Notation, p.4; Corollary 14, p.24

import Mathlib

namespace PerspEpi

/-- **Epigraph in the Euclidean space E × ℝ.** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §1.2 Notation, p.4
("epi f = {(x,α) ∈ E × ℝ | f(x) ≤ α}") and Corollary 14, p.24 (the Euclidean projection onto
epi f).

**Formalization Note.** The same set as the published `ShortestGCS.MICP.epigraph f`, placed in `WithLp 2 (E × ℝ)`, whose
norm is the Euclidean one `‖(x, α)‖² = ‖x‖² + α²` and whose inner product is
`⟨(x, α), (y, β)⟩ = ⟨x, y⟩ + αβ`. Lean's plain `E × ℝ` carries the sup norm, under which the
nearest point of the epigraph is a different point; the paper's E × ℝ is a Euclidean space. -/
def epiL2 {E : Type*} (f : E → EReal) : Set (WithLp 2 (E × ℝ)) :=
  {p | f p.fst ≤ (p.snd : EReal)}

end PerspEpi


