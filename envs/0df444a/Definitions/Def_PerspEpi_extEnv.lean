-- Prove2me | Definitions.Def_PerspEpi_extEnv
-- name    : PerspEpi_extEnv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:45.421033+00:00
-- url     : https://prove2.me/theorems/de115b71-b6c0-4692-b432-52f29b642fe6
-- title:
--   Extended Moreau envelope $p_f$
-- statement:
--   For $f \in \Gamma_0(E)$ the **extended Moreau envelope** is the function on $E\times\mathbb R$
--
--   $$
--   p_f(x,\lambda) = \begin{cases} e_\lambda f(x) & \lambda > 0,\\ f(x) & \lambda = 0,\\ +\infty & \lambda < 0. \end{cases}
--   $$
--
--   By Proposition 4(a) it is the natural extension of the envelope to $\lambda = 0$; Corollary 6 shows $p_f \in \Gamma_0(E\times\mathbb R)$ and computes its conjugate and subdifferential.
--
--   **Formalization Note** Defined on the Euclidean space `WithLp 2 (E × ℝ)`, so that its conjugate and subdifferential are taken with the inner product $\langle x,y\rangle + \lambda\mu$.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §4.1, p.14 (boxed display)

import Mathlib
import Definitions.Def_MoreauChance_Consistency_Basic

namespace PerspEpi

/-- **Extended Moreau envelope** `p_f`. Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §4.1, p.14 (boxed):
"p_f : (x,λ) ∈ E × ℝ ↦ e_λ f(x) if λ > 0; f(x) if λ = 0; +∞ if λ < 0."

**Formalization Note.** `e_λ f` is the published `MoreauChance.Consistency.moreauEnv`. Defined on the Euclidean space
`WithLp 2 (E × ℝ)` (inner product `⟨x, y⟩ + λμ`), so that its conjugate and subdifferential (Corollary 6) are the paper's. -/
noncomputable def extEnv {E : Type*} [NormedAddCommGroup E] (f : E → EReal)
    (q : WithLp 2 (E × ℝ)) : EReal :=
  if 0 < q.snd then MoreauChance.Consistency.moreauEnv f q.snd q.fst else if q.snd = 0 then f q.fst else ⊤

end PerspEpi


