-- Prove2me | Definitions.Def_PerspEpi_extProx
-- name    : PerspEpi_extProx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:30.586014+00:00
-- url     : https://prove2.me/theorems/d91ba123-cffd-4b1f-b4dd-2b56d1b7ad78
-- title:
--   Extended proximal map $P_f$
-- statement:
--   For $f \in \Gamma_0(E)$ the **extended proximal map** is the set-valued map $P_f : E \times \mathbb R \rightrightarrows E$,
--
--   $$
--   P_f(x,\lambda) = \begin{cases} P_\lambda f(x) & \lambda > 0,\\ P_{\operatorname{cl}(\operatorname{dom} f)}(x) & \lambda = 0,\\ \emptyset & \lambda < 0. \end{cases}
--   $$
--
--   Proposition 5 motivates the value at $\lambda = 0$, and Corollary 7 establishes its continuity and Lipschitz properties.
--
--   **Formalization Note** Encoded as `E × ℝ → Set E`: a singleton for $\lambda \ge 0$, empty for $\lambda < 0$.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §4.3, p.16 (boxed display)

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PerspEpi_projC
import Definitions.Def_PerspEpi_prox

namespace PerspEpi

/-- **Extended proximal map** `P_f`. Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §4.3, p.16 (boxed):
"P_f : E × ℝ ⇉ E, P_f(x,λ) := P_λ f(x) if λ > 0; P_cl(dom f)(x) if λ = 0; ∅ if λ < 0."

**Formalization Note.** A set-valued map, encoded as `E × ℝ → Set E`: a singleton for `λ ≥ 0`,
empty for `λ < 0`. -/
noncomputable def extProx {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (q : E × ℝ) :
    Set E :=
  if 0 < q.2 then {prox f q.2 q.1} else if q.2 = 0 then {projC (closure (AubinLipschitz.effDom f)) q.1} else ∅

end PerspEpi


