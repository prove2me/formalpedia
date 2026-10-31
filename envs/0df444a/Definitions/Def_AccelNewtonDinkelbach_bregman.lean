-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_bregman
-- name    : AccelNewtonDinkelbach_bregman
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:34.448+00:00
-- url     : https://prove2.me/theorems/c39ed2c6-db83-43c2-96cc-59c8575cb271
-- title:
--   Bregman divergence $D_f(\delta',\delta)$ of a proper concave function (Definition 3.2)
-- statement:
--   Let $f:\mathbb R\to\bar{\mathbb R}$ be a proper concave function. For $\delta,\delta'\in\operatorname{dom}(f)$ with $\partial f(\delta)\neq\emptyset$, the **Bregman divergence associated with $f$** is
--
--   $$D_f(\delta',\delta)=\begin{cases} f(\delta)+\displaystyle\sup_{g\in\partial f(\delta)} g\,(\delta'-\delta)-f(\delta') & \text{if } \delta\neq\delta',\\[4pt] 0 & \text{otherwise.}\end{cases}$$
--
--   It extends the classical Bregman divergence of a differentiable, strictly concave function to arbitrary proper concave functions on the line: the supremum picks the supergradient whose tangent line lies highest at $\delta'$. By concavity it is nonnegative, and it may be $+\infty$ (for example when $\delta$ is the right endpoint of $\operatorname{dom}(f)$ and $\delta'<\delta$, so that $\partial f(\delta)$ is unbounded below). It is the potential in the analysis of the look-ahead Newton–Dinkelbach method.
--
--   **Formalization Note** The value lies in the extended reals `EReal`, so the supremum may be $+\infty$ and then $f(\delta)+(+\infty)-f(\delta')=+\infty$, as on the page. The Lean function is total; outside the paper's range (for instance when $\partial f(\delta)=\emptyset$, where the empty supremum is $-\infty$) its value is never used by the statements of this mission.
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Definition 3.2, p.7

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_superdiff

namespace AccelNewtonDinkelbach

/-- **Bregman divergence `D_f(δ′, δ)` of a proper concave function (Definition 3.2).**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Definition 3.2, p.7: "Df(δ′, δ) :=
f(δ) + sup_{g∈∂f(δ)} g(δ′ − δ) − f(δ′) if δ ≠ δ′, 0 otherwise. for all δ, δ′ ∈ dom(f) such that
∂f(δ) ≠ ∅."

`bregman dom f δ' δ` is `0` when `δ = δ'`, and otherwise
`f δ + ⨆_{g ∈ ∂f(δ)} g (δ' − δ) − f δ'`, computed in the extended reals.

**Formalization Note** The value is in `EReal` because the supremum can be `+∞` (for instance when
`δ` is the right endpoint of `dom` and `δ′ < δ`, so that `∂f(δ)` is unbounded below); then
`f δ + ⊤ − f δ' = ⊤`, which is the paper's value. The paper defines `D_f` only for
`δ, δ′ ∈ dom(f)` with `∂f(δ) ≠ ∅`; this Lean function is total, and outside that range its value
(for example `⊥` when `∂f(δ) = ∅`, the empty supremum in `EReal`) is never used by the statements
of this mission, which always evaluate it at points of `dom` with a known supergradient.
`(dom, f)` encodes a proper concave `f : ℝ → ℝ̄` as in `superdiff`. -/
noncomputable def bregman (dom : Set ℝ) (f : ℝ → ℝ) (δ' δ : ℝ) : EReal :=
  if δ = δ' then 0
  else ((f δ : ℝ) : EReal) + (⨆ g ∈ superdiff dom f δ, ((g * (δ' - δ) : ℝ) : EReal))
    - ((f δ' : ℝ) : EReal)

end AccelNewtonDinkelbach


