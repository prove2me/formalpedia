-- Prove2me | Definitions.Def_SelfSelReg_modelCondLaw
-- name    : SelfSelReg_modelCondLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:56.750621+00:00
-- url     : https://prove2.me/theorems/2142a2a4-cc75-408c-804e-18722284fb8d
-- title:
--   The conditional law of $(X,\xi)$ given $Y_i=t$ in the self-selection model
-- statement:
--   In the self-selection model the vector $(X,\xi,Y_i)$ is centered jointly Gaussian, $Y_i=\langle w_i,X\rangle+\xi_i$ has variance $\sigma_i^2=1+\|w_i\|_2^2$, and the covariance of $(X,\xi)$ with $Y_i$ is $(w_i,e_i)$. By Proposition 4.3, given $Y_i=t$ the vector $(X,\xi)$ is Gaussian with mean $t(w_i,e_i)/\sigma_i^2$ and covariance $I-(w_i,e_i)(w_i,e_i)^\top/\sigma_i^2$.
--
--   This file defines that law, for every $t$, as the image of the model law under
--   $$(x,\xi)\mapsto\big(x-c\,w_i,\ \xi-c\,e_i\big),\qquad c=\frac{\langle w_i,x\rangle+\xi_i-t}{\sigma_i^2}.$$
--   Under it $Y_i=t$, and the other responses $Y_j$ have the induced conditional Gaussian law. It is the meaning of "$\mathbb P(\,\cdot\mid Y_i=t)$" and "$\mathbb E_{X,\xi_i}[\,\cdot\mid Y_i=t]$" in Lemma 5.4 and Corollary 5.6.
--
--   **Formalization Note** The conditional law is defined explicitly for every $t$ (the continuous version), not as an almost-everywhere defined conditional distribution evaluated at a point.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Proposition 4.3, p.16 (PDF p.19); Lemma 5.4, p.20 (PDF p.23); Corollary 5.6, p.22 (PDF p.25)

import Mathlib
import Definitions.Def_SelfSelReg_jointLaw

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- The conditioning map for `Y_i = t` in the model: with `c = (Y_i − t)/σ_i²`,
`(x, ξ) ↦ (x − c·w_i, ξ − c·e_i)`. `(w_i, e_i)` is the covariance of `(X, ξ)` with `Y_i`, and the
image satisfies `Y_i = t`. -/
noncomputable def modelCondMap {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n)) (i : Fin k)
    (t : ℝ) (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) :=
  let c := (response w z.1 z.2 i - t) / (1 + ‖w i‖ ^ 2)
  (z.1 - c • w i, z.2 - c • EuclideanSpace.single i (1 : ℝ))

/-- **The conditional law of `(X, ξ)` given `Y_i = t`** in the self-selection model
(Proposition 4.3 applied to the jointly Gaussian vector `(X, ξ, Y_i)`).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Proposition 4.3, p.16 (PDF p.19); used as "E_{X,ξ_i}[· | Y_i = t]" and
"P(· | Y_i = t)" in Lemma 5.4, Corollary 5.6 (pp.20–22, PDF pp.23–25).

`modelCondLaw w i t` is the pushforward of `jointLaw n k` under `modelCondMap w i t`: the Gaussian law
of `(X, ξ)` with mean `t(w_i, e_i)/σ_i²` and covariance `I − (w_i, e_i)(w_i, e_i)ᵀ/σ_i²`.

**Formalization Note.** This is the conditional law of Proposition 4.3, defined for every `t`, not an
almost-everywhere defined conditional distribution evaluated at a point. Under it `Y_i = t` and the
other responses have the induced conditional Gaussian law (used in the proof of Lemma 5.4). -/
noncomputable def modelCondLaw {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n)) (i : Fin k)
    (t : ℝ) : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) :=
  (jointLaw n k).map (modelCondMap w i t)

end SelfSelReg


