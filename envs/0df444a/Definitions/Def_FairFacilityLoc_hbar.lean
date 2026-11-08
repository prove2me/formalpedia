-- Prove2me | Definitions.Def_FairFacilityLoc_hbar
-- name    : FairFacilityLoc_hbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:06.63588+00:00
-- url     : https://prove2.me/theorems/57714b16-c221-424f-9e8e-d7978cd7fb45
-- title:
--   The functions $\gamma,\eta,q,\bar h,\omega,g$
-- statement:
--   For $t\in[0,1]$, a real $d$ and a penalty parameter $b$:
--   $$\gamma(t)=(1+t)(1-(1-b)t),\quad \eta(t)=(1+b)t(1+t),\quad q(t)=t(1+2t),$$
--   $\bar h(t)$ is the positive solution of $(1+\eta(t))h^2-\eta(t)h=dt^2$, namely
--   $$\bar h(t)=\frac{\eta(t)+\sqrt{\eta(t)^2+4(1+\eta(t))dt^2}}{2(1+\eta(t))},$$
--   and $\omega(t)=\eta\bar h/((1+\eta)\bar h+1)$, $g(\xi)=\bar h(\sqrt\xi)^2$.
--
--   They bound the share of a coordinate in the estimate of the weighted capacity.
--
--   **Formalization Note** The explicit formulas give the printed values $\bar h(0)=0$ and $\omega(0)=0$, and their denominators are positive for $b\ge0$ and $t\ge0$.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), pp.36–38 (PDF pp.38–40), (3.20)

import Mathlib

namespace FairFacilityLoc

/-- `η(t) = (1 + b) t (1 + t)` (Yan, Zhou, manuscript, sha256 642a1268…, p.36, PDF p.38), with a general penalty
parameter `b` as in Lemma 3.21. -/
def etaFun (b t : ℝ) : ℝ := (1 + b) * t * (1 + t)

/-- `γ(t) = (1 + t)(1 − (1 − b) t)`, p.36, PDF p.38. -/
def gammaFun (b t : ℝ) : ℝ := (1 + t) * (1 - (1 - b) * t)

/-- `q(t) = t (1 + 2t)`, p.36, PDF p.38. -/
def qFun (t : ℝ) : ℝ := t * (1 + 2 * t)

/-- **The root `h̄(t)`**, p.37, PDF p.39: the positive solution of `(1 + η(t)) h² − η(t) h = d t²`, given by
`h̄(t) = (η(t) + √(η(t)² + 4 (1 + η(t)) d t²)) / (2 (1 + η(t)))`.

**Formalization Note.** The explicit formula, which also gives the printed `h̄(0) = 0`. `d` is a real number, as
in Lemma 3.21. -/
noncomputable def hbar (d b t : ℝ) : ℝ :=
  (etaFun b t + √(etaFun b t ^ 2 + 4 * (1 + etaFun b t) * d * t ^ 2)) / (2 * (1 + etaFun b t))

/-- **`ω(t) = η h̄ / ((1 + η) h̄ + 1)`**, Lemma 3.20, p.38, PDF p.40. The formula also gives the printed
`ω(0) = 0`, because `η(0) = 0`. -/
noncomputable def omegaFun (d b t : ℝ) : ℝ :=
  etaFun b t * hbar d b t / ((1 + etaFun b t) * hbar d b t + 1)

/-- **`g(ξ) = h̄(√ξ)²`**, p.38, PDF p.40. -/
noncomputable def gEnvelope (d b ξ : ℝ) : ℝ :=
  hbar d b (√ξ) ^ 2

end FairFacilityLoc


