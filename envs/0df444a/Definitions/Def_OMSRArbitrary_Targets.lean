-- Prove2me | Definitions.Def_OMSRArbitrary_Targets
-- name    : OMSRArbitrary_Targets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:05.300496+00:00
-- url     : https://prove2.me/theorems/b2319aea-deb0-46e9-a773-428ba62ed190
-- title:
--   The targets $\gamma(x,\pi)$ and $\gamma_\Lambda(x,\pi)$
-- statement:
--   For $x\in[0,1]$ and $\pi\ge0$ let
--   $$\beta^1(x,\pi)=g(x)\,\mathbf 1\{1-g(x)>\pi\},\qquad \beta^2(x,\pi)=\big(\sigma(x)g(x)+1-g(x)-\pi\big)\mathbf 1\{1-g(x)>\pi\},$$
--   and, with weights,
--   $$w(x,\pi)=\min\Big\{1,\frac{1-g(x)-\pi}{(1-g(x))(1-\sigma_\Lambda(x))}\Big\}\quad(\text{read as }1\text{ if }\sigma_\Lambda(x)=1),$$
--   $$\beta^1_\Lambda(x,\pi)=\big(g(x)-c(x)+c(x)w(x,\pi)\big)\mathbf 1\{1-g(x)>\pi\},\qquad \beta^2_\Lambda(x,\pi)=\big(1-g(x)-\pi+(g(x)-c(x))\sigma_\Lambda(x)+c(x)w(x,\pi)\big)\mathbf 1\{1-g(x)>\pi\}.$$
--   The two targets are
--   $$\gamma(x,\pi)=\pi+\min\{\beta^1(x,\pi),\beta^2(x,\pi)\},\qquad \gamma_\Lambda(x,\pi)=\pi+\min\{\beta^1_\Lambda(x,\pi),\beta^2_\Lambda(x,\pi)\}.$$
--
--   The dual solution of the analysis pays $r_ip_{it}\gamma(u,\pi_t)$ (or $\gamma_\Lambda$) at each arrival where OPT could match resource $i$; Lemma 7 integrates the targets to the guarantees.
--
--   **Formalization Note** $\sigma_\Lambda=\rho\sigma$ with $\rho=1/\Lambda$; "read as 1" is an explicit case split.
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, §3.1 (Targets), pp.14–15

import Mathlib
import Definitions.Def_OMSRArbitrary_Guarantees

noncomputable section

namespace OMSRArbitrary

/-- `β¹(x, π) := g(x) 1{1 − g(x) > π}`, arXiv:2611.03598, §3.1 ("Targets"), p.14. -/
def beta1 (g : ℝ → ℝ) (x π : ℝ) : ℝ := if π < 1 - g x then g x else 0

/-- `β²(x, π) := (σ(x)g(x) + 1 − g(x) − π) 1{1 − g(x) > π}`, arXiv:2611.03598, §3.1, p.14. -/
def beta2 (g : ℝ → ℝ) (x π : ℝ) : ℝ :=
  if π < 1 - g x then sigma g x * g x + 1 - g x - π else 0

/-- `w(x, π) := min{1, (1 − g(x) − π)/((1 − g(x))(1 − σ_Λ(x)))}` "(read as 1 if σ_Λ(x) = 1)",
arXiv:2611.03598, §3.1, p.14, with `σ_Λ = ρ σ`.

**Formalization Note.** "Read as 1 if σ_Λ(x) = 1" is the explicit `if`. -/
def wfun (g : ℝ → ℝ) (ρ x π : ℝ) : ℝ :=
  if sigmaW g ρ x = 1 then 1 else
    min 1 ((1 - g x - π) / ((1 - g x) * (1 - sigmaW g ρ x)))

/-- `β¹_Λ(x, π) := (g(x) − c(x) + c(x) w(x, π)) 1{1 − g(x) > π}`, arXiv:2611.03598, §3.1, p.14. -/
def beta1W (g c : ℝ → ℝ) (ρ x π : ℝ) : ℝ :=
  if π < 1 - g x then g x - c x + c x * wfun g ρ x π else 0

/-- `β²_Λ(x, π) := (1 − g(x) − π + (g(x) − c(x))σ_Λ(x) + c(x) w(x, π)) 1{1 − g(x) > π}`,
arXiv:2611.03598, §3.1, p.14. -/
def beta2W (g c : ℝ → ℝ) (ρ x π : ℝ) : ℝ :=
  if π < 1 - g x then 1 - g x - π + (g x - c x) * sigmaW g ρ x + c x * wfun g ρ x π else 0

/-- **The unweighted target** `γ(x, π) := π + min{β¹(x, π), β²(x, π)}`, arXiv:2611.03598,
§3.1, p.15. -/
def gamma (g : ℝ → ℝ) (x π : ℝ) : ℝ := π + min (beta1 g x π) (beta2 g x π)

/-- **The weighted target** `γ_Λ(x, π) := π + min{β¹_Λ(x, π), β²_Λ(x, π)}`, arXiv:2611.03598,
§3.1, p.15 (`ρ = 1/Λ`). -/
def gammaW (g c : ℝ → ℝ) (ρ x π : ℝ) : ℝ := π + min (beta1W g c ρ x π) (beta2W g c ρ x π)

end OMSRArbitrary


