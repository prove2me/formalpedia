-- Prove2me | Definitions.Def_ShortWDRODual_Tight_Setting
-- name    : ShortWDRODual_Tight_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:31.425301+00:00
-- url     : https://prove2.me/theorems/ebbb0c29-6759-4147-aa56-03341f76cc68
-- title:
--   §2.1 (IP), p. 3 and Proposition 2, p. 7 — couplings Γ_ℙ̂, the pointwise supremum Φ, the (IP) clause, and φ(x̂, x) = f(x) − λd(x̂, x)^p
-- statement:
--   This module fixes the objects of Proposition 2 of Zhang, Yang and Gao.
--
--   Let $(\mathcal X,\mathcal F)$ be a measurable space and $\widehat{\mathbb P}$ a probability measure on it. Expectations take values in the extended reals $\overline{\mathbb R}=\mathbb R\cup\{\pm\infty\}$: for $\varphi:\mathcal X\to\overline{\mathbb R}$, $\mathbb E_\nu[\varphi]=\int\varphi^+\,d\nu-\int\varphi^-\,d\nu$ (the published definition `extIntegral`).
--
--   1. **Couplings with first marginal $\widehat{\mathbb P}$.** $\Gamma_{\widehat{\mathbb P}}$ is the set of probability measures $\gamma$ on $(\mathcal X\times\mathcal X,\mathcal F\otimes\mathcal F)$ whose first marginal is $\widehat{\mathbb P}$; the second marginal is free.
--   2. **Pointwise supremum.** For $\varphi:\mathcal X\times\mathcal X\to\overline{\mathbb R}$,
--   $$\Phi(\widehat x)=\sup_{x\in\mathcal X}\varphi(\widehat x,x).$$
--   3. **The interchangeability clause.** $\varphi$ satisfies the clause of the interchangeability principle (IP) if $\Phi$ is $\widehat{\mathbb P}$-measurable (measurable for the completion $\mathcal F_{\widehat{\mathbb P}}$ of $\mathcal F$ under $\widehat{\mathbb P}$) and
--   $$\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_{x\in\mathcal X}\varphi(\widehat X,x)\Big]=\sup_{\gamma\in\Gamma_{\widehat{\mathbb P}}}\mathbb E_{(\widehat X,X)\sim\gamma}[\varphi(\widehat X,X)].$$
--   4. **The $p$-Wasserstein integrand.** On a metric space $(\mathcal X,d)$, for $f:\mathcal X\to\mathbb R$ and real $\lambda,p$,
--   $$\varphi(\widehat x,x)=f(x)-\lambda\,d(\widehat x,x)^p .$$
--
--   (IP) is the condition under which the paper's strong duality for Wasserstein distributionally robust optimization holds; Proposition 2 verifies it for the $p$-Wasserstein integrand.
--
--   **Formalization Note** The page defines (IP) for an $(\mathcal F\otimes\mathcal F)$-measurable $\varphi$ with values in $\mathbb R\cup\{-\infty\}$. This module states only the clause; each result states its own measurability hypothesis on $\varphi$, because Proposition 2 applies (IP) to a $\varphi$ that is only $(\mathcal F\otimes\mathcal F_{\widehat{\mathbb P}})$-measurable. For such $\varphi$ the page does not say how $\mathbb E_\gamma[\varphi]$ is defined; here it is `extIntegral γ φ`, built from lower Lebesgue integrals (`lintegral`), which are defined for every function and agree with the integral against the completion of $\gamma$ whenever $\varphi$ is $\gamma$-null-measurable. In `extIntegral`, $\infty-\infty=-\infty$. $d(\widehat x,x)^p$ is the real power of a nonnegative number, and the cost is finite, so the paper's convention $0\cdot\infty=\infty$ plays no role.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, §2.1 (IP), p. 3 (PDF p. 3) and Proposition 2, p. 7 (PDF p. 7)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.Tight

open MeasureTheory ModelRiskOT.Duality

/-- The `p`-Wasserstein integrand of Proposition 2, p. 7:
`φ(x̂, x) = f(x) − λ d(x̂, x)^p`, real valued, as an element of `ℝ̄`. -/
noncomputable def pWassIntegrand {X : Type*} [MetricSpace X] (f : X → ℝ) (lam p : ℝ) :
    X × X → EReal :=
  fun q => ((f q.2 - lam * dist q.1 q.2 ^ p : ℝ) : EReal)

end ShortWDRODual.Tight


