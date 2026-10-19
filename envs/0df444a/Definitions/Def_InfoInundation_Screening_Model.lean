-- Prove2me | Definitions.Def_InfoInundation_Screening_Model
-- name    : InfoInundation_Screening_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:10:41.589584+00:00
-- url     : https://prove2.me/theorems/59454ffa-0e5f-4219-aead-d55c5e8127a8
-- title:
--   §3–§4, pp. 7–11 — accuracy law 𝔾, ψ and the likelihood (5), Bayes posterior (4), Belief Updating Equations, Screening Equation, auxiliary density g
-- statement:
--   This file fixes the objects of the screening model of Allon, Drakopoulos and Manshadi.
--
--   **Posts and accuracy.** A platform shows a consumer posts about an unknown truth $\theta\in\mathbb R$. Post $i$ has value $Z_i=\theta+\Sigma_i\epsilon_i$, where $\epsilon_i\sim\mathcal N(0,1)$ and the *accuracy* $\Sigma_i$ (a standard deviation) is drawn from a publicly known law $\mathbb G$. Standing assumption (§3, p. 8): $\mathbb G$ is a probability measure on $\mathbb R$ whose support is bounded away from zero and bounded above, i.e. there are $0<\underline\sigma\le\overline\sigma$ with
--   $$\mathbb G\big([\underline\sigma,\overline\sigma]^{\mathrm c}\big)=0 .$$
--   This is the predicate `AccuracyLaw G`.
--
--   **Likelihood (5).** A consumer with normal belief $\mathcal N(\mu,s^2)$ about $\theta$ assigns to a post of value $z$, given $\Sigma=\sigma$, the likelihood
--   $$P(z\mid\sigma;\mu,s)=\psi\Big((z-\mu)^2,\sqrt{2(\sigma^2+s^2)}\Big),\qquad \psi(x,y)=\frac{1}{\sqrt\pi\,y}\exp\Big(-\frac{x}{y^2}\Big).$$
--
--   **Posterior (4).** For a function $h$ of the accuracy, the posterior expectation given the post is the Bayes ratio
--   $$\mathbb E[h(\Sigma)\mid Z=z;\mu,s]=\frac{\int h(\sigma)\,P(z\mid\sigma;\mu,s)\,d\mathbb G(\sigma)}{\int P(z\mid\sigma;\mu,s)\,d\mathbb G(\sigma)} .$$
--
--   **Belief Updating Equations** (p. 8). After reading a post of value $z$ whose accuracy estimate is $\hat\sigma$, the belief becomes $\mathcal N(\mu',s'^2)$ with
--   $$\mu'=\frac{s^2}{s^2+\hat\sigma^2}z+\frac{\hat\sigma^2}{s^2+\hat\sigma^2}\mu,\qquad s'=\sqrt{\frac{s^2\hat\sigma^2}{s^2+\hat\sigma^2}} .$$
--
--   **Scores.** Under ex-post known accuracy ($\hat\sigma=\Sigma$, case (a) on p. 8), the score of a post printed in the Screening Equation is the expected decrease in posterior standard deviation, $s-\mathbb E[s'(\Sigma)\mid Z=z]$ (`sdScore`); the prose reading "expected decrease in posterior variance" is $s^2-\mathbb E[s'(\Sigma)^2\mid Z=z]$ (`varScore`). For a menu $Z_1,\dots,Z_K$ of posts, `argmaxMenu f Z` is the set of indices maximizing $f(Z_i)$ and `closestPosts μ Z` the set of indices minimizing $(Z_i-\mu)^2$.
--
--   **Auxiliary density** (p. 11). With $r=(z-\mu)^2$, the auxiliary density is $g(\sigma)\propto d\mathbb G(\sigma)\exp\big(-r/(2(\sigma^2+s^2))\big)$; `auxMoment G s r p` is the unnormalized integral $\int(\sigma^2+s^2)^{-p}\exp\big(-r/(2(\sigma^2+s^2))\big)\,d\mathbb G(\sigma)$, and `auxExp G s r p` $=\mathbb E_g[(\Sigma^2+s^2)^{-p}]$ is its normalized version.
--
--   These are the objects of Proposition 1 and of every step of its proof.
--
--   **Formalization Note.** All quantities are real. The consumer's state is any belief mean $\mu\in\mathbb R$ and standard deviation $s$ (the theorems assume $s>0$). The likelihood is everywhere positive, so for a probability law $\mathbb G$ the denominator in (4) is positive and no division by zero occurs; likewise `auxMoment G s r 0 > 0`. `Real.sqrt` is applied only to nonnegative arguments, and the real power $(\sigma^2+s^2)^{-p}$ only to a positive base when $s>0$. The scores take $\hat\sigma=\Sigma$ inside the expectation (ex-post known accuracy, the case the proof of Proposition 1 treats); under the ex-post unknown estimate (2) the score would not involve the posterior of $\Sigma$. Neither score and neither posterior is defined through a closed form in $(z-\mu)^2$. `nextMean` is recorded for completeness of the Belief Updating Equations and is not used by the theorems. Menus are `Fin K → ℝ`, so equal-valued posts are distinct posts.
-- source:
--   Allon, Drakopoulos & Manshadi, Information Inundation on Platforms and Implications, SSRN 3385627 (version of 2020-04-05), pp. 7–11, §3, eq. (1), footnote 2, standing assumption on 𝔾 (p. 8), (Screening Equation), (Belief Updating Equations), case (a) ex-post known accuracy (p. 8), (4), (5), auxiliary density g (p. 11)

import Mathlib

namespace InfoInundation.Screening

open MeasureTheory ProbabilityTheory

/-- §3, pp. 7–8: the accuracy Σ of a post (a standard deviation) has law `G`, a probability
measure whose support is bounded away from zero and bounded from above. -/
structure AccuracyLaw (G : Measure ℝ) : Prop where
  isProb : IsProbabilityMeasure G
  bdd : ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ G (Set.Icc lo hi)ᶜ = 0

/-- p. 10: `ψ(x, y) = (1 / (√π y)) exp(−x / y²)`. -/
noncomputable def psi (x y : ℝ) : ℝ :=
  1 / (Real.sqrt Real.pi * y) * Real.exp (-(x / y ^ 2))

/-- (5), p. 10: the likelihood of the post value `z` given `Σ = σ`, for a consumer with belief
`N(μ, s²)`: `ψ((z − μ)², √(2(σ² + s²)))`. -/
noncomputable def likelihood (μ s σ z : ℝ) : ℝ :=
  psi ((z - μ) ^ 2) (Real.sqrt (2 * (σ ^ 2 + s ^ 2)))

/-- (4), p. 10: the posterior expectation `E[h(Σ) | Z = z; μ, s]`, by Bayes rule with prior `G`
on the accuracy and the likelihood (5). -/
noncomputable def postExp (G : Measure ℝ) (μ s z : ℝ) (h : ℝ → ℝ) : ℝ :=
  (∫ σ, h σ * likelihood μ s σ z ∂G) / (∫ σ, likelihood μ s σ z ∂G)

/-- (Belief Updating Equations), p. 8: the posterior mean after reading a post of value `z`
whose accuracy estimate is `σhat`. -/
noncomputable def nextMean (μ s σhat z : ℝ) : ℝ :=
  s ^ 2 / (s ^ 2 + σhat ^ 2) * z + σhat ^ 2 / (s ^ 2 + σhat ^ 2) * μ

/-- (Belief Updating Equations), p. 8: the posterior standard deviation after reading a post
whose accuracy estimate is `σhat`, `√(s² σ̂² / (s² + σ̂²))`. -/
noncomputable def nextSd (s σhat : ℝ) : ℝ :=
  Real.sqrt (s ^ 2 * σhat ^ 2 / (s ^ 2 + σhat ^ 2))

/-- (Screening Equation), p. 8, as printed: `σ_x(t) − E[σ_x(t+1; Z) | Z; μ, s]`, with ex-post
known accuracy `σ̂ = Σ` inside the expectation. -/
noncomputable def sdScore (G : Measure ℝ) (μ s z : ℝ) : ℝ :=
  s - postExp G μ s z (fun σ => nextSd s σ)

/-- The prose reading of the screening rule, p. 8, "the (expected) decrease in posterior
variance": `σ_x(t)² − E[σ_x(t+1; Z)² | Z; μ, s]`, with `σ̂ = Σ`. -/
noncomputable def varScore (G : Measure ℝ) (μ s z : ℝ) : ℝ :=
  s ^ 2 - postExp G μ s z (fun σ => (nextSd s σ) ^ 2)

open Classical in
/-- The argmax over the menu `K_x(t) = (Z_1, …, Z_K)` of a score of the post value. -/
noncomputable def argmaxMenu {K : ℕ} (f : ℝ → ℝ) (Z : Fin K → ℝ) : Finset (Fin K) :=
  Finset.univ.filter (fun i => ∀ j, f (Z j) ≤ f (Z i))

open Classical in
/-- The argmin over the menu of `(Z_i − μ)²`: the posts closest to the belief `μ`. -/
noncomputable def closestPosts {K : ℕ} (μ : ℝ) (Z : Fin K → ℝ) : Finset (Fin K) :=
  Finset.univ.filter (fun i => ∀ j, (Z i - μ) ^ 2 ≤ (Z j - μ) ^ 2)

/-- p. 11: the unnormalized moment `∫ (σ² + s²)^(−p) exp(−r / (2(σ² + s²))) dG(σ)` of the
auxiliary density `g(σ) ∝ dG(σ) exp(−r / (2(σ² + s²)))`, with `r = (Z − μ)²`. -/
noncomputable def auxMoment (G : Measure ℝ) (s r p : ℝ) : ℝ :=
  ∫ σ, (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) ∂G

/-- p. 11: the expectation `E_g[(Σ² + s²)^(−p)]` under the normalized auxiliary density `g`. -/
noncomputable def auxExp (G : Measure ℝ) (s r p : ℝ) : ℝ :=
  auxMoment G s r p / auxMoment G s r 0

end InfoInundation.Screening


