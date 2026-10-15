-- Prove2me | Definitions.Def_InfoBargaining_Monotone_Setting
-- name    : InfoBargaining_Monotone_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:18.447162+00:00
-- url     : https://prove2.me/theorems/6abea769-33eb-484a-91fd-b89f98d2aca1
-- title:
--   §2–§3.1, pp. 6–11 — truth-or-noise posterior mean, G(v, α), total ex ante surplus A(α, c) (7), buyer objective (6), the optimal set α*
-- statement:
--   This file sets up the base model of Guo, *Gathering Information before Negotiation*, §2 and §3.1.
--
--   **Prior.** The buyer's true value $u$ of one unit of the seller's product is unknown to both parties. Its prior law $F$ is a probability distribution on $\mathbb R$ with a finite mean
--   $$\hat u=\int w\,dF(w)>0 .$$
--
--   **Truth-or-noise signal.** Before negotiating, the buyer acquires a signal $w$ that equals the true $u$ with probability $\alpha$ and is an independent draw from $F$ with probability $1-\alpha$. The buyer's posterior mean is
--   $$v\equiv \alpha w+(1-\alpha)\hat u,$$
--   and, ex ante, $v$ has the distribution function
--   $$G(v,\alpha)\equiv F\!\left(\frac{v-(1-\alpha)\hat u}{\alpha}\right).$$
--
--   **Information choice.** The buyer chooses the informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$, with $\underline\alpha<\bar\alpha$, at a cost $k(\alpha)$ that is increasing on $[\underline\alpha,\bar\alpha]$, with $k(\underline\alpha)=0$ and $k(\bar\alpha)>0$.
--
--   **Surplus and objective.** The seller's cost is $c$. Trade happens exactly when $v>c$, and the parties then split the net surplus $v-c$ in proportions $\theta_s:\theta_b$, with $\theta_s+\theta_b=1$. The total ex ante surplus (7) and the buyer's ex ante net surplus (6) are
--   $$A(\alpha,c)=\int_c^{\bar v}(v-c)\,dG(v,\alpha)=\mathbb E\big[(\alpha w+(1-\alpha)\hat u-c)^+\big],\qquad U_b(\alpha)=\theta_b\,A(\alpha,c)-k(\alpha).$$
--   The optimal level of information acquisition $\alpha^*$ is a solution of (6), $\max_\alpha U_b(\alpha)$; the set of all such solutions is
--   $$\mathcal A^*(\theta_b,c)=\Big\{\alpha\in[\underline\alpha,\bar\alpha]\;:\;U_b(\alpha')\le U_b(\alpha)\ \text{for all }\alpha'\in[\underline\alpha,\bar\alpha]\Big\}.$$
--
--   These objects are shared by every statement of the mission: Proposition 1 compares the optimal sets $\mathcal A^*(\theta_b,c)$ as $\theta_b$ and $c$ vary.
--
--   **Formalization Note** The prior is a probability measure $\mu$ on $\mathbb R$ with an integrable identity (finite mean); the paper's further assumptions on $F$ (continuous and differentiable, a strictly positive density on a bounded support $[\underline u,\bar u]$) and $c\in(\underline u,\bar u)$ are dropped, so the results are stated for a larger class of priors; the paper remarks (p. 11) that its argument needs only that a higher $\alpha$ is a mean-preserving spread. $F$ is `ProbabilityTheory.cdf μ`. $A$ is written as the integral over the prior of $\max(\alpha w+(1-\alpha)\hat u-c,0)$, which is the paper's $\int_c^{\bar v}(v-c)\,dG(v,\alpha)$ after the change of variables $v=\alpha w+(1-\alpha)\hat u$; no closed form is used. The bargaining stage is not modelled: the paper's reduction (pp. 9–10) that the buyer receives the share $\theta_b$ of $(v-c)^+$ is built into $U_b$. $\alpha^*$ is the set `optSet θb c`, never a chosen maximizer; the paper does not claim uniqueness. The bargaining power $\theta_b$ and the cost $c$ are parameters, not fields of the model.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), pp. 6–11: §2 bargaining powers, prior, signal, G(v, α) (p. 7), information choice and cost k (p. 8); §3.1 (6) (p. 10), (7) (p. 11)

import Mathlib

namespace InfoBargaining.Monotone

open MeasureTheory

/-- The base model of Guo, *Gathering Information before Negotiation*, §2 (pp. 6–8).

* `μ` is the prior law `F` of the buyer's true value `u`: a probability measure on `ℝ`
  with a finite mean (`integrable`), and the mean `û = ∫ w ∂μ` is positive (`mean_pos`).
* `[αlo, αhi] ⊆ (0, 1)` is the range of the information index `α` (the page's `[α̲, ᾱ]`).
* `k` is the cost of information gathering, increasing on `[αlo, αhi]`, with
  `k αlo = 0` (the page's `k̲ = 0`) and `k αhi > 0` (the page's `k̄ > 0`). -/
structure Model where
  μ : Measure ℝ
  isProb : IsProbabilityMeasure μ
  integrable : Integrable (fun w : ℝ => w) μ
  mean_pos : 0 < ∫ w, w ∂μ
  αlo : ℝ
  αhi : ℝ
  αlo_pos : 0 < αlo
  αlo_lt_αhi : αlo < αhi
  αhi_lt_one : αhi < 1
  k : ℝ → ℝ
  k_mono : MonotoneOn k (Set.Icc αlo αhi)
  k_αlo : k αlo = 0
  k_αhi_pos : 0 < k αhi

attribute [instance] Model.isProb

namespace Model

variable (M : Model)

/-- The prior mean `û = ∫ w dF(w)`. -/
noncomputable def uhat : ℝ := ∫ w, w ∂M.μ

/-- The posterior mean `v ≡ α w + (1 - α) û` after the truth-or-noise signal `w` (p. 7). -/
noncomputable def postMean (α w : ℝ) : ℝ := α * w + (1 - α) * M.uhat

/-- The distribution of the posterior mean, `G(v, α) ≡ F((v - (1 - α) û) / α)` (p. 7),
where `F` is the cumulative distribution function of the prior `μ`. -/
noncomputable def G (v α : ℝ) : ℝ :=
  ProbabilityTheory.cdf M.μ ((v - (1 - α) * M.uhat) / α)

/-- The total ex ante surplus (7), `A(α, c) = ∫_c^{v̄} (v - c) dG(v, α)`, written as the
expectation over the prior of `(α w + (1 - α) û - c)⁺`, i.e. after the change of variables
`v = α w + (1 - α) û`. -/
noncomputable def A (α c : ℝ) : ℝ := ∫ w, max (M.postMean α w - c) 0 ∂M.μ

/-- The buyer's ex ante net surplus (6), `U_b(α) = θ_b A(α, c) - k(α)`. -/
noncomputable def Ub (θb c α : ℝ) : ℝ := θb * M.A α c - M.k α

/-- The set of solutions `α*` of the buyer's problem (6): the maximizers of `U_b` over
`[αlo, αhi]`. -/
def optSet (θb c : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc M.αlo M.αhi ∧ ∀ α' ∈ Set.Icc M.αlo M.αhi, M.Ub θb c α' ≤ M.Ub θb c α}

end Model

end InfoBargaining.Monotone


