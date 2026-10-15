-- Prove2me | Definitions.Def_InfoBargaining_Uniform_Setting
-- name    : InfoBargaining_Uniform_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:56:51.440052+00:00
-- url     : https://prove2.me/theorems/353d5f32-5724-4a6f-9760-5d40f5dfc1b8
-- title:
--   §2–§3.2, pp. 7–13 — uniform-prior surplus A(α, c) (7), linear cost, buyer objective (6), optimal set, gain A(ᾱ, c) − A(α̲, c), threshold θ̃
-- statement:
--   This file sets up the bargaining model of Guo, *Gathering Information before Negotiation*, specialised to the uniform prior and the linear information cost of p. 13.
--
--   A seller with cost $c$ and a buyer with unknown value $u$ negotiate over one unit. The buyer's prior for $u$ is the uniform distribution $F(u)=u$ on $[0,1]$, with mean $\hat u = 1/2$. Before negotiating, the buyer chooses an informativeness level $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$ and observes a signal $w$ that equals $u$ with probability $\alpha$ and is an independent draw from the prior otherwise. Its posterior mean is $v=\alpha w+(1-\alpha)\hat u$. The objects defined are:
--
--   1. **Model parameters**: $0<\underline\alpha<\bar\alpha<1$ and the maximal information cost $\bar k>0$.
--   2. **Total ex ante surplus** (7): $A(\alpha,c)=\int_c^{\bar v}(v-c)\,dG(v,\alpha)$, written as the expectation over the prior of the positive part of $v-c$:
--   $$A(\alpha,c)=\int_0^1 \max\Big\{\alpha w+\frac{1-\alpha}{2}-c,\;0\Big\}\,dw .$$
--   3. **Linear information cost**: $k(\alpha)=\bar k(\alpha-\underline\alpha)/(\bar\alpha-\underline\alpha)$, so $k(\underline\alpha)=0$ and $k(\bar\alpha)=\bar k$.
--   4. **The buyer's objective** (6): $U_b(\alpha)=\theta_b A(\alpha,c)-k(\alpha)$, where $\theta_b$ is the buyer's bargaining power.
--   5. **The optimal set** $\alpha^*$: the set of maximisers of $U_b$ over $[\underline\alpha,\bar\alpha]$.
--   6. **The gain of maximal information** $\Delta(c)=A(\bar\alpha,c)-A(\underline\alpha,c)$.
--   7. **The threshold** $\tilde\theta = \bar k/\Delta(c)$ of the proof of Corollary 1, set to $1$ when $\Delta(c)\le\bar k$.
--
--   The seller's equilibrium payoffs $U_s^*=\theta_s A(\alpha^*,c)$ (material cost) and $V_s^*=c+\theta_s A(\alpha^*,c)$ (opportunity cost), with $\theta_s=1-\theta_b$, are written directly in the statements that use them.
--
--   **Formalization Note** The bargaining stage is not modelled: as the paper reduces it (pp. 9–10), the parties split any positive $v-c$ in the proportions $\theta_s:\theta_b$, so the buyer's ex ante payoff is (6) and the seller's is $\theta_s A(\alpha^*,c)$. $A$ is the integral over the prior after the change of variables $v=\alpha w+(1-\alpha)\hat u$, not the closed form of p. 13 (that closed form is a separate theorem). $\alpha^*$ is a set, because (6) need not have a unique solution. The paper's $\tilde\theta\equiv\bar k/[A(\bar\alpha,c)-A(\underline\alpha,c)]$ lies in $(0,1]$ only when the gain exceeds $\bar k$; otherwise the buyer never gathers information and $\tilde\theta=1$ is used (this also avoids Lean's convention $\bar k/0=0$). The paper's interval $[\underline\alpha,\bar\alpha]$ is taken non-degenerate.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), pp. 7–8 (model), p. 10 (6), p. 11 (7), p. 12 (U*_s, V*_s), p. 13 (linear cost, uniform prior), p. 30 (θ̃, proof of Corollary 1)

import Mathlib

namespace InfoBargaining.Uniform

/-- The exogenous parameters of the model of §2 with the linear information cost of p. 13:
the information range `[αlo, αhi] ⊆ (0, 1)` (the paper's `[α̲, ᾱ]`, taken non-degenerate) and
the maximal information cost `kbar = k̄ > 0`. -/
structure Model where
  αlo : ℝ
  αhi : ℝ
  kbar : ℝ
  αlo_pos : 0 < αlo
  αlo_lt_αhi : αlo < αhi
  αhi_lt_one : αhi < 1
  kbar_pos : 0 < kbar

/-- Total ex ante surplus (7), `A(α, c) = ∫_c^{v̄} (v − c) dG(v, α)`, for the uniform prior
`F(u) = u` on `[0, 1]` (mean `û = 1/2`). The posterior mean is `v = α w + (1 − α) û` with `w`
drawn from the prior, so (7) is the expectation of `(α w + (1 − α)/2 − c)⁺` over `w ∈ [0, 1]`. -/
noncomputable def A (α c : ℝ) : ℝ :=
  ∫ w in (0:ℝ)..1, max (α * w + (1 - α) / 2 - c) 0

namespace Model

variable (M : Model)

/-- The linear information-acquisition cost `k(α) = k̄ (α − α̲)/(ᾱ − α̲)` of p. 13. -/
noncomputable def k (α : ℝ) : ℝ := M.kbar * (α - M.αlo) / (M.αhi - M.αlo)

/-- The buyer's ex ante net surplus (6), `U_b(α) = θ_b A(α, c) − k(α)`. -/
noncomputable def Ub (θb c α : ℝ) : ℝ := θb * A α c - M.k α

/-- The set of optimal information levels `α*` solving (6) on `[α̲, ᾱ]`. -/
def optSet (θb c : ℝ) : Set ℝ :=
  {α | α ∈ Set.Icc M.αlo M.αhi ∧ ∀ α' ∈ Set.Icc M.αlo M.αhi, M.Ub θb c α' ≤ M.Ub θb c α}

/-- The gross surplus gain of maximal information, `A(ᾱ, c) − A(α̲, c)`. -/
noncomputable def gain (c : ℝ) : ℝ := A M.αhi c - A M.αlo c

/-- The bargaining-power threshold `θ̃ ≡ k̄ / [A(ᾱ, c) − A(α̲, c)]` of the proof of Corollary 1
(p. 30), set to `1` when the gain does not exceed `k̄` (then `θ̃ ∈ (0, 1]` as Corollary 1 (i)
requires, and a zero gain is not divided by). -/
noncomputable def thetaTilde (c : ℝ) : ℝ :=
  if M.gain c ≤ M.kbar then 1 else M.kbar / M.gain c

end Model

end InfoBargaining.Uniform


