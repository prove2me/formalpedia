-- Prove2me | Definitions.Def_SCInfoDesign_Intersecting_Setting
-- name    : SCInfoDesign_Intersecting_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:06.352689+00:00
-- url     : https://prove2.me/theorems/81b35822-2554-4674-afae-4b0293352f97
-- title:
--   §2, §4, App. C.1 — intersecting uniform supports: newsvendor (2), policies and Bayes' rule (1), best responses and (3), K_IS (B.1), thresholds and Γ*_IS (7)
-- statement:
--   This definition file sets up the model of Candogan and Gurkan for a retailer who designs the information she discloses to a supplier.
--
--   **Demand and parameters.** The state $\omega\in\{0,1\}$ has prior $\mathbb P(\omega=0)=p_0$. In state $\omega$ the retailer's demand $D_\omega$ is uniform on $[a_\omega,b_\omega]$. The parameters $a_0,b_0,a_1,b_1$ and the critical ratio $\xi$ are bundled in a record; the expectation of $f(D)$ for $D\sim U[a,b]$ is $\frac{1}{b-a}\int_a^b f(x)\,dx$.
--
--   **Supplier.** At belief $p=\mathbb P(\omega=0)$ the supplier chooses a production quantity $Q\ge 0$ minimizing the normalized newsvendor cost (2)
--   $$
--   p\,\mathbb E\big[\xi(D_0-Q)^+ + (1-\xi)(Q-D_0)^+\big] + (1-p)\,\mathbb E\big[\xi(D_1-Q)^+ + (1-\xi)(Q-D_1)^+\big].
--   $$
--   A **best-response profile** is a function $Q^*:\mathbb R\to\mathbb R$ such that $Q^*(p)$ minimizes (2) for every $p\in[0,1]$.
--
--   **Retailer.** Her expected shortage at belief $p$ and quantity $Q$ is $p\,\mathbb E[(D_0-Q)^+]+(1-p)\,\mathbb E[(D_1-Q)^+]$. A **policy** on a finite message space $\mathcal M$ is a family $\pi(m\mid\omega)\ge 0$ with $\sum_m\pi(m\mid\omega)=1$ for each $\omega$. Message $m$ has probability $\mathbb P(m)=p_0\pi(m\mid 0)+(1-p_0)\pi(m\mid 1)$, and the supplier's posterior is given by Bayes' rule (1), $p_0\pi(m\mid 0)/\mathbb P(m)$. The objective (3) of a policy $\pi$ with profile $Q^*$ is
--   $$
--   \sum_{m\in\mathcal M}\mathbb P(m)\Big(p_m\,\mathbb E[(D_0-Q^*(p_m))^+]+(1-p_m)\,\mathbb E[(D_1-Q^*(p_m))^+]\Big),
--   $$
--   where $p_m$ is the posterior after $m$. A policy is **optimal** at $p_0$ if, together with some best-response profile, its objective is at most that of every policy on every finite message space under every best-response profile. **Full disclosure** sends message $i$ exactly in state $i$; **no disclosure** sends a single message in both states.
--
--   **The function $K_{\mathsf{IS}}$** of (B.1) is $K_{\mathsf{IS}}(p)=p\,\mathbb E[(D_0-Q^*_p)^+]+(1-p)\,\mathbb E[(D_1-Q^*_p)^+]$, with $Q^*_p$ the largest optimal quantity at belief $p$ (the optimal quantity is unique in this mission).
--
--   **Constants.** $\delta_u=b_0-b_1$, $\delta_d=a_0-a_1$, $\delta_{\mathsf{IS}}=b_1-a_0$; $\underline\tau_{\mathsf{IS}}(p)=(1-p)(a_0-a_1)/(b_1-a_1)$ and $\bar\tau_{\mathsf{IS}}(p)=1-p(b_0-b_1)/(b_0-a_0)$; $\breve\xi=(\delta_d-2\delta_u)/(\delta_d-\delta_u)$ and $\breve p=1-\xi(b_1-a_1)/(a_0-a_1)$. The three branches of the quantity formula (6) are named separately. The policy $\Gamma^*_{\mathsf{IS}}$ of (7) has messages $m_0,m_1$ with
--   $$
--   \pi^*_{\mathsf{IS}}(m_0\mid\omega=0)=1,\qquad \pi^*_{\mathsf{IS}}(m_0\mid\omega=1)=\frac{\xi(b_1-a_1)}{(a_0-a_1)-\xi(b_1-a_1)}\cdot\frac{p_0}{1-p_0},
--   $$
--   and $\pi^*_{\mathsf{IS}}(m_1\mid\cdot)$ completing each row to one.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** States are `Fin 2` and messages are any finite type; the paper's footnote 8 does not bound the message space, and finite spaces are the standard Kamenica–Gentzkow setting. The supplier's cost is divided by $C_s+C_e>0$, which leaves its minimizers unchanged, so $\xi=C_s/(C_s+C_e)\in(0,1)$ is the only cost parameter. No disclosure is the one-message policy (every uninformative policy has the same cost). A message of probability $0$ gets the junk posterior $0$ and weight $0$. $K_{\mathsf{IS}}$ uses the supremum of the optimal set (the retailer-preferred best response); the supplier's response is an argmin of (2), never the closed form (6). The parameter hypotheses are stated in each theorem. The uniform expectation, policies, message probabilities, posteriors, full disclosure and no disclosure are the shared declarations of `SCInfoDesign.Nested.Setting` (identical objects), used here by their qualified names.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), pp. 6–8, (1)–(3); p. 15, Propositions 2–3, (6), (7); p. 24, (B.1); p. 31, Lemma 2

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Nested_Setting

namespace SCInfoDesign.Intersecting

/-- The parameters of the model (Candogan–Gurkan, §2, pp. 6–8): the demand supports
`[a₀, b₀]` (state `ω = 0`) and `[a₁, b₁]` (state `ω = 1`), and the supplier's critical ratio
`ξ = C_s / (C_s + C_e)`. The standing hypotheses and the intersecting-support configuration
`b₀ > b₁ > a₀ > a₁` (§4, p. 15) are stated as hypotheses of each theorem. -/
structure Params where
  a₀ : ℝ
  b₀ : ℝ
  a₁ : ℝ
  b₁ : ℝ
  ξ : ℝ

namespace Params

variable (P : Params)

/-- The supplier's newsvendor cost (2) at belief `p` and quantity `Q`, normalized by
`C_s + C_e`: `p E[ξ(D₀ − Q)⁺ + (1 − ξ)(Q − D₀)⁺] + (1 − p) E[ξ(D₁ − Q)⁺ + (1 − ξ)(Q − D₁)⁺]`. -/
noncomputable def supplierCost (p Q : ℝ) : ℝ :=
  p * SCInfoDesign.Nested.uniformMean P.a₀ P.b₀ (fun d => P.ξ * max (d - Q) 0 + (1 - P.ξ) * max (Q - d) 0) +
  (1 - p) * SCInfoDesign.Nested.uniformMean P.a₁ P.b₁ (fun d => P.ξ * max (d - Q) 0 + (1 - P.ξ) * max (Q - d) 0)

/-- `Q` is an optimal solution of (2) at belief `p`. -/
def IsOptimalQuantity (p Q : ℝ) : Prop :=
  0 ≤ Q ∧ ∀ Q', 0 ≤ Q' → P.supplierCost p Q ≤ P.supplierCost p Q'

/-- The retailer's expected shortage `p E[(D₀ − Q)⁺] + (1 − p) E[(D₁ − Q)⁺]`. -/
noncomputable def retailerCost (p Q : ℝ) : ℝ :=
  p * SCInfoDesign.Nested.uniformMean P.a₀ P.b₀ (fun d => max (d - Q) 0) +
  (1 - p) * SCInfoDesign.Nested.uniformMean P.a₁ P.b₁ (fun d => max (d - Q) 0)

/-- A best-response profile `Q* ∈ 𝓑(Γ)`: `Q*(p)` is optimal for (2) at every belief `p ∈ [0,1]`. -/
def IsBestResponseProfile (Qs : ℝ → ℝ) : Prop :=
  ∀ p ∈ Set.Icc (0:ℝ) 1, P.IsOptimalQuantity p (Qs p)

/-- The objective of the design problem (3): the retailer's expected shortage under policy `π`
and best-response profile `Qs`, at prior `p₀`. -/
noncomputable def expectedCost {M : Type} [Fintype M] (p₀ : ℝ) (π : Fin 2 → M → ℝ)
    (Qs : ℝ → ℝ) : ℝ :=
  ∑ m, SCInfoDesign.Nested.msgProb p₀ π m *
    P.retailerCost (SCInfoDesign.Nested.posterior p₀ π m) (Qs (SCInfoDesign.Nested.posterior p₀ π m))

/-- `π` solves the design problem (3) at prior `p₀`: it is a policy and, with some best-response
profile, its cost is at most that of every policy on every finite message space under every
best-response profile. -/
def IsOptimalPolicy {M : Type} [Fintype M] (p₀ : ℝ) (π : Fin 2 → M → ℝ) : Prop :=
  SCInfoDesign.Nested.IsPolicy π ∧ ∃ Qs : ℝ → ℝ, P.IsBestResponseProfile Qs ∧
    ∀ (M' : Type) [Fintype M'] (π' : Fin 2 → M' → ℝ) (Qs' : ℝ → ℝ),
      SCInfoDesign.Nested.IsPolicy π' → P.IsBestResponseProfile Qs' → P.expectedCost p₀ π Qs ≤ P.expectedCost p₀ π' Qs'

/-- The retailer-preferred optimal quantity: the largest optimal solution of (2) (its supremum;
the optimal set is a singleton under the hypotheses of this mission, Proposition 2). -/
noncomputable def prefQ (p : ℝ) : ℝ :=
  sSup {Q : ℝ | P.IsOptimalQuantity p Q}

/-- `K_IS(p)` of (B.1): the retailer's expected shortage when both hold belief `p` and the
supplier best-responds. -/
noncomputable def K (p : ℝ) : ℝ :=
  P.retailerCost p (P.prefQ p)

/-- `δ_u = b₀ − b₁` (Proposition 3). -/
def δu : ℝ := P.b₀ - P.b₁

/-- `δ_d = a₀ − a₁` (Proposition 3). -/
def δd : ℝ := P.a₀ - P.a₁

/-- `δ_IS = b₁ − a₀` (Proposition 3). -/
def δIS : ℝ := P.b₁ - P.a₀

/-- `τ̲_IS(p) = (1 − p)(a₀ − a₁)/(b₁ − a₁)` (Proposition 2). -/
noncomputable def τlowIS (p : ℝ) : ℝ := (1 - p) * (P.a₀ - P.a₁) / (P.b₁ - P.a₁)

/-- `τ̄_IS(p) = 1 − p(b₀ − b₁)/(b₀ − a₀)` (Proposition 2). -/
noncomputable def τbarIS (p : ℝ) : ℝ := 1 - p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀)

/-- `ξ̆ = (δ_d − 2δ_u)/(δ_d − δ_u)` (Lemma 2). -/
noncomputable def ξbreve : ℝ := (P.δd - 2 * P.δu) / (P.δd - P.δu)

/-- `p̆ = 1 − ξ(b₁ − a₁)/(a₀ − a₁)` (Lemma 2). -/
noncomputable def pbreve : ℝ := 1 - P.ξ * (P.b₁ - P.a₁) / (P.a₀ - P.a₁)

/-- First branch of (6): `(ξ − (1 − p))(b₀ − a₀)/p + a₀`. -/
noncomputable def qHigh (p : ℝ) : ℝ := (P.ξ - (1 - p)) * (P.b₀ - P.a₀) / p + P.a₀

/-- Second branch of (6):
`(b₀ − a₀)[(b₁ − a₁)ξ − (1 − p)(a₀ − a₁)] / ((1 − p)(b₀ − a₀) + p(b₁ − a₁)) + a₀`. -/
noncomputable def qMid (p : ℝ) : ℝ :=
  (P.b₀ - P.a₀) * ((P.b₁ - P.a₁) * P.ξ - (1 - p) * (P.a₀ - P.a₁)) /
    ((1 - p) * (P.b₀ - P.a₀) + p * (P.b₁ - P.a₁)) + P.a₀

/-- Third branch of (6): `ξ(b₁ − a₁)/(1 − p) + a₁`. -/
noncomputable def qLow (p : ℝ) : ℝ := P.ξ * (P.b₁ - P.a₁) / (1 - p) + P.a₁

/-- The partial-disclosure policy `Γ*_IS` of (7) on `𝓜*_IS = {m₀, m₁}` (`m₀ = 0`, `m₁ = 1`):
`π*_IS(m₀ | ω = 0) = 1` and
`π*_IS(m₀ | ω = 1) = ξ(b₁ − a₁)/((a₀ − a₁) − ξ(b₁ − a₁)) · p₀/(1 − p₀)`;
`π*_IS(m₁ | ·)` completes each row to `1`. -/
noncomputable def gammaStarIS (p₀ : ℝ) : Fin 2 → Fin 2 → ℝ :=
  let r := P.ξ * (P.b₁ - P.a₁) / ((P.a₀ - P.a₁) - P.ξ * (P.b₁ - P.a₁)) * (p₀ / (1 - p₀))
  ![![1, 0], ![r, 1 - r]]

end Params

end SCInfoDesign.Intersecting


