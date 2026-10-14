-- Prove2me | Definitions.Def_SCInfoDesign_Nested_Setting
-- name    : SCInfoDesign_Nested_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:21.849548+00:00
-- url     : https://prove2.me/theorems/d1b14f19-d36c-4530-9364-97bef9a8b79b
-- title:
--   §2, pp. 5–8 and (B.1), p. 24 — uniform demand, the supplier's newsvendor (2), policies and Bayes' rule (1), best responses and the design problem (3), K, and the policy Γ* of (5)
-- statement:
--   This file sets up the supply-chain information design model of Candogan and Gurkan with **nested uniform demand supports**.
--
--   **Demand and states.** The state is $\omega\in\{0,1\}$ with prior $p_0=\mathbb P(\omega=0)$. In state $i$ demand is $D_i\sim U[a_i,b_i]$. A parameter record holds $a_0,b_0,a_1,b_1$ and the supplier's **critical ratio** $\xi=C_s/(C_s+C_e)$. For $a<b$ the uniform expectation is
--   $$\mathbb E_{U[a,b]}[f]=\frac{1}{b-a}\int_a^b f(x)\,dx .$$
--
--   **The supplier.** At belief $p=\mathbb P(\omega=0)$ the supplier chooses $Q\ge 0$ to minimize the newsvendor cost (2), normalized by $C_s+C_e$:
--   $$c_s(p,Q)=p\,\mathbb E\big[\xi(D_0-Q)^+ + (1-\xi)(Q-D_0)^+\big]+(1-p)\,\mathbb E\big[\xi(D_1-Q)^+ + (1-\xi)(Q-D_1)^+\big].$$
--   $Q$ is an *optimal quantity* at $p$ if $Q\ge0$ and $c_s(p,Q)\le c_s(p,Q')$ for every $Q'\ge 0$. A *best-response profile* $Q^*$ assigns an optimal quantity $Q^*(p)$ to every $p\in[0,1]$; this is the paper's set $\mathcal B(\Gamma)$.
--
--   **The retailer.** Her expected shortage at belief $p$ and quantity $Q$ is $c_r(p,Q)=p\,\mathbb E[(D_0-Q)^+]+(1-p)\,\mathbb E[(D_1-Q)^+]$.
--
--   **Policies.** A policy on a finite message space $\mathcal M$ is a stochastic map $\pi(m\mid\omega)\ge 0$ with $\sum_m\pi(m\mid\omega)=1$ for each $\omega$. Message $m$ has probability $\mathbb P(m)=p_0\pi(m\mid 0)+(1-p_0)\pi(m\mid 1)$ and induces the posterior of Bayes' rule (1),
--   $$p_m=\frac{\pi(m\mid 0)\,p_0}{\pi(m\mid 0)p_0+\pi(m\mid 1)(1-p_0)} .$$
--   The objective of the design problem (3) is
--   $$\mathbb E\big[c_r(p,Q^*(p))\mid\Gamma\big]=\sum_{m}\mathbb P(m)\,c_r\big(p_m,Q^*(p_m)\big),$$
--   and a policy is **optimal** at $p_0$ if, together with some best-response profile, its objective is at most that of every policy on every finite message space under every best-response profile (the joint minimum over $\Gamma$ and $Q^*\in\mathcal B(\Gamma)$ of (3)).
--
--   **Named objects.** Full disclosure sends message $m_i$ exactly in state $i$; no disclosure sends one message in both states. $K(p)=c_r(p,\bar Q_p)$ is the function (B.1), where $\bar Q_p$ is the largest optimal quantity at $p$ (the unique one under this mission's hypotheses). The thresholds are
--   $$\underline\tau(p)=\frac{p(a_1-a_0)}{b_0-a_0},\quad \bar\tau(p)=1-\frac{p(b_0-b_1)}{b_0-a_0},\quad \xi_h=\frac{a_1-a_0}{b_0-a_0-b_1+a_1},\quad \hat p=\frac{\xi(b_0-a_0)}{a_1-a_0}.$$
--   Finally $\Gamma^*$ is the two-message policy of (5): with $\mathcal M^*=\{m_0,m_1\}$,
--   $$\pi^*(m_1\mid\omega=0)=\frac{1-p_0}{p_0}\,\frac{\xi(b_0-a_0)}{(a_1-a_0)-\xi(b_0-a_0)},\qquad \pi^*(m_1\mid\omega=1)=1,$$
--   and $\pi^*(m_0\mid\cdot)$ completes each row to $1$.
--
--   These objects are the shared vocabulary of every statement in the mission.
--
--   **Formalization Note** States are `Fin 2` and messages $m_0,m_1$ are the indices $0,1$. The supplier's cost is divided by $C_s+C_e>0$, which does not change its minimizers; every $\xi\in(0,1)$ arises from some $C_s,C_e>0$. Message spaces are finite types (the paper does not bound $\mathcal M$; binary spaces already attain the optimum). No disclosure uses a single message; every uninformative policy has the same cost. A message of probability $0$ gets posterior $0$ in Lean and has weight $0$. $\bar Q_p$ is a real supremum, so it would be $0$ if the optimal set were empty or unbounded; under the hypotheses of every theorem of the mission it is a singleton. The threshold $\xi_h$ is $0/0=0$ in Lean when the supports coincide; every theorem remains the paper's there. The standing hypotheses ($a_0<b_0$, $a_1<b_1$, $0\le a_0$, $0\le a_1$, $0<\xi<1$, $a_0\le a_1$, $b_1\le b_0$) are binders of each theorem, not part of the definitions.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), pp. 6–8, §2.1–2.3, (1)–(3); p. 8, Proposition 1 (τ̲, τ̄); p. 9, Theorem 1 and (5); p. 24, (B.1); p. 25, Lemma 1 (p̂)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope

namespace SCInfoDesign.Nested

/-- The parameters of the model (Candogan–Gurkan, §2, pp. 6–8): the demand supports
`[a₀, b₀]` (state `ω = 0`) and `[a₁, b₁]` (state `ω = 1`), and the supplier's critical ratio
`ξ = C_s / (C_s + C_e)`. The standing hypotheses (`a₀ < b₀`, `a₁ < b₁`, `0 ≤ a₀`, `0 ≤ a₁`,
`0 < ξ < 1`) and the support configuration are stated as hypotheses of each theorem. -/
structure Params where
  a₀ : ℝ
  b₀ : ℝ
  a₁ : ℝ
  b₁ : ℝ
  ξ : ℝ

/-- Expectation of `f(D)` for `D` uniform on `[a, b]` (meaningful for `a < b`). -/
noncomputable def uniformMean (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in a..b, f x) / (b - a)

/-- A disclosure policy with finite message space `M`: `π ω m = π(m | ω)`, a stochastic map from
the state `ω ∈ Fin 2` to messages. -/
def IsPolicy {M : Type} [Fintype M] (π : Fin 2 → M → ℝ) : Prop :=
  (∀ ω m, 0 ≤ π ω m) ∧ ∀ ω, ∑ m, π ω m = 1

/-- Probability of message `m` under prior `p₀ = P(ω = 0)`. -/
def msgProb {M : Type} (p₀ : ℝ) (π : Fin 2 → M → ℝ) (m : M) : ℝ :=
  p₀ * π 0 m + (1 - p₀) * π 1 m

/-- The supplier's posterior `P(ω = 0 | m)` by Bayes' rule (1). A message of probability `0`
gets the value `0`; it carries weight `0` in the expected cost. -/
noncomputable def posterior {M : Type} (p₀ : ℝ) (π : Fin 2 → M → ℝ) (m : M) : ℝ :=
  p₀ * π 0 m / msgProb p₀ π m

/-- Full disclosure: message `i` is sent exactly in state `i`. -/
def fullDisclosure : Fin 2 → Fin 2 → ℝ := fun ω m => if m = ω then 1 else 0

/-- No disclosure: a single message, sent in both states. -/
def noDisclosure : Fin 2 → Unit → ℝ := fun _ _ => 1

namespace Params

variable (P : Params)

/-- The supplier's newsvendor cost (2) at belief `p` and quantity `Q`, normalized by
`C_s + C_e`: `p E[ξ(D₀ − Q)⁺ + (1 − ξ)(Q − D₀)⁺] + (1 − p) E[ξ(D₁ − Q)⁺ + (1 − ξ)(Q − D₁)⁺]`. -/
noncomputable def supplierCost (p Q : ℝ) : ℝ :=
  p * uniformMean P.a₀ P.b₀ (fun d => P.ξ * max (d - Q) 0 + (1 - P.ξ) * max (Q - d) 0) +
  (1 - p) * uniformMean P.a₁ P.b₁ (fun d => P.ξ * max (d - Q) 0 + (1 - P.ξ) * max (Q - d) 0)

/-- `Q` is an optimal solution of (2) at belief `p`. -/
def IsOptimalQuantity (p Q : ℝ) : Prop :=
  0 ≤ Q ∧ ∀ Q', 0 ≤ Q' → P.supplierCost p Q ≤ P.supplierCost p Q'

/-- The retailer's expected shortage `p E[(D₀ − Q)⁺] + (1 − p) E[(D₁ − Q)⁺]`. -/
noncomputable def retailerCost (p Q : ℝ) : ℝ :=
  p * uniformMean P.a₀ P.b₀ (fun d => max (d - Q) 0) +
  (1 - p) * uniformMean P.a₁ P.b₁ (fun d => max (d - Q) 0)

/-- A best-response profile `Q* ∈ 𝓑(Γ)`: `Q*(p)` is optimal for (2) at every belief `p ∈ [0,1]`. -/
def IsBestResponseProfile (Qs : ℝ → ℝ) : Prop :=
  ∀ p ∈ Set.Icc (0:ℝ) 1, P.IsOptimalQuantity p (Qs p)

/-- The objective of the design problem (3): the retailer's expected shortage under policy `π`
and best-response profile `Qs`, at prior `p₀`. -/
noncomputable def expectedCost {M : Type} [Fintype M] (p₀ : ℝ) (π : Fin 2 → M → ℝ)
    (Qs : ℝ → ℝ) : ℝ :=
  ∑ m, msgProb p₀ π m * P.retailerCost (posterior p₀ π m) (Qs (posterior p₀ π m))

/-- `π` solves the design problem (3) at prior `p₀`: it is a policy and, with some best-response
profile, its cost is at most that of every policy on every finite message space under every
best-response profile. -/
def IsOptimalPolicy {M : Type} [Fintype M] (p₀ : ℝ) (π : Fin 2 → M → ℝ) : Prop :=
  IsPolicy π ∧ ∃ Qs : ℝ → ℝ, P.IsBestResponseProfile Qs ∧
    ∀ (M' : Type) [Fintype M'] (π' : Fin 2 → M' → ℝ) (Qs' : ℝ → ℝ),
      IsPolicy π' → P.IsBestResponseProfile Qs' → P.expectedCost p₀ π Qs ≤ P.expectedCost p₀ π' Qs'

/-- The retailer-preferred optimal quantity: the largest optimal solution of (2) (its supremum;
the optimal set is a singleton under the hypotheses of this mission). -/
noncomputable def prefQ (p : ℝ) : ℝ :=
  sSup {Q : ℝ | P.IsOptimalQuantity p Q}

/-- `K(p)` of (B.1): the retailer's expected shortage when both hold belief `p` and the supplier
best-responds. -/
noncomputable def K (p : ℝ) : ℝ :=
  P.retailerCost p (P.prefQ p)

/-- `τ̲(p) = p(a₁ − a₀)/(b₀ − a₀)` (Proposition 1). -/
noncomputable def τlow (p : ℝ) : ℝ := p * (P.a₁ - P.a₀) / (P.b₀ - P.a₀)

/-- `τ̄(p) = 1 − p(b₀ − b₁)/(b₀ − a₀)` (Proposition 1). -/
noncomputable def τup (p : ℝ) : ℝ := 1 - p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀)

/-- The full-disclosure threshold `ξ_h = (a₁ − a₀)/(b₀ − a₀ − b₁ + a₁)` (Theorem 1). -/
noncomputable def ξh : ℝ := (P.a₁ - P.a₀) / (P.b₀ - P.a₀ - P.b₁ + P.a₁)

/-- `p̂ = ξ(b₀ − a₀)/(a₁ − a₀)` (Lemma 1). -/
noncomputable def pHat : ℝ := P.ξ * (P.b₀ - P.a₀) / (P.a₁ - P.a₀)

/-- The partial-disclosure policy `Γ*` of (5) on `𝓜* = {m₀, m₁}` (`m₀ = 0`, `m₁ = 1`):
`π*(m₁ | ω = 0) = ((1 − p₀)/p₀) · ξ(b₀ − a₀)/((a₁ − a₀) − ξ(b₀ − a₀))`, `π*(m₁ | ω = 1) = 1`,
and `π*(m₀ | ·)` completes each row to `1`. -/
noncomputable def gammaStar (p₀ : ℝ) : Fin 2 → Fin 2 → ℝ :=
  let q := (1 - p₀) / p₀ * (P.ξ * (P.b₀ - P.a₀) / ((P.a₁ - P.a₀) - P.ξ * (P.b₀ - P.a₀)))
  ![![1 - q, q], ![0, 1]]

end Params

end SCInfoDesign.Nested


