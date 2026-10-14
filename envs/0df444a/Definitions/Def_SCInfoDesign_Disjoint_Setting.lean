-- Prove2me | Definitions.Def_SCInfoDesign_Disjoint_Setting
-- name    : SCInfoDesign_Disjoint_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:06.997803+00:00
-- url     : https://prove2.me/theorems/49d49b26-5dbd-405a-8be8-b7a73a2bbace
-- title:
--   §2, pp. 5–8, §4, p. 16, App. B–C.2 — uniform demand, the supplier's newsvendor (2), policies and Bayes' rule (1), best responses, the design problem (3), K_DS (B.1), p̃ and Γ*_DS (8)
-- statement:
--   This definition fixes the model of Candogan and Gurkan's information-design game between a retailer and a supplier, in the notation of the paper.
--
--   **Data.** The state is $\omega\in\{0,1\}$ with prior $p_0=\mathbb P(\omega=0)$. In state $\omega=i$ the retailer's demand is $D_i\sim U[a_i,b_i]$. The supplier's critical ratio is $\xi=C_s/(C_s+C_e)$, where $C_s$ is his unit shortage cost and $C_e$ his unit excess cost. The five numbers $a_0,b_0,a_1,b_1,\xi$ form a parameter record $P$; the hypotheses on them (such as $a_0<b_0$ or the disjointness $b_1<a_0$) are stated in each theorem, not in the record. For $a<b$, $\mathbb E_{U[a,b]}[f]=\frac1{b-a}\int_a^b f(x)\,dx$.
--
--   **The supplier.** At belief $p=\mathbb P(\omega=0)$ the supplier's (normalized) newsvendor cost of producing $Q$ is
--   $$C(p,Q)=p\,\mathbb E\big[\xi(D_0-Q)^++(1-\xi)(Q-D_0)^+\big]+(1-p)\,\mathbb E\big[\xi(D_1-Q)^++(1-\xi)(Q-D_1)^+\big],$$
--   which is the paper's cost (2) divided by $C_s+C_e>0$. A quantity $Q$ is *optimal* at $p$ if $Q\ge0$ and $C(p,Q)\le C(p,Q')$ for every $Q'\ge0$. A *best-response profile* is a function $Q^*:\mathbb R\to\mathbb R$ such that $Q^*(p)$ is optimal at every $p\in[0,1]$; this is the set $\mathcal B(\Gamma)$ of p. 8.
--
--   **The retailer.** Her expected shortage at belief $p$ and quantity $Q$ is $R(p,Q)=p\,\mathbb E[(D_0-Q)^+]+(1-p)\,\mathbb E[(D_1-Q)^+]$. Her cost function (B.1) is
--   $$K_{DS}(p)=R\big(p,\bar Q_p\big),\qquad \bar Q_p=\sup\{Q:\ Q\text{ optimal at }p\},$$
--   the largest optimal quantity, which is the best response the retailer prefers since $R$ is nonincreasing in $Q$.
--
--   **Policies.** A policy with finite message space $\mathcal M$ is a family $\pi(m\mid\omega)\ge0$ with $\sum_m\pi(m\mid\omega)=1$ for each $\omega$. Message $m$ has probability $\mathbb P(m)=p_0\pi(m\mid0)+(1-p_0)\pi(m\mid1)$ and induces the posterior (1), $p_m=p_0\pi(m\mid0)/\mathbb P(m)$. The retailer's expected cost (3) under $\pi$ and a best-response profile $Q^*$ is
--   $$\sum_{m\in\mathcal M}\mathbb P(m)\,R\big(p_m,Q^*(p_m)\big).$$
--   A policy $\pi$ is *optimal* at $p_0$ if, for some best-response profile $Q^*$, this cost is at most the cost of every finite-message policy $\pi'$ under every best-response profile $Q'^*$ — the joint minimization over $\Gamma$ and $Q^*\in\mathcal B(\Gamma)$ of (3).
--
--   **Named policies.** Full disclosure sends $m_i$ exactly in state $\omega=i$; no disclosure sends a single message. With $\tilde p=\max\big(1-\xi,\ 2(b_0-a_0)/(b_1-a_1)\big)$, the policy $\Gamma^*_{DS}$ of (8) has messages $m_0,m_1$ and
--   $$\pi^*_{DS}(m_0\mid\omega=0)=1,\qquad \pi^*_{DS}(m_0\mid\omega=1)=\frac{1-\tilde p}{\tilde p}\cdot\frac{p_0}{1-p_0},$$
--   the remaining entries making each row sum to $1$.
--
--   These objects are the model on which Proposition 6, the value claim after (B.2), (C.9), (C.13), Lemma 3 and Theorem 3 are stated.
--
--   **Formalization Note** States are `Fin 2`; the cost (2) is divided by $C_s+C_e$, so $\xi$ is the parameter; message spaces are finite types (the paper does not bound $\mathcal M$); no disclosure is the one-message policy (every uninformative policy costs the same); a message of probability $0$ gets posterior $0$ and weight $0$. $K_{DS}$ uses the largest optimal quantity: at $p=1-\xi$ every $Q\in[b_1,a_0]$ is optimal, and the retailer-preferred choice $a_0$ is the one the paper's (3) and footnote 9 prescribe, whereas Proposition 6 prints $b_1$. The lower convex envelope $\kappa_{DS}$ is the published `BiconvexProg.BranchBound.convexEnvelope` on $[0,1]$.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), pp. 5–8, (1)–(3), footnote 9; p. 16, Theorem 3, (8); App. B, p. 24, (B.1)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Nested_Setting

namespace SCInfoDesign.Disjoint

/-- The primitive data of the model (Candogan–Gurkan, §2, pp. 5–8): the demand supports
`D₀ ~ U[a₀, b₀]` (state `ω = 0`), `D₁ ~ U[a₁, b₁]` (state `ω = 1`) and the supplier's critical
ratio `ξ = C_s / (C_s + C_e)`. No hypotheses are bundled; every theorem states the ones it uses. -/
structure Params where
  a₀ : ℝ
  b₀ : ℝ
  a₁ : ℝ
  b₁ : ℝ
  ξ : ℝ

namespace Params

variable (P : Params)

/-- The supplier's newsvendor cost (2) at belief `p = P(ω = 0)` and quantity `Q`, normalized by
`C_s + C_e`: `p E[ξ(D₀ - Q)⁺ + (1 - ξ)(Q - D₀)⁺] + (1 - p) E[ξ(D₁ - Q)⁺ + (1 - ξ)(Q - D₁)⁺]`. -/
noncomputable def supplierCost (p Q : ℝ) : ℝ :=
  p * SCInfoDesign.Nested.uniformMean P.a₀ P.b₀ (fun d => P.ξ * max (d - Q) 0 + (1 - P.ξ) * max (Q - d) 0) +
    (1 - p) * SCInfoDesign.Nested.uniformMean P.a₁ P.b₁ (fun d => P.ξ * max (d - Q) 0 + (1 - P.ξ) * max (Q - d) 0)

/-- `Q` is an optimal solution of (2) at belief `p`: `Q ≥ 0` and no `Q' ≥ 0` is cheaper. -/
def IsOptimalQuantity (p Q : ℝ) : Prop :=
  0 ≤ Q ∧ ∀ Q' : ℝ, 0 ≤ Q' → P.supplierCost p Q ≤ P.supplierCost p Q'

/-- The retailer's expected shortage at belief `p` and quantity `Q`:
`p E[(D₀ - Q)⁺] + (1 - p) E[(D₁ - Q)⁺]`. -/
noncomputable def retailerCost (p Q : ℝ) : ℝ :=
  p * SCInfoDesign.Nested.uniformMean P.a₀ P.b₀ (fun d => max (d - Q) 0) +
    (1 - p) * SCInfoDesign.Nested.uniformMean P.a₁ P.b₁ (fun d => max (d - Q) 0)

/-- A best-response profile `Q* ∈ 𝓑(Γ)` (p. 8): `Q*(p)` is optimal for (2) at every belief
`p ∈ [0, 1]`. -/
def IsBestResponseProfile (Qs : ℝ → ℝ) : Prop :=
  ∀ p ∈ Set.Icc (0 : ℝ) 1, P.IsOptimalQuantity p (Qs p)

/-- The largest optimal quantity at belief `p`, the supplier's best response the retailer prefers
(her shortage cost is nonincreasing in `Q`). -/
noncomputable def prefQ (p : ℝ) : ℝ :=
  sSup {Q : ℝ | P.IsOptimalQuantity p Q}

/-- The retailer's cost `K_DS(p)` of (B.1), at the retailer-preferred best response `prefQ p`. -/
noncomputable def K (p : ℝ) : ℝ :=
  P.retailerCost p (P.prefQ p)

/-- The threshold `p̃ = max(1 - ξ, 2(b₀ - a₀)/(b₁ - a₁))` of Theorem 3. -/
noncomputable def ptilde : ℝ :=
  max (1 - P.ξ) (2 * (P.b₀ - P.a₀) / (P.b₁ - P.a₁))

/-- The policy `Γ*_DS` of (8) at prior `p₀`, with messages `m₀ = 0`, `m₁ = 1`:
`π(m₀ | ω = 0) = 1`, `π(m₀ | ω = 1) = ((1 - p̃)/p̃) · p₀/(1 - p₀)`, and the complementary
entries make each row sum to `1`. -/
noncomputable def gammaStarDS (p₀ : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun ω m =>
    if ω = 0 then (if m = 0 then 1 else 0)
    else
      (if m = 0 then (1 - P.ptilde) / P.ptilde * (p₀ / (1 - p₀))
       else 1 - (1 - P.ptilde) / P.ptilde * (p₀ / (1 - p₀)))

end Params

/-- The probability of message `m` under prior `p₀ = P(ω = 0)`. -/
def msgProb {M : Type} (p₀ : ℝ) (π : Fin 2 → M → ℝ) (m : M) : ℝ :=
  p₀ * π 0 m + (1 - p₀) * π 1 m

/-- The supplier's posterior `P(ω = 0 | m)` by Bayes' rule (1). A message of probability `0` gets
the value `0`; it carries weight `0` in (3). -/
noncomputable def posterior {M : Type} (p₀ : ℝ) (π : Fin 2 → M → ℝ) (m : M) : ℝ :=
  p₀ * π 0 m / msgProb p₀ π m

/-- The retailer's expected shortage (3) under policy `π` at prior `p₀` when the supplier plays
the best-response profile `Qs`. -/
noncomputable def expectedCost (P : Params) {M : Type} [Fintype M] (p₀ : ℝ)
    (π : Fin 2 → M → ℝ) (Qs : ℝ → ℝ) : ℝ :=
  ∑ m, msgProb p₀ π m * P.retailerCost (posterior p₀ π m) (Qs (posterior p₀ π m))

/-- `π` is an optimal policy for the retailer's design problem (3) at prior `p₀`: it is a policy,
and together with some best-response profile it attains a cost no larger than that of any
finite-message policy with any best-response profile. -/
def IsOptimalPolicy (P : Params) {M : Type} [Fintype M] (p₀ : ℝ) (π : Fin 2 → M → ℝ) : Prop :=
  SCInfoDesign.Nested.IsPolicy π ∧ ∃ Qs : ℝ → ℝ, P.IsBestResponseProfile Qs ∧
    ∀ (M' : Type) [Fintype M'] (π' : Fin 2 → M' → ℝ) (Qs' : ℝ → ℝ),
      SCInfoDesign.Nested.IsPolicy π' → P.IsBestResponseProfile Qs' → expectedCost P p₀ π Qs ≤ expectedCost P p₀ π' Qs'

end SCInfoDesign.Disjoint


