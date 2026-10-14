-- Prove2me | Definitions.Def_SCInfoDesign_ValueInfo_Setting
-- name    : SCInfoDesign_ValueInfo_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:55.129244+00:00
-- url     : https://prove2.me/theorems/63f92c82-45d4-404a-b705-ab1424c01eb7
-- title:
--   §2, pp. 5–8, 13, 30 — uniform demand, the supplier's newsvendor (2), policies and Bayes' rule (1), the design problem (3), K (B.1), VI_ND and VI_FD
-- statement:
--   This file fixes the model of Candogan and Gurkan in which the value of information is studied, with the critical ratio $\xi$ as an explicit argument of every object (it varies in Theorem 2).
--
--   1. **Demand** (§2.1, p. 6). The state $\omega\in\{0,1\}$ has $\mathbb P(\omega=0)=p_0$. In state $0$ demand is $D_0\sim U[a_0,b_0]$, in state $1$ it is $D_1\sim U[a_1,b_1]$. For a function $f$, $\mathbb E_{U[a,b]}[f]=\frac{1}{b-a}\int_a^b f(x)\,dx$.
--   2. **The supplier** (2), p. 7. At belief $p=\mathbb P(\omega=0)$ the supplier chooses a quantity $Q\ge 0$ minimizing
--   $$S_\xi(p,Q)=p\,\mathbb E\big[\xi(D_0-Q)^+ + (1-\xi)(Q-D_0)^+\big]+(1-p)\,\mathbb E\big[\xi(D_1-Q)^+ + (1-\xi)(Q-D_1)^+\big].$$
--   $Q$ is **optimal at $p$** if $Q\ge0$ and $S_\xi(p,Q)\le S_\xi(p,Q')$ for every $Q'\ge 0$.
--   3. **The retailer's shortage cost** at belief $p$ and quantity $Q$: $R(p,Q)=p\,\mathbb E[(D_0-Q)^+]+(1-p)\,\mathbb E[(D_1-Q)^+]$.
--   4. **Policies and Bayes' rule** (§2.2, p. 7). A policy with a finite message set $\mathcal M$ is a pair of probability vectors $\pi(\cdot\mid\omega)$ on $\mathcal M$, $\omega\in\{0,1\}$. Message $m$ has probability $\mathbb P(m)=p_0\pi(m\mid 0)+(1-p_0)\pi(m\mid1)$ and induces the posterior (1)
--   $$p_m=\frac{p_0\,\pi(m\mid 0)}{\mathbb P(m)} .$$
--   5. **Best responses and the design problem** (3), p. 8. A best-response profile is a map $Q^*$ with $Q^*(p)$ optimal at every $p\in[0,1]$. The retailer's expected cost of a policy $\pi$ against $Q^*$ is $\sum_m \mathbb P(m)\,R\big(p_m,Q^*(p_m)\big)$, and the **optimal expected cost** $V_\xi(p_0)$ is the infimum of this quantity over all finite message sets, all policies and all best-response profiles.
--   6. **The no-disclosure cost** (B.1), p. 24: $K(p)=R(p,Q^*_p)$, where $Q^*_p$ is the largest optimal quantity at $p$. The **full-disclosure cost** is $K_F(p_0)=(1-p_0)K(0)+p_0K(1)$ (p. 30).
--   7. **Values of information** (p. 13): $VI_{ND}(\xi,p_0)=K(p_0)-V_\xi(p_0)$ and $VI_{FD}(\xi,p_0)=K_F(p_0)-V_\xi(p_0)$.
--   8. **Thresholds** (pp. 8, 13, 25): $\underline\tau(p)=p(a_1-a_0)/(b_0-a_0)$, $\bar\tau(p)=1-p(b_0-b_1)/(b_0-a_0)$, $\hat p=\xi(b_0-a_0)/(a_1-a_0)$, $p_0^*=\sqrt{\xi(b_0-a_0)/(a_1-a_0)}$ and $\xi^*=1-\tfrac12(a_1-a_0)/(b_0-b_1+a_1-a_0)$.
--
--   These are the objects of Theorem 2 and of the results of Appendix B its proof uses.
--
--   **Formalization Note** The supplier's cost uses the normalized loss $\xi(D-Q)^+ + (1-\xi)(Q-D)^+$, which is the paper's $C_s(D-Q)^+ + C_e(Q-D)^+$ divided by $C_s+C_e$; it has the same minimizers, and every $\xi\in(0,1)$ is $C_s/(C_s+C_e)$ for some $C_s,C_e>0$. Message sets are finite (`Fin n`); the paper does not bound them, and two messages already attain the optimum. A zero-probability message gets the junk posterior $0$ and weight $0$. $Q^*_p$ in $K$ is the supremum of the optimal set, which is the unique optimum under nested supports (Proposition 1). The paper defines the value of information as the absolute value of the difference; both differences are nonnegative by optimality, so the formalization uses the differences themselves. The full-disclosure cost is written as the paper's own expression $K_F$ (p. 30) rather than as the expected cost of a full-disclosure policy; the two coincide. The supports $a_0,b_0,a_1,b_1$ are bundled in a structure `Params`; their standing hypotheses are binders of each theorem.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), pp. 5–8 (1)–(3), p. 13 (Theorem 2), p. 24 (B.1), p. 25 (B.2), p. 30 (K_F)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope

namespace SCInfoDesign.ValueInfo

/-- The demand supports: in state `ω = 0` demand is `U[a₀, b₀]`, in state `ω = 1` it is
`U[a₁, b₁]` (Candogan–Gurkan, §2.1, p. 6). The critical ratio `ξ` is *not* a field: it varies
in Theorem 2, so every object below takes it as an explicit argument. -/
structure Params where
  a₀ : ℝ
  b₀ : ℝ
  a₁ : ℝ
  b₁ : ℝ

/-- Expectation of `f` under the uniform law on `[a, b]` (meaningful for `a < b`). -/
noncomputable def uniformMean (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in a..b, f x) / (b - a)

/-- The supplier's normalized newsvendor loss at quantity `Q` and demand `d`:
`ξ (d − Q)⁺ + (1 − ξ) (Q − d)⁺`, i.e. the cost `C_s (d − Q)⁺ + C_e (Q − d)⁺` of (2) divided by
`C_s + C_e`, with `ξ = C_s / (C_s + C_e)`. -/
noncomputable def nvLoss (ξ Q d : ℝ) : ℝ :=
  ξ * max (d - Q) 0 + (1 - ξ) * max (Q - d) 0

/-- The supplier's expected cost (2) at belief `p = P(ω = 0)` and quantity `Q`. -/
noncomputable def supplierCost (P : Params) (ξ p Q : ℝ) : ℝ :=
  p * uniformMean P.a₀ P.b₀ (fun d => nvLoss ξ Q d) +
    (1 - p) * uniformMean P.a₁ P.b₁ (fun d => nvLoss ξ Q d)

/-- `Q` is an optimal solution of the supplier's problem (2), `min_{Q ≥ 0}`, at belief `p`. -/
def IsOptimalQuantity (P : Params) (ξ p Q : ℝ) : Prop :=
  0 ≤ Q ∧ ∀ Q' : ℝ, 0 ≤ Q' → supplierCost P ξ p Q ≤ supplierCost P ξ p Q'

/-- The retailer's expected shortage `p E[(D₀ − Q)⁺] + (1 − p) E[(D₁ − Q)⁺]` at belief `p`. -/
noncomputable def retailerCost (P : Params) (p Q : ℝ) : ℝ :=
  p * uniformMean P.a₀ P.b₀ (fun d => max (d - Q) 0) +
    (1 - p) * uniformMean P.a₁ P.b₁ (fun d => max (d - Q) 0)

/-- A disclosure policy with finite message space `M`: `π ω m = π(m | ω)`, a probability
distribution over `M` for each state `ω ∈ {0, 1}` (§2.2, p. 7). -/
def IsPolicy {M : Type} [Fintype M] (π : Fin 2 → M → ℝ) : Prop :=
  (∀ ω m, 0 ≤ π ω m) ∧ ∀ ω, ∑ m, π ω m = 1

/-- Probability of message `m` under prior `p₀ = P(ω = 0)`. -/
def msgProb {M : Type} (p₀ : ℝ) (π : Fin 2 → M → ℝ) (m : M) : ℝ :=
  p₀ * π 0 m + (1 - p₀) * π 1 m

/-- The supplier's posterior `P(ω = 0 | m)` by Bayes' rule (1). A message of probability `0`
gets the value `0` (Lean's `x / 0 = 0`); it carries weight `0` in `expectedCost`. -/
noncomputable def posterior {M : Type} (p₀ : ℝ) (π : Fin 2 → M → ℝ) (m : M) : ℝ :=
  p₀ * π 0 m / msgProb p₀ π m

/-- A best-response profile `Q* ∈ 𝓑(Γ)` (p. 8): `Q*(p)` is optimal for (2) at every belief
`p ∈ [0, 1]`. -/
def IsBestResponseProfile (P : Params) (ξ : ℝ) (Qs : ℝ → ℝ) : Prop :=
  ∀ p ∈ Set.Icc (0 : ℝ) 1, IsOptimalQuantity P ξ p (Qs p)

/-- The objective of the retailer's design problem (3): expected shortage when the supplier
best-responds with `Qs` to the posterior induced by each message. -/
noncomputable def expectedCost {M : Type} [Fintype M] (P : Params) (p₀ : ℝ)
    (π : Fin 2 → M → ℝ) (Qs : ℝ → ℝ) : ℝ :=
  ∑ m, msgProb p₀ π m * retailerCost P (posterior p₀ π m) (Qs (posterior p₀ π m))

/-- The optimal value of (3): the infimum of `expectedCost` over every finite message space
(`Fin n`, which covers every finite space up to relabelling), every policy and every
best-response profile. -/
noncomputable def optimalCost (P : Params) (ξ p₀ : ℝ) : ℝ :=
  sInf {c : ℝ | ∃ (n : ℕ) (π : Fin 2 → Fin n → ℝ) (Qs : ℝ → ℝ),
    IsPolicy π ∧ IsBestResponseProfile P ξ Qs ∧ c = expectedCost P p₀ π Qs}

/-- The largest optimal quantity of (2) at belief `p` (the one the retailer prefers, since her
shortage cost is nonincreasing in `Q`). -/
noncomputable def prefQ (P : Params) (ξ p : ℝ) : ℝ :=
  sSup {Q : ℝ | IsOptimalQuantity P ξ p Q}

/-- The retailer's cost `K(p)` of (B.1), p. 24, at the supplier's (preferred) optimal quantity. -/
noncomputable def K (P : Params) (ξ p : ℝ) : ℝ :=
  retailerCost P p (prefQ P ξ p)

/-- The retailer's expected cost under no disclosure, `K(p₀)` (p. 30). -/
noncomputable def costNoDisclosure (P : Params) (ξ p₀ : ℝ) : ℝ :=
  K P ξ p₀

/-- The retailer's expected cost under full disclosure, `K_F(p₀) = (1 − p₀) K(0) + p₀ K(1)`
(p. 30). -/
noncomputable def costFullDisclosure (P : Params) (ξ p₀ : ℝ) : ℝ :=
  (1 - p₀) * K P ξ 0 + p₀ * K P ξ 1

/-- Value of information against no disclosure, `VI_ND` (p. 13). -/
noncomputable def VI_ND (P : Params) (ξ p₀ : ℝ) : ℝ :=
  costNoDisclosure P ξ p₀ - optimalCost P ξ p₀

/-- Value of information against full disclosure, `VI_FD` (p. 13). -/
noncomputable def VI_FD (P : Params) (ξ p₀ : ℝ) : ℝ :=
  costFullDisclosure P ξ p₀ - optimalCost P ξ p₀

/-- `τ̲(p) = p (a₁ − a₀) / (b₀ − a₀)` (Proposition 1, p. 8). -/
noncomputable def τlow (P : Params) (p : ℝ) : ℝ :=
  p * (P.a₁ - P.a₀) / (P.b₀ - P.a₀)

/-- `τ̄(p) = 1 − p (b₀ − b₁) / (b₀ − a₀)` (Proposition 1, p. 8). -/
noncomputable def τup (P : Params) (p : ℝ) : ℝ :=
  1 - p * (P.b₀ - P.b₁) / (P.b₀ - P.a₀)

/-- `p̂ = ξ (b₀ − a₀) / (a₁ − a₀)` (Lemma 1, p. 25). -/
noncomputable def pHat (P : Params) (ξ : ℝ) : ℝ :=
  ξ * (P.b₀ - P.a₀) / (P.a₁ - P.a₀)

/-- The peak `p₀* = √(ξ (b₀ − a₀) / (a₁ − a₀))` of `VI_ND` in `p₀` (Theorem 2, p. 13). -/
noncomputable def p₀star (P : Params) (ξ : ℝ) : ℝ :=
  Real.sqrt (ξ * (P.b₀ - P.a₀) / (P.a₁ - P.a₀))

/-- The peak `ξ* = 1 − 1/2 × (a₁ − a₀) / (b₀ − b₁ + a₁ − a₀)` of `VI_FD` in `ξ`
(Theorem 2, p. 13). -/
noncomputable def ξstar (P : Params) : ℝ :=
  1 - (1 / 2) * (P.a₁ - P.a₀) / (P.b₀ - P.b₁ + P.a₁ - P.a₀)

end SCInfoDesign.ValueInfo


