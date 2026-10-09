-- Prove2me | Definitions.Def_SLPricing_PreAnn_Model
-- name    : SLPricing_PreAnn_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:13:46.977119+00:00
-- url     : https://prove2.me/theorems/5eb19127-14dc-463b-aaf2-186fec3fd18d
-- title:
--   §§3–6, Lemma 1, Definition 1, (4), (8), pp. 7–22 — the two-period pricing model with social learning: pre-posterior law, purchasing equilibria, expected profits and optimal values
-- statement:
--   This file sets up the two-period model of Papanastasiou and Savva in which a monopolist sells a new product of unknown quality to strategic consumers who learn from the reviews of earlier buyers.
--
--   **Parameters.** The prior belief over the product's mean quality $\hat q$ is $\tilde q_p\sim N(0,\sigma_p^2)$; individual quality perceptions are $N(\hat q,\sigma_q^2)$, and $\gamma=\sigma_p^2/\sigma_q^2$ is the *social-learning (SL) influence parameter*. Consumers discount second-period utility by $\delta_c$ and the firm's unit cost is $c$. The standing assumptions of §3 are
--   $$\sigma_p>0,\qquad \gamma\ge 0,\qquad \delta_c\in[0,1],\qquad c\in[0,1).$$
--   The benchmark *absence of SL* is the same model with $\gamma=0$; the model with discount factor $d$ in place of $\delta_c$ is also named.
--
--   **Pre-posterior law.** If a mass $n_1$ of consumers buys in period 1, the posterior mean $q_u$ of quality, seen from period 1, has the law
--   $$N\!\left(0,\ \sigma_p^2\,\frac{n_1\gamma}{n_1\gamma+1}\right),$$
--   which is the point mass at $0$ when $n_1\gamma=0$. Definition 1's density $f(\cdot\,;z)$ is the density of this law with $n_1=1-z$.
--
--   **Consumers.** Preference types $x$ are uniform on $[0,1]$ (Lebesgue measure). A set $B\subseteq[0,1]$ of first-period buyers has mass $|B|$, which is the mass of reviews. In period 2 the remaining types $x\in[0,1]\setminus B$ buy iff $x+q_u-p_2\ge 0$.
--
--   **Pre-announced pricing.** Under a plan $\{p_1,p_2\}$, type $x$ weakly prefers to buy early iff $x-p_1\ge 0$ and
--   $$x-p_1\ \ge\ \delta_c\,\mathbb E\big[(x+q_u-p_2)^+\big],$$
--   with $q_u$ distributed by the pre-posterior law for $n_1=|B|$; it weakly prefers to delay iff the reverse inequality holds. A *purchasing equilibrium* is a measurable $B\subseteq[0,1]$ such that every type in $B$ weakly prefers to buy and every type in $[0,1]\setminus B$ weakly prefers to delay. The expected profit (4) is
--   $$\pi_p(p_1,p_2;B)=(p_1-c)\,|B|+(p_2-c)\,\mathbb E\Big[\big|\{x\in[0,1]\setminus B:\ p_2\le x+q_u\}\big|\Big],$$
--   and the optimal pre-announced profit $\pi_p^*$ is the supremum of $\pi_p(p_1,p_2;B)$ over all real prices and all their purchasing equilibria, taken in the extended reals. A plan is *optimal* if one of its equilibria attains $\pi_p^*$.
--
--   **Responsive pricing.** The firm announces only $p_1$ and sets $p_2=s(q_u)$ after the reviews. An equilibrium is a measurable buyer set $B$ together with a measurable rule $s$ that maximizes the second-period profit $(p_2-c)\,|\{x\in[0,1]\setminus B: p_2\le x+q_u\}|$ at every realization $q_u$, such that $B$ is a purchasing equilibrium against $s$. The profit (8), the optimal value $\pi_r^*$ and optimal first-period prices are defined in the same way.
--
--   These objects are shared by every statement of the mission series.
--
--   **Formalization Note** The firm's discount factor is $\delta_f=1$ (§3). Best responses are weak, so the indifferent marginal type may be in or out of $B$, and equilibrium sets are determined only up to null sets. Optimal values are suprema in `EReal`, so an empty or unbounded family has no junk real value. The section on responsive pricing is not used in this mission; it is included verbatim because the model file is shared by the three missions of this series.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), §3, §4, Lemma 1, Definition 1, (4), §6.2.1, (8), pp. 7–22

import Mathlib

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.PreAnn

/-- The primitive parameters of §3 (pp. 7–10): `σp` the standard deviation of the prior belief
`q̃p ∼ N(0, σp²)` over mean quality, `γ = σp²/σq²` the SL influence parameter (1), `δc` the
consumers' discount factor, `c` the unit cost. -/
structure Params where
  σp : ℝ
  γ : ℝ
  δc : ℝ
  c : ℝ

/-- Standing assumptions of §3: `σp > 0`, `γ ≥ 0`, `δc ∈ [0, 1]`, `c ∈ [0, 1)`.
`γ = 0` encodes the paper's benchmark "absence of SL" (the limit `γ → 0` of §5.1, §6.1). -/
structure Params.Standing (P : Params) : Prop where
  σp_pos : 0 < P.σp
  γ_nonneg : 0 ≤ P.γ
  δc_nonneg : 0 ≤ P.δc
  δc_le_one : P.δc ≤ 1
  c_nonneg : 0 ≤ P.c
  c_lt_one : P.c < 1

/-- The benchmark without social learning (§5.1, §6.1): `γ = 0`. -/
def Params.noSL (P : Params) : Params := { P with γ := 0 }

/-- The same model with consumer discount factor `d`. -/
def Params.withδc (P : Params) (d : ℝ) : Params := { P with δc := d }

/-- Lemma 1 / Definition 1 (p. 11): the variance `σp² · n₁γ/(n₁γ + 1)` of the pre-posterior
distribution of `q_u` when a mass `n₁` of first-period reviews is available. -/
noncomputable def preVar (P : Params) (n₁ : ℝ) : ℝ≥0 :=
  (P.σp ^ 2 * (n₁ * P.γ / (n₁ * P.γ + 1))).toNNReal

/-- The pre-posterior law of `q_u`: `N(0, σp² n₁γ/(n₁γ + 1))` (Lemma 1). Definition 1's density
`f(·; z)` is the density of `prePost P (1 - z)`. If `n₁γ = 0` it is the point mass at `0`. -/
noncomputable def prePost (P : Params) (n₁ : ℝ) : Measure ℝ :=
  gaussianReal 0 (preVar P n₁)

/-- The mass (Lebesgue measure) of a set of preference types. -/
noncomputable def mass (B : Set ℝ) : ℝ := (volume B).toReal

/-- The mass of second-period buyers: types `x ∈ [0, 1] \ B` (still in the market) with
`x + q_u − p₂ ≥ 0`. -/
noncomputable def lateMass (B : Set ℝ) (p₂ q : ℝ) : ℝ :=
  (volume {x ∈ Icc (0 : ℝ) 1 \ B | p₂ ≤ x + q}).toReal

/-! ### Pre-announced pricing (§5) -/

/-- §3, p. 10: under the announced plan `{p₁, p₂}`, buying in period 1 is a best response for a
customer of type `x` iff (i) `E[u₁] = x − p₁ ≥ 0` and (ii) `E[u₁] ≥ δc E[(x + q_u − p₂)⁺]`, the
expected utility of delaying, where `q_u` has the pre-posterior law for a mass `n₁` of reviews. -/
def BuysEarlyPre (P : Params) (p₁ p₂ n₁ x : ℝ) : Prop :=
  0 ≤ x - p₁ ∧ P.δc * ∫ q, max (x + q - p₂) 0 ∂(prePost P n₁) ≤ x - p₁

/-- Delaying is a best response for type `x`: `x − p₁ ≤ δc E[(x + q_u − p₂)⁺]` (delaying keeps the
option, not the obligation, to buy in period 2, so its value is `≥ 0`). -/
def DelaysPre (P : Params) (p₁ p₂ n₁ x : ℝ) : Prop :=
  x - p₁ ≤ P.δc * ∫ q, max (x + q - p₂) 0 ∂(prePost P n₁)

/-- A pure-strategy (Nash) equilibrium of the consumers' purchasing game under `{p₁, p₂}`:
`B ⊆ [0, 1]` is the set of types that buy in period 1; each type in `B` best-responds by buying and
each type of `[0, 1] \ B` by delaying, given the mass of reviews `mass B` that `B` generates. -/
def IsPreEq (P : Params) (p₁ p₂ : ℝ) (B : Set ℝ) : Prop :=
  MeasurableSet B ∧ B ⊆ Icc 0 1 ∧
    (∀ x ∈ B, BuysEarlyPre P p₁ p₂ (mass B) x) ∧
    ∀ x ∈ Icc (0 : ℝ) 1 \ B, DelaysPre P p₁ p₂ (mass B) x

/-- The firm's expected profit (4) under `{p₁, p₂}` when `B` buys early. -/
noncomputable def preProfit (P : Params) (p₁ p₂ : ℝ) (B : Set ℝ) : ℝ :=
  (p₁ - P.c) * mass B + (p₂ - P.c) * ∫ q, lateMass B p₂ q ∂(prePost P (mass B))

/-- `π*_p`: the firm's optimal expected profit under pre-announced pricing, the supremum over all
plans and their purchasing equilibria (in `EReal`, so no junk value). -/
noncomputable def preValue (P : Params) : EReal :=
  ⨆ o : {o : ℝ × ℝ × Set ℝ // IsPreEq P o.1 o.2.1 o.2.2},
    ((preProfit P o.1.1 o.1.2.1 o.1.2.2 : ℝ) : EReal)

/-- `{p₁, p₂}` is an optimal pre-announced price plan: it has an equilibrium attaining `π*_p`. -/
def IsOptimalPre (P : Params) (p₁ p₂ : ℝ) : Prop :=
  ∃ B, IsPreEq P p₁ p₂ B ∧ ((preProfit P p₁ p₂ B : ℝ) : EReal) = preValue P

/-! ### Responsive pricing (§6) -/

/-- The firm's second-period profit `(p₂ − c) · (mass of second-period buyers)` at realized `q_u`
(§6.2.1, p. 20). -/
noncomputable def secondProfit (P : Params) (B : Set ℝ) (q p₂ : ℝ) : ℝ :=
  (p₂ - P.c) * lateMass B p₂ q

/-- Under responsive pricing with first-period price `p₁` and second-period pricing rule
`s : q_u ↦ p₂`, buying in period 1 is a best response for type `x` iff `x − p₁ ≥ 0` and
`x − p₁ ≥ δc E[(x + q_u − s(q_u))⁺]`. -/
def BuysEarlyResp (P : Params) (p₁ : ℝ) (s : ℝ → ℝ) (n₁ x : ℝ) : Prop :=
  0 ≤ x - p₁ ∧ P.δc * ∫ q, max (x + q - s q) 0 ∂(prePost P n₁) ≤ x - p₁

/-- Delaying is a best response for type `x`: `x − p₁ ≤ δc E[(x + q_u − s(q_u))⁺]`. -/
def DelaysResp (P : Params) (p₁ : ℝ) (s : ℝ → ℝ) (n₁ x : ℝ) : Prop :=
  x - p₁ ≤ P.δc * ∫ q, max (x + q - s q) 0 ∂(prePost P n₁)

/-- A pure-strategy subgame-perfect continuation after the first-period price `p₁` (§6): the
(measurable) second-period rule `s` is optimal for the remaining population `[0, 1] \ B` at every
realization `q_u`, and `B` is a purchasing equilibrium given `s`. -/
def IsRespEq (P : Params) (p₁ : ℝ) (B : Set ℝ) (s : ℝ → ℝ) : Prop :=
  MeasurableSet B ∧ B ⊆ Icc 0 1 ∧ Measurable s ∧
    (∀ q p₂, secondProfit P B q p₂ ≤ secondProfit P B q (s q)) ∧
    (∀ x ∈ B, BuysEarlyResp P p₁ s (mass B) x) ∧
    ∀ x ∈ Icc (0 : ℝ) 1 \ B, DelaysResp P p₁ s (mass B) x

/-- The firm's expected profit (8) under responsive pricing. -/
noncomputable def respProfit (P : Params) (p₁ : ℝ) (B : Set ℝ) (s : ℝ → ℝ) : ℝ :=
  (p₁ - P.c) * mass B + ∫ q, secondProfit P B q (s q) ∂(prePost P (mass B))

/-- `π*_r`: the firm's optimal expected profit under responsive pricing. -/
noncomputable def respValue (P : Params) : EReal :=
  ⨆ o : {o : ℝ × Set ℝ × (ℝ → ℝ) // IsRespEq P o.1 o.2.1 o.2.2},
    ((respProfit P o.1.1 o.1.2.1 o.1.2.2 : ℝ) : EReal)

/-- `p₁` is an optimal first-period price under responsive pricing. -/
def IsOptimalResp (P : Params) (p₁ : ℝ) : Prop :=
  ∃ B s, IsRespEq P p₁ B s ∧ ((respProfit P p₁ B s : ℝ) : EReal) = respValue P

end SLPricing.PreAnn


