-- Prove2me | Definitions.Def_MitigateSupplyRisk_LateCommit_Model
-- name    : MitigateSupplyRisk_LateCommit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:47.897489+00:00
-- url     : https://prove2.me/theorems/317ed902-21fd-469e-9614-a54e97182b89
-- title:
--   §3, §4.2, Eqs. (1), (3), (7), (9) — single sourcing from unreliable suppliers with improvement: Π₂*(a), early-commitment Π₁ᴱ, late-commitment Π₁ᴸ and their optimal values
-- statement:
--   This file fixes the model of Wang, Gilland and Tomlin (§3) as it is used for single sourcing with reliability improvement (§4.2).
--
--   **Market.** A firm sells one product over one season. It earns a unit revenue $r\ge 0$, salvages leftovers at $v$, and pays a penalty $p\ge 0$ per unit of unmet demand, with $v<r+p$. Demand $X$ has a law $\mu$ on $[0,\infty)$ with finite mean.
--
--   **Supplier.** A supplier has design capacity $K>0$ and committed-cost fraction $\eta\in[0,1]$. At reliability index $a$ its capacity loss $\xi$ has a continuous law $\nu_a$ on $[0,\infty)$ with distribution function $G(t,a)=\nu_a(-\infty,t]$. A larger index means a stochastically smaller loss: $a\le a'$ implies $G(t,a)\le G(t,a')$ for all $t$. An order $q\ge 0$ placed with unit cost $c\ge 0$ delivers $y=\min\{q,(K-\xi)^+\}$, and the realized profit is Eq. (1) with this one supplier:
--   $$\pi(q)=-(\eta q+(1-\eta)y)c+r\min\{x,y\}+v(y-x)^+-p(x-y)^+ .$$
--   Loss and demand are independent, and the second-stage expected profit is $\Pi_2(q;a)=\mathsf E_{\xi(a),X}[\pi(q)]$, the single-supplier form (7) of (3). The optimal second-stage profit is
--   $$\Pi_2^*(a)=\sup_{q\ge 0}\Pi_2(q;a).$$
--
--   **Improvement.** Supplier $i$ starts at index $a_i^0$. An effort that targets index $a\ge a_i^0$ costs $m_i z_i(a)$ with $m_i\ge 0$, where $z_i$ is convex and increasing on $[a_i^0,\infty)$ and $z_i(a_i^0)=0$. It succeeds with probability $\theta_i\in[0,1]$; on failure the index stays at $a_i^0$.
--
--   **Two suppliers.** For supplier $i=1,2$ with unit cost $c_i\ge 0$, write $P_i(a)$ for its single-sourcing value $\Pi_2^*(a)$. Under **early commitment** the firm selects one supplier before the improvement outcome is known. Supplier $i$'s first-stage profit is (7),
--   $$\Pi_{1i}^E(a)=-m_iz_i(a)+\theta_iP_i(a)+(1-\theta_i)P_i(a_i^0),\qquad a\ge a_i^0,$$
--   and $\Pi_1^{*E}=\max_{i}\sup_{a\ge a_i^0}\Pi_{1i}^E(a)$. Under **late commitment** the firm improves both suppliers and, after observing the outcomes, buys from the better one. Its first-stage profit is (9),
--   $$\begin{aligned}\Pi_1^L(a_1,a_2)={}&-m_1z_1(a_1)-m_2z_2(a_2)+\theta_1\theta_2\max\{P_1(a_1),P_2(a_2)\}+\theta_1(1-\theta_2)\max\{P_1(a_1),P_2(a_2^0)\}\\&+(1-\theta_1)\theta_2\max\{P_1(a_1^0),P_2(a_2)\}+(1-\theta_1)(1-\theta_2)\max\{P_1(a_1^0),P_2(a_2^0)\},\end{aligned}$$
--   and $\Pi_1^{*L}=\sup_{a_1\ge a_1^0,\,a_2\ge a_2^0}\Pi_1^L(a_1,a_2)$. Suppliers are **identical except for their unit costs** when they share $\eta$, $K$, the loss family, $a^0$, $\theta$, $m$ and $z$.
--
--   Every result of the mission (Lemma 2(b), Theorems 4(a) and 5, Lemma 4, Corollary 3(a)) is stated about these objects.
--
--   **Formalization Note** The sign conditions $r,p,c_i\ge 0$, $v<r+p$, the nonnegativity and finite mean of demand, and the convexity and monotonicity of $z$ are the paper's standing reading of §3 made explicit. They make every supremum finite: $\Pi_2(q;a)\le(r+|v|)K$ because $y\le K$, and $z\ge 0$, so $\Pi_2^*$, $\Pi_1^{*E}$ and $\Pi_1^{*L}$ are genuine suprema of nonempty, bounded-above sets, never a junk `sSup`. For fixed $q$ the integrand is bounded by a constant times $1+|x|$, so the Bochner integral defining $\Pi_2$ is never the junk value $0$. In (9) the paper writes $\Pi_2^*$ for both suppliers; here they are $P_1$ and $P_2$. Taking $z$ as the primitive on $[a^0,\infty)$ assumes that every index $a\ge a^0$ is reachable, as for the paper's example $a(z)=a^0+\log(1+z)$. The loss law is given for every real index, and the stochastic order is required for all of them.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), pp. 492–493 (§3.1–3.3, Eqs. (1)–(5)), p. 496 (§4.2.1, Eq. (7)), p. 498 (§4.2.2, Eq. (9)); PDF pp. 4–5, 8, 10

import Mathlib
open MeasureTheory
noncomputable section

namespace MitigateSupplyRisk.LateCommit

/-- Market data of §3.1 (p. 492): unit revenue `r`, salvage value `v`, penalty cost `p`, and the
law `μ` of the demand `X`.  Standing conventions: `r ≥ 0` and `p ≥ 0` (revenue and penalty),
`v < r + p` (the divisor `r + p − v` of (2)–(3) is positive), demand is nonnegative almost surely
and has a finite mean (`E[X]` appears in (3)).  No density is assumed; deterministic demand is the
Dirac case. -/
structure Market where
  r : ℝ
  v : ℝ
  p : ℝ
  μ : Measure ℝ
  μ_prob : IsProbabilityMeasure μ
  r_nonneg : 0 ≤ r
  p_nonneg : 0 ≤ p
  v_lt : v < r + p
  demand_nonneg : μ (Set.Iio 0) = 0
  demand_integrable : Integrable id μ

/-- An unreliable supplier of §3.1–3.2 (pp. 492–493), *without* its unit cost (the cost is kept
separate so that suppliers "identical except for their unit costs" share one `Supplier`).
`η` is the committed-cost fraction, `K` the design capacity, and `ν a` the law of the capacity loss
`ξ` at reliability index `a`, so `G(t, a) = ν a (−∞, t]`.  Each `ν a` is a probability measure on
`[0, ∞)` without atoms (the loss distribution is continuous), and a larger index means a
stochastically smaller loss: `a ≤ a' → G(t, a) ≤ G(t, a')` for all `t`. -/
structure Supplier where
  η : ℝ
  K : ℝ
  ν : ℝ → Measure ℝ
  ν_prob : ∀ a, IsProbabilityMeasure (ν a)
  η_nonneg : 0 ≤ η
  η_le_one : η ≤ 1
  K_pos : 0 < K
  loss_nonneg : ∀ a, ν a (Set.Iio 0) = 0
  loss_noAtoms : ∀ a, NullSingletonClass (ν a)
  stoch_order : ∀ a a', a ≤ a' → ∀ t, ν a (Set.Iic t) ≤ ν a' (Set.Iic t)

/-- Improvement data of §3.2 (p. 493) for one supplier: initial index `a0 = a⁰`, success
probability `θ`, unit improvement cost `m`, and the effort `z(a)` needed to reach index `a`, which
the paper (p. 493) notes is convex and increasing in `a`, with `z(a⁰) = 0`.  Taking `z` as the
primitive on `[a⁰, ∞)` presumes the reachable indices are all of `[a⁰, ∞)`. -/
structure Improvement where
  a0 : ℝ
  θ : ℝ
  m : ℝ
  z : ℝ → ℝ
  θ_nonneg : 0 ≤ θ
  θ_le_one : θ ≤ 1
  m_nonneg : 0 ≤ m
  z_convex : ConvexOn ℝ (Set.Ici a0) z
  z_mono : MonotoneOn z (Set.Ici a0)
  z_a0 : z a0 = 0

/-- Delivered quantity `y = min{q, (K − ξ)⁺}` (p. 493). -/
def delivered (K q ξ : ℝ) : ℝ := min q (max (K - ξ) 0)

/-- Realized single-sourcing profit, Eq. (1) (p. 493) with one supplier of unit cost `c`
(the other supplier's order and delivery are `0`):
`π = −(η q + (1 − η) y) c + r min{x, y} + v (y − x)⁺ − p (x − y)⁺`. -/
def realizedProfit (M : Market) (S : Supplier) (c q ξ x : ℝ) : ℝ :=
  -(S.η * q + (1 - S.η) * delivered S.K q ξ) * c + M.r * min x (delivered S.K q ξ)
    + M.v * max (delivered S.K q ξ - x) 0 - M.p * max (x - delivered S.K q ξ) 0

/-- Second-stage single-sourcing expected profit `Π₂(q; a) = E_{ξ(a), X}[π(q)]`, the
single-supplier form (7) of (3) (pp. 493, 496): loss and demand are independent, so the
expectation is over `ν a ⊗ μ`.  For fixed `q` the integrand is bounded by a constant times
`1 + |x|`, hence integrable, so this Bochner integral is never the junk value. -/
def secondStageProfit (M : Market) (S : Supplier) (c q a : ℝ) : ℝ :=
  ∫ w, realizedProfit M S c q w.1 w.2 ∂((S.ν a).prod M.μ)

/-- Optimal second-stage value `Π₂*(a) = sup_{q ≥ 0} Π₂(q; a)` (p. 496).  The set is nonempty
(`q = 0`) and bounded above by `(r + |v|) K` (as `y ≤ K`, `r, p, c ≥ 0`), so `sSup` is the true
supremum. -/
def optValue (M : Market) (S : Supplier) (c a : ℝ) : ℝ :=
  sSup ((fun q => secondStageProfit M S c q a) '' Set.Ici 0)

/-- Early-commitment first-stage profit, Eq. (7) (p. 496):
`Π₁(a) = −m z(a) + θ Π₂*(a) + (1 − θ) Π₂*(a⁰)`. -/
def earlyProfit (M : Market) (S : Supplier) (c : ℝ) (I : Improvement) (a : ℝ) : ℝ :=
  -(I.m * I.z a) + I.θ * optValue M S c a + (1 - I.θ) * optValue M S c I.a0

/-- The two-supplier setting of §4.2 (pp. 496–499): a market, and two suppliers `i = 1, 2`, each
with its own `Supplier` data, unit cost `cᵢ ≥ 0` and improvement data. -/
structure Setting where
  M : Market
  S₁ : Supplier
  S₂ : Supplier
  c₁ : ℝ
  c₂ : ℝ
  I₁ : Improvement
  I₂ : Improvement
  c₁_nonneg : 0 ≤ c₁
  c₂_nonneg : 0 ≤ c₂

namespace Setting

variable (X : Setting)

/-- `P₁(a) = Π₂*(a)` when single sourcing from supplier 1. -/
def P₁ (a : ℝ) : ℝ := optValue X.M X.S₁ X.c₁ a

/-- `P₂(a) = Π₂*(a)` when single sourcing from supplier 2. -/
def P₂ (a : ℝ) : ℝ := optValue X.M X.S₂ X.c₂ a

/-- Supplier 1's early-commitment profit `Π₁₁^E(a)` of (7). -/
def early₁ (a : ℝ) : ℝ := earlyProfit X.M X.S₁ X.c₁ X.I₁ a

/-- Supplier 2's early-commitment profit `Π₁₂^E(a)` of (7). -/
def early₂ (a : ℝ) : ℝ := earlyProfit X.M X.S₂ X.c₂ X.I₂ a

/-- Optimal early-commitment profit if supplier 1 is selected: `sup_{a ≥ a₁⁰} Π₁₁^E(a)`. -/
def earlyValue₁ : ℝ := sSup (X.early₁ '' Set.Ici X.I₁.a0)

/-- Optimal early-commitment profit if supplier 2 is selected: `sup_{a ≥ a₂⁰} Π₁₂^E(a)`. -/
def earlyValue₂ : ℝ := sSup (X.early₂ '' Set.Ici X.I₂.a0)

/-- `Π₁^{*E}`: early commitment selects the better of the two suppliers. -/
def earlyValue : ℝ := max X.earlyValue₁ X.earlyValue₂

/-- Late-commitment first-stage profit `Π₁^L(a₁, a₂)`, Eq. (9) (p. 498). -/
def lateProfit (a₁ a₂ : ℝ) : ℝ :=
  -(X.I₁.m * X.I₁.z a₁) - X.I₂.m * X.I₂.z a₂
    + X.I₁.θ * X.I₂.θ * max (X.P₁ a₁) (X.P₂ a₂)
    + X.I₁.θ * (1 - X.I₂.θ) * max (X.P₁ a₁) (X.P₂ X.I₂.a0)
    + (1 - X.I₁.θ) * X.I₂.θ * max (X.P₁ X.I₁.a0) (X.P₂ a₂)
    + (1 - X.I₁.θ) * (1 - X.I₂.θ) * max (X.P₁ X.I₁.a0) (X.P₂ X.I₂.a0)

/-- Feasible index pairs of late commitment: `a₁ ≥ a₁⁰`, `a₂ ≥ a₂⁰`. -/
def lateFeasible : Set (ℝ × ℝ) := {a | X.I₁.a0 ≤ a.1 ∧ X.I₂.a0 ≤ a.2}

/-- `Π₁^{*L} = sup_{a₁ ≥ a₁⁰, a₂ ≥ a₂⁰} Π₁^L(a₁, a₂)`. -/
def lateValue : ℝ := sSup ((fun a : ℝ × ℝ => X.lateProfit a.1 a.2) '' X.lateFeasible)

/-- Suppliers 1 and 2 are identical except for their unit costs (Theorem 5, p. 498): the same
`Supplier` data (`η`, `K`, loss family) and the same improvement data (`a⁰`, `θ`, `m`, `z`). -/
def IdenticalExceptCost : Prop := X.S₁ = X.S₂ ∧ X.I₁ = X.I₂

end Setting

end MitigateSupplyRisk.LateCommit


