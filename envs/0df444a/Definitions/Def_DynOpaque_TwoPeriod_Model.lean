-- Prove2me | Definitions.Def_DynOpaque_TwoPeriod_Model
-- name    : DynOpaque_TwoPeriod_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:41.336566+00:00
-- url     : https://prove2.me/theorems/78311b9d-ab8c-462b-bacd-7ec1ee60538f
-- title:
--   §3, pp. 7–13 — two-period opaque selling with one-anecdote customers (K = 1, ξ0 = 0), purchase rule (1), profit (2), transparent selling, objectives (3)–(6)
-- statement:
--   A firm sells two versions of a product, $H$ and $L$, over two periods $t=1,2$, to a fresh unit mass of customers in each period. Every customer values $H$ at $v_H$ and $L$ at $v_L$, and the unit costs are $c_H$ and $c_L$. The **standing assumptions** are
--   $$
--   v_H>v_L,\qquad c_H>c_L,\qquad 0\le\alpha\le1,\qquad c_L\le v_L .
--   $$
--
--   **Opaque (probabilistic) selling.** In period $t$ the firm posts a price $p_t$ for an opaque product and delivers $H$ with probability $\xi_t\in[0,1]$, $L$ otherwise. A customer does not know $\xi_t$; she draws $K$ anecdotes (past realizations $H$ or $L$) and, with prior $\xi_0$, estimates the $H$-probability as $\tilde\xi=(\xi_0+\#\{H\text{ anecdotes}\})/(K+1)$. This mission fixes $K=1$ and $\xi_0=0$, so the estimate is $1/2$ after an $H$ anecdote and $0$ after an $L$ anecdote. She buys at price $p$ if and only if (rule (1))
--   $$
--   \tilde\xi\,v_H+(1-\tilde\xi)\,v_L\ \ge\ p .
--   $$
--   In period 1 an anecdote is $H$ with probability $\xi_1$; in period 2 it comes from period 1 with probability $\alpha$ and from period 2 otherwise, so it is $H$ with probability $\alpha\xi_1+(1-\alpha)\xi_2$. If an anecdote is $H$ with probability $h$, the purchasing fraction at price $p$ is
--   $$
--   \gamma(h,p)=h\,\mathbf 1\{\tfrac12 v_H+\tfrac12 v_L\ge p\}+(1-h)\,\mathbf 1\{v_L\ge p\},
--   $$
--   and the two-period profit (2) is
--   $$
--   \Pi(\xi_1,\xi_2\mid p_1,p_2)=\gamma(\xi_1,p_1)\,[p_1-\xi_1c_H-(1-\xi_1)c_L]+\gamma(\alpha\xi_1+(1-\alpha)\xi_2,p_2)\,[p_2-\xi_2c_H-(1-\xi_2)c_L].
--   $$
--   The price $v_{HL}\equiv\frac{v_H-v_L}{2}+v_L$ is the highest price any customer pays for the opaque product. An opaque policy $(p_1,p_2,\xi_1,\xi_2)$ is **feasible** when $p_1,p_2\le v_{HL}$ and $\xi_1,\xi_2\in[0,1]$.
--
--   **Transparent selling** (§3.3) sells one version $m\in\{H,L\}$ at prices $q_1,q_2$; in period $t$ every customer buys iff $q_t\le v_m$, so the profit is $\sum_{t=1,2}\mathbf 1\{q_t\le v_m\}(q_t-c_m)$. Every transparent policy is feasible. A policy is **optimal** when it is feasible and its profit is at least that of every feasible opaque or transparent policy.
--
--   The file also defines the four objectives (3)–(6) of §4 literally as printed: with $\bar\xi_2=\alpha\xi_1+(1-\alpha)\xi_2$,
--   $$
--   \begin{aligned}
--   (3)&\ \ \xi_1[v_{HL}-\xi_1c_H-(1-\xi_1)c_L]+\bar\xi_2[v_{HL}-\xi_2c_H-(1-\xi_2)c_L],\\
--   (4)&\ \ \xi_1[v_{HL}-\xi_1c_H-(1-\xi_1)c_L]+[v_L-\xi_2c_H-(1-\xi_2)c_L],\\
--   (5)&\ \ [v_L-\xi_1c_H-(1-\xi_1)c_L]+\bar\xi_2[v_{HL}-\xi_2c_H-(1-\xi_2)c_L],\\
--   (6)&\ \ [v_L-\xi_1c_H-(1-\xi_1)c_L]+[v_L-\xi_2c_H-(1-\xi_2)c_L],
--   \end{aligned}
--   $$
--   the box $[0,1]^2$ of offering pairs, the notion of an optimal offering decision (a maximizer over the box, not necessarily unique), and the threshold $\bar\alpha=(\sqrt{17}-3)/2$.
--
--   These objects are shared by every statement of the mission: Lemma 1 links the purchasing fractions to the closed forms, Lemmas 2–4 optimize (3)–(5), and Proposition 1 identifies the globally optimal policy.
--
--   **Formalization Note** All quantities are real numbers. The demand $\gamma$ is computed from the estimate and rule (1), not from closed forms; equality buys. Two choices are disclosed additions to the page. (a) $c_L\le v_L$ is added to the standing assumptions: the proof of Proposition 1 (p. 30) uses $v_L-c_L\ge0$, and without it $\xi_1^*$ of Proposition 1 (i) can be negative. (b) Opaque prices are restricted to $p_t\le v_{HL}$: Lemma 1 places every optimal price in $\{v_L,v_{HL}\}$ for $K=1$, and above $v_{HL}$ nobody buys, so there are no period-1 anecdotes, a case the paper's model leaves undefined. Transparent prices are unrestricted.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927, pp. 7–13, §3 (eqs. (1), (2), §3.3 Benchmark), §4 (vHL, eqs. (3)–(6))

import Mathlib

namespace DynOpaque.TwoPeriod

/-- Standing assumptions of §3 (pp. 7–8): `vH > vL`, `cH > cL`, `0 ≤ α ≤ 1`, plus the added
assumption `cL ≤ vL`, which the proof of Proposition 1 (p. 30) uses ("(vL − cL) ≥ 0"). -/
def Standing (vH vL cH cL α : ℝ) : Prop :=
  vL < vH ∧ cL < cH ∧ 0 ≤ α ∧ α ≤ 1 ∧ cL ≤ vL

/-- `vHL ≡ (vH − vL)/2 + vL` (p. 11). -/
noncomputable def vHL (vH vL : ℝ) : ℝ := (vH - vL) / 2 + vL

/-- The anecdote-averaging estimate of p. 8 with prior `ξ0` and `K` anecdotes, `nH` of which
report product `H`: `(ξ0 + nH) / (K + 1)`. -/
noncomputable def estimateK (ξ0 : ℝ) (K nH : ℕ) : ℝ := (ξ0 + (nH : ℝ)) / ((K : ℝ) + 1)

/-- The estimate of a customer with one anecdote (`K = 1`) and prior `ξ0 = 0` (p. 9):
`1/2` if the anecdote is `H` (`nH = 1`), `0` if it is `L` (`nH = 0`). -/
noncomputable def estimate (nH : ℕ) : ℝ := estimateK 0 1 nH

/-- Purchase rule (1), p. 9: a customer with estimate `e` buys at price `p` iff
`e vH + (1 − e) vL ≥ p` (equality buys). -/
def buys (vH vL e p : ℝ) : Prop := e * vH + (1 - e) * vL ≥ p

noncomputable instance (vH vL e p : ℝ) : Decidable (buys vH vL e p) :=
  inferInstanceAs (Decidable (e * vH + (1 - e) * vL ≥ p))

/-- The purchasing fraction at price `p` when each customer's single anecdote reports `H` with
probability `h`: the `H`-anecdote customers buy iff rule (1) holds at estimate `1/2`, the
`L`-anecdote customers iff it holds at estimate `0`. -/
noncomputable def frac (vH vL h p : ℝ) : ℝ :=
  h * (if buys vH vL (estimate 1) p then 1 else 0) +
    (1 - h) * (if buys vH vL (estimate 0) p then 1 else 0)

/-- Unit margin of an opaque sale at price `p` when `H` is delivered with probability `ξ`. -/
noncomputable def margin (cH cL ξ p : ℝ) : ℝ := p - ξ * cH - (1 - ξ) * cL

/-- Profit (2), p. 11, for `K = 1`: period-1 anecdotes are `H` with probability `ξ₁`, period-2
anecdotes with probability `α ξ₁ + (1 − α) ξ₂`. -/
noncomputable def opaqueProfit (vH vL cH cL α p₁ p₂ ξ₁ ξ₂ : ℝ) : ℝ :=
  frac vH vL ξ₁ p₁ * margin cH cL ξ₁ p₁ +
    frac vH vL (α * ξ₁ + (1 - α) * ξ₂) p₂ * margin cH cL ξ₂ p₂

/-- The two product versions. -/
inductive Version
  | H
  | L
  deriving DecidableEq

/-- Valuation of a version. -/
def Version.val (vH vL : ℝ) : Version → ℝ
  | .H => vH
  | .L => vL

/-- Unit cost of a version. -/
def Version.cost (cH cL : ℝ) : Version → ℝ
  | .H => cH
  | .L => cL

/-- Transparent selling (§3.3, p. 11) of version `m` at prices `q₁, q₂`: in each period the unit
mass of customers buys iff `q_t ≤ v_m` (net utility `v_m − q_t ≥ 0`). -/
noncomputable def transparentProfit (vH vL cH cL : ℝ) (m : Version) (q₁ q₂ : ℝ) : ℝ :=
  (if q₁ ≤ m.val vH vL then (1 : ℝ) else 0) * (q₁ - m.cost cH cL) +
    (if q₂ ≤ m.val vH vL then (1 : ℝ) else 0) * (q₂ - m.cost cH cL)

/-- A two-period selling policy: opaque (prices and offering probabilities) or transparent
(one version, two prices). -/
inductive Policy
  | opaque (p₁ p₂ ξ₁ ξ₂ : ℝ)
  | transparent (m : Version) (q₁ q₂ : ℝ)

/-- Feasibility: opaque prices are at most `vHL` and offering probabilities lie in `[0, 1]`;
transparent prices are unrestricted. -/
def Feasible (vH vL : ℝ) : Policy → Prop
  | .opaque p₁ p₂ ξ₁ ξ₂ =>
      p₁ ≤ vHL vH vL ∧ p₂ ≤ vHL vH vL ∧ ξ₁ ∈ Set.Icc (0 : ℝ) 1 ∧ ξ₂ ∈ Set.Icc (0 : ℝ) 1
  | .transparent _ _ _ => True

/-- Two-period profit of a policy. -/
noncomputable def profit (vH vL cH cL α : ℝ) : Policy → ℝ
  | .opaque p₁ p₂ ξ₁ ξ₂ => opaqueProfit vH vL cH cL α p₁ p₂ ξ₁ ξ₂
  | .transparent m q₁ q₂ => transparentProfit vH vL cH cL m q₁ q₂

/-- A policy is optimal iff it is feasible and earns at least the profit of every feasible
policy. -/
def IsOptimal (vH vL cH cL α : ℝ) (P : Policy) : Prop :=
  Feasible vH vL P ∧ ∀ Q : Policy, Feasible vH vL Q → profit vH vL cH cL α Q ≤ profit vH vL cH cL α P

/-- Display (3), p. 11 (`p₁ = p₂ = vHL`). -/
noncomputable def obj3 (vH vL cH cL α ξ₁ ξ₂ : ℝ) : ℝ :=
  ξ₁ * (vHL vH vL - ξ₁ * cH - (1 - ξ₁) * cL) +
    (α * ξ₁ + (1 - α) * ξ₂) * (vHL vH vL - ξ₂ * cH - (1 - ξ₂) * cL)

/-- Display (4), p. 12 (`p₁ = vHL`, `p₂ = vL`). -/
noncomputable def obj4 (vH vL cH cL ξ₁ ξ₂ : ℝ) : ℝ :=
  ξ₁ * (vHL vH vL - ξ₁ * cH - (1 - ξ₁) * cL) + (vL - ξ₂ * cH - (1 - ξ₂) * cL)

/-- Display (5), p. 12 (`p₁ = vL`, `p₂ = vHL`). -/
noncomputable def obj5 (vH vL cH cL α ξ₁ ξ₂ : ℝ) : ℝ :=
  (vL - ξ₁ * cH - (1 - ξ₁) * cL) +
    (α * ξ₁ + (1 - α) * ξ₂) * (vHL vH vL - ξ₂ * cH - (1 - ξ₂) * cL)

/-- Display (6), p. 13 (`p₁ = p₂ = vL`). -/
noncomputable def obj6 (vL cH cL ξ₁ ξ₂ : ℝ) : ℝ :=
  (vL - ξ₁ * cH - (1 - ξ₁) * cL) + (vL - ξ₂ * cH - (1 - ξ₂) * cL)

/-- The box `[0, 1] × [0, 1]` of offering-probability pairs `(ξ₁, ξ₂)`. -/
def box : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- `(ξ₁, ξ₂)` is an optimal product-offering decision for the objective `f`: it lies in the box
and maximizes `f` over the box (not necessarily uniquely). -/
def IsOptimalOffering (f : ℝ → ℝ → ℝ) (ξ₁ ξ₂ : ℝ) : Prop :=
  (ξ₁, ξ₂) ∈ box ∧ ∀ x ∈ box, f x.1 x.2 ≤ f ξ₁ ξ₂

/-- The threshold `(√17 − 3)/2` of Lemma 2 and Proposition 1. -/
noncomputable def alphaBar : ℝ := (Real.sqrt 17 - 3) / 2

end DynOpaque.TwoPeriod


