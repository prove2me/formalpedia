-- Prove2me | Definitions.Def_CalibeatBandit_Supplement_PricingRun
-- name    : CalibeatBandit_Supplement_PricingRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:29:23.666257+00:00
-- url     : https://prove2.me/theorems/d6209bdb-16aa-45a4-9811-7a2765f04c62
-- title:
--   The dynamic pricing protocol (§2.2) with $K$-sparse recommendations, and its $\mathrm{SR}_T$, $\mathrm{Rec}_T$
-- statement:
--   **Setting.** Prices lie in $[0,1]$ and the seller's production cost is $c\in[0,1]$. In each round $t$ the adversary chooses a non-increasing demand curve $D_t:[0,1]\to[0,1]$, and the revenue of price $p$ is
--   $$y_t(p)=(p-c)\,D_t(p).$$
--   The recommendations are **$K$-sparse**: a common set $S$ of at most $K$ prices contains the support of every recommended mixed strategy $q_t$.
--
--   **Protocol** (that of §2.1). In round $t$ the recommendation $q_t$ and the demand curve $D_t$ are fixed before the seller's fresh randomness, and they may be adaptive and correlated. The recommended price $J_t$ is drawn from $q_t$. The seller posts a price $P_t$ drawn from its mixed strategy, which is a probability measure on $[0,1]$ chosen from the recommended strategies and prices so far and from its own past prices and the revenues observed at them. The seller observes only the revenue $y_t(P_t)$ at its posted price.
--
--   **A dynamic pricing algorithm** is admissible if it is a measurable function of the seller's information whose values are probability measures on $[0,1]$.
--
--   **Benchmarks.**
--   $$\mathrm{SR}_T=\sup_{\sigma}\sum_{t=1}^T\big(y_t(\sigma(P_t))-y_t(P_t)\big),\qquad \mathrm{Rec}_T=\sup_{\sigma}\sum_{t=1}^T\big(y_t(\sigma(J_t))-y_t(P_t)\big),$$
--   where both suprema range over measurable maps $\sigma:[0,1]\to[0,1]$.
--
--   These are the objects of Theorem 5.1.
--
--   **Formalization Note** $S$ is a map `Fin K → ℝ`, whose image has at most $K$ elements, and $q_t$ weights its points. The seller sees each $q_t$ as a measure on prices, not the labelling of $S$. As in the base protocol, the seller also sees the drawn recommended price $J_t$. Demand curves are functions on $\mathbb R$ of which only $[0,1]$ matters. They are jointly measurable in the outcome and the price, so the observed revenue is a random variable. Rounds are $0,\dots,T-1$.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §2.2 (Dynamic Pricing), p.8 (PDF 8); K-sparse recommendations, §5.1, p.22 (PDF 22); protocol §2.1, p.7 (PDF 7)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

namespace Supplement

open MeasureTheory

/-- The **revenue** `y_t(p) = (p − c)D_t(p)` of price `p` under demand curve `D` and production
cost `c` (§2.2, p.8). -/
def revenue (c : ℝ) (D : ℝ → ℝ) (p : ℝ) : ℝ :=
  (p - c) * D p

/-- The recommended mixed strategy over prices: weight `q k` on the price `S k`, i.e. the
measure `∑_k q(k) δ_{S k}` on `ℝ`. -/
noncomputable def recMeasure {K : ℕ} (S : Fin K → ℝ) (q : Fin K → ℝ) : Measure ℝ :=
  ∑ k, ENNReal.ofReal (q k) • Measure.dirac (S k)

/-- What the seller knows before posting its price in round `t`: the recommended mixed
strategies over prices of rounds `0, …, t`, the recommended prices of rounds `0, …, t`, its own
posted prices of rounds `0, …, t − 1` and the revenues observed at them. -/
abbrev PriceHistory (t : ℕ) : Type :=
  (Fin (t + 1) → Measure ℝ) × (Fin (t + 1) → ℝ) × (Fin t → ℝ) × (Fin t → ℝ)

/-- A **dynamic pricing algorithm**: in round `t` it maps the seller's information to the mixed
strategy (a measure on prices) from which it draws its posted price. -/
abbrev PricingPolicy : Type := (t : ℕ) → PriceHistory t → Measure ℝ

/-- A dynamic pricing algorithm is **admissible** if in every round it is a measurable function
of the seller's information (a Markov kernel) whose values are probability measures on prices in
`[0, 1]`.

**Formalization Note.** Measurability is what makes the algorithm implementable on a probability
space: it guarantees that the protocol has runs for every environment, so the quantification
over runs in `PricingRegretBound` is never vacuous for an admissible algorithm. -/
def IsPricingPolicy (seller : PricingPolicy) : Prop :=
  ∀ t, Measurable (seller t) ∧
    ∀ h, IsProbabilityMeasure (seller t h) ∧ seller t h (Set.Icc (0 : ℝ) 1)ᶜ = 0

/-- **A run of the dynamic pricing protocol** (§2.2 with the protocol of §2.1) over `T` rounds,
with production cost `c`, a common set of recommended prices `S = {S k : k ∈ Fin K}` (so
`|S| ≤ K`: the recommendations are `K`-sparse), driven by the seller's algorithm `seller`, on a
probability space `(Ω, P)`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §2.2 "Dynamic
Pricing", p.8: "actions are prices p ∈ P ⊆ [0, 1], and the adversary chooses a non-increasing
demand function D_t : [0, 1] → [0, 1]. The seller's fixed production cost is c ∈ [0, 1] and the
revenue of price p is y_t(p) = (p − c)D_t(p). Both the recommendation and the seller's choice
are mixed strategies over prices … The seller observes only the revenue (or equivalently the
demand) at the posted price." §5.1, p.22: "the recommendations are K-sparse if there is a common
set S with |S| ≤ K such that every recommendation q_t is supported on S." The interaction
protocol (adaptive, randomized, correlated environment, non-anticipation) is that of §2.1, p.7.

Fields:
* `info t`: everything fixed before the seller's round-`t` draw;
* `q t`: the recommendation, weights on the prices `S k`; `D t`: the demand curve; both
  `info t`-measurable (non-anticipation); `D_t` maps `[0, 1]` into `[0, 1]` and is
  non-increasing there;
* `J t`: the recommended price is `S (J t)`, `P[J_t = k | info t] = q_t(k)`;
* `price t`: the posted price; given `info t` and `J_t` its law is the seller's mixed strategy,
  evaluated on the seller's information (`PriceHistory`).

**Formalization Note.** Rounds are `0, …, T − 1`. The demand curve is a function `ℝ → ℝ` of
which only `[0, 1]` matters. Its joint measurability in `(ω, p)` makes the observed revenue
`y_t(P_t)` a random variable; it excludes only environments in which that expectation is
undefined. As in the base protocol, the seller sees the drawn recommended price `S (J t)`; it
also sees the recommended mixed strategies as measures on prices, not the labelling `S`. -/
structure PricingRun (K T : ℕ) (c : ℝ) (S : Fin K → ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (seller : PricingPolicy) where
  /-- information available before the seller's draw in round `t` -/
  info : ℕ → MeasurableSpace Ω
  /-- recommended mixed strategy: weight `q t ω k` on the price `S k` -/
  q : ℕ → Ω → Fin K → ℝ
  /-- demand curve `D_t` -/
  D : ℕ → Ω → ℝ → ℝ
  /-- recommended price index: the recommended price is `S (J t ω)` -/
  J : ℕ → Ω → Fin K
  /-- posted price `P_t` -/
  price : ℕ → Ω → ℝ
  info_le : ∀ t ≤ T, info t ≤ mΩ
  info_mono : ∀ t < T, info t ≤ info (t + 1)
  q_measurable : ∀ t < T, Measurable[info t] (q t)
  D_measurable : ∀ t < T,
    Measurable[MeasurableSpace.prod (info t) (borel ℝ)] (Function.uncurry (D t))
  J_measurable : ∀ t < T, Measurable[info (t + 1)] (J t)
  price_measurable : ∀ t < T, Measurable[info (t + 1)] (price t)
  q_nonneg : ∀ t < T, ∀ ω k, 0 ≤ q t ω k
  q_sum : ∀ t < T, ∀ ω, ∑ k, q t ω k = 1
  D_mem : ∀ t < T, ∀ ω, ∀ p ∈ Set.Icc (0 : ℝ) 1, D t ω p ∈ Set.Icc (0 : ℝ) 1
  D_antitone : ∀ t < T, ∀ ω, AntitoneOn (D t ω) (Set.Icc (0 : ℝ) 1)
  J_law : ∀ t < T, ∀ k : Fin K,
    condExp (info t) P ((J t ⁻¹' {k}).indicator (fun _ => (1 : ℝ))) =ᵐ[P] fun ω => q t ω k
  price_law : ∀ t < T, ∀ B : Set ℝ, MeasurableSet B →
    condExp (info t ⊔ MeasurableSpace.comap (J t) inferInstance) P
        ((price t ⁻¹' B).indicator (fun _ => (1 : ℝ)))
      =ᵐ[P] fun ω => (seller t
          ((fun s => recMeasure S (q s ω)), (fun s => S (J s ω)), (fun s => price s ω),
            (fun s => revenue c (D s ω) (price s ω))) B).toReal

/-- The pricing **swap regret** `SR_T = sup_σ ∑_{t=1}^T (y_t(σ(P_t)) − y_t(P_t))`, the supremum
over measurable maps `σ` from prices to prices in `[0, 1]` (§2.2, p.8), for demand curves `D`
and posted prices `price`. -/
noncomputable def pricingSR (T : ℕ) (c : ℝ) (D : ℕ → ℝ → ℝ) (price : ℕ → ℝ) : ℝ :=
  sSup {x | ∃ σ : ℝ → ℝ, Measurable σ ∧ (∀ p, σ p ∈ Set.Icc (0 : ℝ) 1) ∧
    x = ∑ t ∈ Finset.range T, (revenue c (D t) (σ (price t)) - revenue c (D t) (price t))}

/-- The pricing **reward loss** `Rec_T = sup_σ ∑_{t=1}^T (y_t(σ(J_t)) − y_t(P_t))`, the supremum
over measurable maps `σ` from prices to prices in `[0, 1]` (§2.2, p.8), for demand curves `D`,
recommended prices `recPrice` and posted prices `price`. -/
noncomputable def pricingRec (T : ℕ) (c : ℝ) (D : ℕ → ℝ → ℝ) (recPrice price : ℕ → ℝ) : ℝ :=
  sSup {x | ∃ σ : ℝ → ℝ, Measurable σ ∧ (∀ p, σ p ∈ Set.Icc (0 : ℝ) 1) ∧
    x = ∑ t ∈ Finset.range T, (revenue c (D t) (σ (recPrice t)) - revenue c (D t) (price t))}

end Supplement

end CalibeatBandit


