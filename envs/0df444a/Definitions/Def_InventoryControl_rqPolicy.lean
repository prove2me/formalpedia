-- Prove2me | Definitions.Def_InventoryControl_rqPolicy
-- name    : InventoryControl_rqPolicy
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T00:00:12.182145+00:00
-- url     : https://prove2.me/theorems/53cdd9ed-8e83-42de-9c71-0712cb4d5867
-- title:
--   Compound Poisson demand, ordering policies in batches of $Q$, the $(R,Q)$ policy, and the long-run average cost of Sect. 6.2.1
-- statement:
--   The model of Axsäter, *Inventory Control*, Sect. 6.2.1, in which an $(R,Q)$ policy is shown to
--   be optimal.
--
--   **Demand.** A `CompoundPoissonDemand` on a probability space consists of a rate $\lambda > 0$,
--   a distribution $f_k$ of the customer demand sizes on the positive integers ($f_0 = 0$,
--   $\sum_k f_k = 1$), and two sequences of random variables: the inter-arrival times
--   $\tau_0, \tau_1, \dots$, each exponential with rate $\lambda$, and the demand sizes
--   $D_0, D_1, \dots$, each with law $f$. The inter-arrival times are independent of each other,
--   the demand sizes are independent of each other, and the whole sequence of inter-arrival
--   times is independent of the whole sequence of demand sizes. The book's standing assumption
--   of Sect. 5.1.1, that not all demands are multiples of some integer larger than one, is the
--   field `size_aperiodic`: for every $d \ge 2$ some demand size with positive probability is not
--   a multiple of $d$. The $n$-th customer arrives at $T_n = \tau_0 + \dots + \tau_{n-1}$
--   (`arrival`), $N(t)$ (`count`) is the number of customers who have arrived by time $t$, and
--   $S_n = D_0 + \dots + D_{n-1}$ (`cumDemand`) is the demand of the first $n$ customers.
--
--   **Policies.** Orders are multiples of a given batch quantity $Q$ and can only be triggered by
--   customer demands, so a policy is any rule $m$ that decides, at the $n$-th demand epoch, how
--   many batches $m_n \in \{0, 1, 2, \dots\}$ to order. Given an initial inventory position $y_0$,
--   the position after the $n$-th demand is (Eq. 6.22)
--   $$ y_{n+1} \;=\; y_n - D_n + m_n Q , $$
--   which is `ipPath`, and the position at time $t$ is $y_{N(t)}$, which is `ipAt`. No
--   measurability or adaptedness is imposed on $m$: the lower bound of Proposition 6.1 holds for
--   every rule whatsoever.
--
--   **The $(R,Q)$ policy.** `rqIP R Q y0 n` is the position after the $n$-th demand when an order
--   is triggered as soon as the position is at or below $R$, for the smallest number of batches
--   that brings it above $R$ (Sect. 5.3.1); `rqOrders R Q y0 n` is the number of batches it orders
--   at the $n$-th demand. `reduceToBand R Q z` is the unique integer $z + xQ$, $x \in \mathbb{Z}$,
--   lying in $\{R+1, \dots, R+Q\}$, the map $y_t \mapsto y_t'$ of the proof of Proposition 6.1.
--
--   **Cost.** With $g(k)$ the holding-plus-shortage cost rate of holding the inventory position at
--   $k$ (from the discrete model), the cost rate charged at time $t + L$ is $g(y_t)$, and
--   $\bar g(y) = \sum_{j=1}^{Q} g(y+j)$ (`windowCost`) is the total cost of the band
--   $\{y+1, \dots, y+Q\}$. `avgCost X D h b1 L Q y0 m T` is the average cost rate over $[0, T]$,
--   $$ \frac{1}{T}\int_0^T g\big(y(t - L)\big)\,\mathrm{d}t, $$
--   with $y(s) = y_0$ for $s < 0$.
--
--   **Formalization Note** `count t` is the supremum of $\{n : T_n \le t\}$, which is the number
--   of arrivals by time $t$ whenever the arrival times tend to infinity, as they do almost surely;
--   on the null set where they do not, it is the junk value $0$. `avgCost` at $T = 0$ is $0$
--   (division by zero); only its behaviour as $T \to \infty$ is ever asserted. `rqOrders` is
--   computed from two consecutive values of `rqIP`, so that the $(R,Q)$ policy is literally one of
--   the rules `m` and `ipPath` under it recovers `rqIP`.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, Sect. 6.2.1 pp. 113-115 (the model, ḡ(y), Lemma 6.1, Eq. 6.22-6.23), Sect. 5.1.1 pp. 64-65 (compound Poisson demand), Sect. 5.3.1 p. 74 (the (R, Q) ordering rule)

import Definitions.Def_InventoryControl_rqDiscrete

open MeasureTheory ProbabilityTheory

namespace InventoryControl

/-- Compound Poisson demand (Axsäter, *Inventory Control*, Sect. 5.1.1): customers arrive
according to a Poisson process with rate `lam` (i.i.d. exponential inter-arrival times `gap`)
and the `n`-th customer demands `dem n` units, i.i.d. with law `size` on the positive integers,
the two sequences being independent.  `size_aperiodic` is the standing assumption that not all
demands are multiples of some integer larger than one. -/
structure CompoundPoissonDemand {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) where
  lam : ℝ
  lam_pos : 0 < lam
  size : ℕ → ℝ
  size_zero : size 0 = 0
  size_nonneg : ∀ k, 0 ≤ size k
  size_hasSum : HasSum size 1
  size_aperiodic : ∀ d : ℕ, 2 ≤ d → ∃ k, 0 < size k ∧ ¬ d ∣ k
  gap : ℕ → Ω → ℝ
  dem : ℕ → Ω → ℕ
  measurable_gap : ∀ n, Measurable (gap n)
  measurable_dem : ∀ n, Measurable (dem n)
  gap_law : ∀ n, P.map (gap n) = expMeasure lam
  dem_law : ∀ n k, P.real {ω | dem n ω = k} = size k
  indep_gap : iIndepFun gap P
  indep_dem : iIndepFun dem P
  indep_gap_dem : IndepFun (fun ω n => gap n ω) (fun ω n => dem n ω) P

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The arrival time of the `n`-th customer: `T₀ = 0`, `Tₙ = τ₀ + ⋯ + τₙ₋₁`. -/
noncomputable def CompoundPoissonDemand.arrival (X : CompoundPoissonDemand P) (n : ℕ) (ω : Ω) :
    ℝ :=
  ∑ i ∈ Finset.range n, X.gap i ω

/-- The number of customers who have arrived by time `t`. -/
noncomputable def CompoundPoissonDemand.count (X : CompoundPoissonDemand P) (t : ℝ) (ω : Ω) :
    ℕ :=
  sSup {n : ℕ | X.arrival n ω ≤ t}

/-- The total demand of the first `n` customers, `Sₙ = D₀ + ⋯ + Dₙ₋₁`. -/
def CompoundPoissonDemand.cumDemand (X : CompoundPoissonDemand P) (n : ℕ) (ω : Ω) : ℕ :=
  ∑ i ∈ Finset.range n, X.dem i ω

/-- The inventory position after the `n`-th demand under an arbitrary ordering rule `m`
(`m n ω` batches of `Q` are ordered at the `n`-th demand epoch), Eq. (6.22):
`y⁺ = y⁻ - Dₜ + mQ`. -/
def ipPath (X : CompoundPoissonDemand P) (Q : ℕ) (y0 : ℤ) (m : ℕ → Ω → ℕ) : ℕ → Ω → ℤ
  | 0, _ => y0
  | n + 1, ω => ipPath X Q y0 m n ω - X.dem n ω + (Q : ℤ) * m n ω

/-- The inventory position at time `t`: the position after the last demand at or before `t`. -/
noncomputable def ipAt (X : CompoundPoissonDemand P) (Q : ℕ) (y0 : ℤ) (m : ℕ → Ω → ℕ) (t : ℝ)
    (ω : Ω) : ℤ :=
  ipPath X Q y0 m (X.count t ω) ω

/-- The reduction of an integer inventory position into the band `{R+1, …, R+Q}` by a
multiple of `Q`: the map `yₜ ↦ y'ₜ` in the proof of Proposition 6.1. -/
def reduceToBand (R : ℤ) (Q : ℕ) (z : ℤ) : ℤ := R + 1 + (z - (R + 1)) % (Q : ℤ)

/-- The inventory position after the `n`-th demand under the `(R, Q)` policy: whenever the
position falls to `R` or below, the smallest number of batches of `Q` bringing it above `R` is
ordered (Sect. 5.3.1). -/
def rqIP (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (y0 : ℤ) : ℕ → Ω → ℤ
  | 0, _ => y0
  | n + 1, ω =>
    let y := rqIP X R Q y0 n ω - X.dem n ω
    if R + 1 ≤ y then y else y + (Q : ℤ) * ((R + 1 - y + (Q : ℤ) - 1) / (Q : ℤ))

/-- The number of batches the `(R, Q)` policy orders at the `n`-th demand epoch. -/
def rqOrders (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (y0 : ℤ) (n : ℕ) (ω : Ω) : ℕ :=
  ((rqIP X R Q y0 (n + 1) ω - (rqIP X R Q y0 n ω - X.dem n ω)) / (Q : ℤ)).toNat

/-- `ḡ(y) = ∑_{j=1}^{Q} g(y + j)`, Axsäter, *Inventory Control*, p. 114. -/
noncomputable def windowCost (D : DiscreteDemand) (h b1 : ℝ) (Q : ℕ) (y : ℤ) : ℝ :=
  ∑ j ∈ Finset.range Q, sPolicyCost D h b1 (y + 1 + j)

/-- The average cost rate over `[0, T]` under the rule `m`: the cost rate charged at time `t`
is `g` of the inventory position a lead-time `L` earlier (Sect. 6.2.1, "the cost rate at time
`t + L` is then `g(yₜ)`"), with the position equal to `y0` before time `0`. -/
noncomputable def avgCost (X : CompoundPoissonDemand P) (D : DiscreteDemand) (h b1 L : ℝ)
    (Q : ℕ) (y0 : ℤ) (m : ℕ → Ω → ℕ) (T : ℝ) (ω : Ω) : ℝ :=
  (1 / T) * ∫ t in (0 : ℝ)..T,
    sPolicyCost D h b1 (if t < L then y0 else ipAt X Q y0 m (t - L) ω)

end InventoryControl


