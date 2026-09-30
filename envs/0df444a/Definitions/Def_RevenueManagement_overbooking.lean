-- Prove2me | Definitions.Def_RevenueManagement_overbooking
-- name    : RevenueManagement_overbooking
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T00:38:25.847879+00:00
-- url     : https://prove2.me/theorems/b7ec47db-9fd3-49ae-85e7-150fd53bcadd
-- title:
--   Overbooking, Chapter 4: the dynamic overbooking model, overbooking limits and the limit policy, and the substitutable-capacity model with its transportation problem and expected net revenue
-- statement:
--   The two overbooking models of Chapter 4 of Talluri and van Ryzin.
--
--   **Dynamic overbooking** (Sect. 4.3.1, after Chatwin). Over periods $t = 1, \dots, T$ a firm
--   with capacity $C$ holds $y$ reservations; in period $t$ it sees $D_t$ new requests (pmf
--   $f_t$ on $\mathbb N$), raises the booking level to $x \in [y, y + D_t]$ collecting $p(t)$ per
--   new reservation, and then each reservation survives the period independently with
--   probability $q_t$, a cancellation refunding $r(t)$. At the deadline the terminal value (4.11)
--   is $V_{T+1}(y) = 0$ for $y \le C$ and $-c(y - C)$ for $y > C$, with $c$ the convex
--   denied-service cost. The data form `DynOverbooking`, `IsModel` states the assumptions
--   (pmfs, $q_t \in [0,1]$, $p, r \ge 0$, and $c(0) = 0 \le c(k)$, i.e. a cost that penalizes denied
--   service) and `IsConvexSeq` convexity on $\mathbb N$. The normalization $c(0) = 0$ is needed.
--   (4.11) never evaluates $c(0)$, and a sequence such as $c = (10, 5, 5, \dots)$ is convex on
--   $\mathbb N$ but gives the non-concave terminal value $-5 \cdot 1\{y > C\}$, under which
--   Proposition 4.1 fails ($T = 1$, $C = 1$, $q = 1$, $p = 3$, $D = 2$: the greatest optimal
--   limit is $+\infty$, and booking 2 earns 1 against 3 for booking 1). The
--   recursion is $v_{t+1}(x) = \mathbb E[V_{t+1}(Z_t(x)) - (x - Z_t(x)) r(t)]$ with
--   $Z_t(x) \sim \mathrm{Bin}(x, q_t)$ (`postValue`) and
--   $V_t(y) = \mathbb E[\max_{y \le x \le y + D_t}\{v_{t+1}(x) + (x - y) p(t)\}]$ (`value`).
--   `IsOptimalLevel t y d x` says $x$ attains that maximum, `limitObjective t x` is
--   $v_{t+1}(x) + x\,p(t)$, and the **greatest optimal overbooking limit** `overbookingLimit t`
--   is the largest $x$ at which `limitObjective` is at least its value at every smaller level,
--   an element of $\mathbb N \cup \{\infty\}$ that is $\infty$ when accepting is always better.
--   The **limit policy** `limitPolicy L y d` books $\min\{y + d, \max\{y, L\}\}$: accept until
--   the reservations on hand reach $L$.
--
--   **Substitutable capacity** (Sect. 4.5). Classes `Fin n`, resources `Fin (m+1)` with $0$ the
--   virtual denied-service resource; $h_{ji}$ is the net benefit of serving a class-$j$ customer
--   on resource $i$ and $C_i$ the capacity of resource $i \ne 0$. The transportation problem
--   (TP) `serviceValue h Cap z` is $V(z, C) = \max \sum_{j,i} h_{ji} z_{ji}$ over
--   $z_{ji} \ge 0$ with $\sum_i z_{ji} = z_j$ and $\sum_j z_{ji} \le C_i$ for $i \ne 0$. With
--   $y_j$ reservations on hand, final levels $x_j$, prices $p_j$, refunds $s_j$ and show demands
--   $Z_j \sim \mathrm{Poisson}(q_j x_j)$ independent, the **expected net revenue** (4.21)
--   `expNetRevenue h Cap p s q y x` is
--   $G(x) = p^\top(x - y) - \mathbb E[s^\top(x - Z(x))] + \mathbb E[V(Z(x), C)]$.
--   `jointLimit … x i` is the greatest optimal booking limit of class $i$ with the other classes
--   held at the levels of $x$, again in $\mathbb N \cup \{\infty\}$.
--
--   **Formalization Note** Periods are natural numbers and `value t` is the value with
--   $T + 1 - t$ periods to go; the book's range $1 \le t \le T$ is a hypothesis of the theorems.
--   The expectation over $D_t$ is a `tsum` against the pmf and the expectation over
--   $Z_t(x)$ a finite binomial sum. The greatest optimal limit is defined as a supremum in
--   $\mathbb N \cup \{\infty\}$ because with a mild denied-service cost accepting every request
--   can be optimal, in which case the book's "critical value" is $+\infty$. In the
--   substitutable-capacity model the virtual resource is uncapacitated, the book's "finite but
--   very high capacity" $C_0$ taken as infinite, so that (TP) is feasible for every Poisson
--   realization. Eq. (4.21) is printed with $-\mathbb E[V(Z(x), C)]$; since $V$ is the maximum
--   net benefit of the service period, the expected net revenue adds it, and the sign here is
--   $+$, without which Proposition 4.4 fails.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, Sect. 4.3.1 pp. 152-153 (Eq. 4.11 and the recursion), Sect. 4.5.1 pp. 162-164 (TP, Eq. 4.18-4.21)

import Mathlib

namespace RevenueManagement

/-! ### Overbooking, Chapter 4 of Talluri and van Ryzin -/

/-! #### The dynamic overbooking model, Sect. 4.3.1 -/

/-- The binomial pmf `P(Bin(x, q) = k)`. -/
noncomputable def binomPmf (q : ℝ) (x k : ℕ) : ℝ := (x.choose k : ℝ) * q ^ k * (1 - q) ^ (x - k)

/-- The data of the dynamic overbooking model: horizon `T`, capacity `C`, denied-service cost
`c`, revenue `p t` per reservation accepted in period `t`, refund `r t` per cancellation in period
`t`, survival probability `q t` of a reservation over period `t`, and the pmf `f t` of the demand
`D_t` for new reservations in period `t`. -/
structure DynOverbooking where
  T : ℕ
  C : ℕ
  c : ℕ → ℝ
  p : ℕ → ℝ
  r : ℕ → ℝ
  q : ℕ → ℝ
  f : ℕ → ℕ → ℝ

/-- The model's assumptions: each `f t` is a pmf on `ℕ`, `0 ≤ q t ≤ 1`, `p t ≥ 0`, `r t ≥ 0`, and
`c` is a cost penalizing denied service: `c 0 = 0` and `c k ≥ 0`. (4.11) never reads `c 0`, so
without `c 0 = 0` a sequence convex on `ℕ` need not make the terminal value concave. -/
def DynOverbooking.IsModel (M : DynOverbooking) : Prop :=
  (∀ t, (∀ d, 0 ≤ M.f t d) ∧ HasSum (M.f t) 1) ∧ (∀ t, 0 ≤ M.q t ∧ M.q t ≤ 1) ∧
    (∀ t, 0 ≤ M.p t) ∧ (∀ t, 0 ≤ M.r t) ∧ M.c 0 = 0 ∧ (∀ k, 0 ≤ M.c k)

/-- `c` is convex on `ℕ`: nondecreasing differences. -/
def IsConvexSeq (c : ℕ → ℝ) : Prop := ∀ k, c (k + 1) - c k ≤ c (k + 2) - c (k + 1)

/-- The value function with `k` periods to go (period `t = T + 1 − k`) and `y` reservations on
hand: the terminal value (4.11) with no period to go, and otherwise the recursion of Sect. 4.3.1,
`V_t(y) = E[max_{y ≤ x ≤ y + D_t} {v_{t+1}(x) + (x − y) p(t)}]` with
`v_{t+1}(x) = E[V_{t+1}(Z_t(x)) − (x − Z_t(x)) r(t)]`, `Z_t(x) ~ Bin(x, q_t)`. -/
noncomputable def DynOverbooking.valueGo (M : DynOverbooking) : ℕ → ℕ → ℝ
  | 0, y => if y ≤ M.C then 0 else -(M.c (y - M.C))
  | k + 1, y => ∑' d, M.f (M.T - k) d *
      (Finset.Icc y (y + d)).sup' ⟨y, Finset.mem_Icc.2 ⟨le_rfl, Nat.le_add_right _ _⟩⟩ (fun x =>
        (∑ z ∈ Finset.range (x + 1), binomPmf (M.q (M.T - k)) x z *
          (M.valueGo k z - ((x : ℝ) - z) * M.r (M.T - k))) + ((x : ℝ) - y) * M.p (M.T - k))

/-- `V_t(y)` for `t = 1, …, T + 1`. -/
noncomputable def DynOverbooking.value (M : DynOverbooking) (t y : ℕ) : ℝ :=
  M.valueGo (M.T + 1 - t) y

/-- `v_{t+1}(x) = E[V_{t+1}(Z_t(x)) − (x − Z_t(x)) r(t)]`, the value of ending period `t` with `x`
reservations before cancellations. -/
noncomputable def DynOverbooking.postValue (M : DynOverbooking) (t x : ℕ) : ℝ :=
  ∑ z ∈ Finset.range (x + 1), binomPmf (M.q t) x z * (M.value (t + 1) z - ((x : ℝ) - z) * M.r t)

/-- `v_{t+1}(x) + x p(t)`, the objective whose maximizer is the overbooking limit of period `t`. -/
noncomputable def DynOverbooking.limitObjective (M : DynOverbooking) (t x : ℕ) : ℝ :=
  M.postValue t x + x * M.p t

/-- `x` is an optimal booking level in period `t` with `y` reservations on hand and `d` new
requests: `y ≤ x ≤ y + d` and it maximizes `v_{t+1}(x) + (x − y) p(t)` over that range. -/
def DynOverbooking.IsOptimalLevel (M : DynOverbooking) (t y d x : ℕ) : Prop :=
  y ≤ x ∧ x ≤ y + d ∧ ∀ x', y ≤ x' → x' ≤ y + d →
    M.postValue t x' + ((x' : ℝ) - y) * M.p t ≤ M.postValue t x + ((x : ℝ) - y) * M.p t

/-- The greatest optimal overbooking limit `x*(t)`: the largest `x` at which
`v_{t+1}(x) + x p(t)` is at least its value at every smaller level, as an element of `ℕ∞`, `⊤`
when accepting is always better. -/
noncomputable def DynOverbooking.overbookingLimit (M : DynOverbooking) (t : ℕ) : ℕ∞ :=
  sSup ((fun x : ℕ => (x : ℕ∞)) ''
    {x | ∀ x' ≤ x, M.limitObjective t x' ≤ M.limitObjective t x})

/-- The overbooking-limit policy with limit `L`: with `y` on hand and `d` requests, accept new
reservations until the total reaches `L`, i.e. book `min {y + d, max {y, L}}`. -/
noncomputable def limitPolicy (L : ℕ∞) (y d : ℕ) : ℕ :=
  (min ((y + d : ℕ) : ℕ∞) (max (y : ℕ∞) L)).toNat

/-! #### Substitutable capacity, Sect. 4.5 -/

/-- The Poisson pmf `P(Poisson(μ) = k)`. -/
noncomputable def poissonPmf (μ : ℝ) (k : ℕ) : ℝ := Real.exp (-μ) * μ ^ k / k.factorial

/-- The service-period transportation problem (TP): the maximum net benefit `V(z, C)` of assigning
`z_j` surviving customers of each class `j : Fin n` to the resources `i : Fin (m+1)`, where
resource `0` is the virtual denied-service resource (uncapacitated) and resource `i ≠ 0` has
capacity `Cap i`; `h j i` is the net benefit of assigning a class-`j` customer to resource `i`. -/
noncomputable def serviceValue {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ) (Cap : Fin (m + 1) → ℝ)
    (z : Fin n → ℕ) : ℝ :=
  sSup {w | ∃ a : Fin n → Fin (m + 1) → ℝ, (∀ j i, 0 ≤ a j i) ∧ (∀ j, ∑ i, a j i = z j) ∧
    (∀ i, i ≠ 0 → ∑ j, a j i ≤ Cap i) ∧ w = ∑ j, ∑ i, h j i * a j i}

/-- The expected net revenue `G(x)` of Eq. (4.21) for final overbooking levels `x` given `y`
reservations on hand, with show demands `Z_j ~ Poisson(q_j x_j)` independent across classes:
`pᵀ(x − y) − E[sᵀ(x − Z(x))] + E[V(Z(x), C)]`. -/
noncomputable def expNetRevenue {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ) (Cap : Fin (m + 1) → ℝ)
    (p s q : Fin n → ℝ) (y x : Fin n → ℕ) : ℝ :=
  ∑ j, p j * ((x j : ℝ) - y j) +
    ∑' z : Fin n → ℕ, (∏ j, poissonPmf (q j * x j) (z j)) *
      (serviceValue h Cap z - ∑ j, s j * ((x j : ℝ) - z j))

/-- The greatest optimal booking limit of class `i` when the other classes are held at the levels
of `x`: the largest `k` at which `G(x with x_i := k)` is at least its value at every smaller `k`,
as an element of `ℕ∞`. -/
noncomputable def jointLimit {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ) (Cap : Fin (m + 1) → ℝ)
    (p s q : Fin n → ℝ) (y x : Fin n → ℕ) (i : Fin n) : ℕ∞ :=
  sSup ((fun k : ℕ => (k : ℕ∞)) '' {k | ∀ k' ≤ k,
    expNetRevenue h Cap p s q y (Function.update x i k') ≤
      expNetRevenue h Cap p s q y (Function.update x i k)})

end RevenueManagement


