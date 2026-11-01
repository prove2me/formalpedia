-- Prove2me | Definitions.Def_StatefulPricing_Instance
-- name    : StatefulPricing_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:36.314827+00:00
-- url     : https://prove2.me/theorems/127b272d-29af-4420-97bf-1311a87246ff
-- title:
--   DRACC instances, demand sets, inventories, feasible prices and pricing policies
-- statement:
--   A **DRACC instance** (dynamic resource allocation with capacity constraints) has horizon $T$, rounds $t=1,\dots,T$, and finitely many resources. Resource $i$ arrives at the beginning of round $t_a(i)$ and departs at the end of round $t_e(i)$, with $1\le t_a(i)\le t_e(i)\le T$, and carries $c(i)$ units, $1\le c(i)\le C$. The active set is $A_t=\{i: t_a(i)\le t\le t_e(i)\}$, with $|A_t|\le W$. User $t$ has a valuation $v_t:2^{A_t}\to[0,1)$ with $v_t(\emptyset)=0$ and no other condition. At prices $p$ she buys her **demand set** (Eq. (1))
--   $$
--   \hat A^{p}_t=\operatorname*{argmax}_{A\subseteq A_t}\Big(v_t(A)-\sum_{i\in A}p(i)\Big),\qquad \hat q^{p}_t=\sum_{i\in\hat A^p_t}p(i),
--   $$
--   ties broken by a fixed order on bundles. The inventory vector $\lambda_t$ starts at $\lambda_t(i)=c(i)$ on arrival and drops by one when a unit of $i$ is sold. A price vector is **feasible** for $\lambda$ on $A$ if all prices lie in $(0,1]$ and $p(i)=1$ for every $i\in A$ with $\lambda(i)=0$. A **pricing policy** $\gamma$ maps an active set and an inventory vector on it to a feasible price vector; playing $\gamma$ repeatedly gives the trajectory $\lambda^\gamma_t$, the prices $p^\gamma_t=\gamma(A_t,\lambda^\gamma_t)$ and the revenue $\sum_{t=1}^T\hat q^{\gamma}_t$.
--
--   These objects are the model of §2 and the setting of the goal theorem.
--
--   **Formalization Note** Resources are natural numbers and the resources of an instance are a finite set $R$, so the number $N=|R|$ is arbitrary. An inventory vector is a function $\mathbb N\to\mathbb N$ that is $0$ off the active set, and a price vector a function $\mathbb N\to\mathbb R$; prices are required to lie in $(0,1]$ at every resource (a price vector on $A_t$ is extended by $1$, which changes no demand set). Ties are broken by a rank function on bundles: the demand set is the maximizer of least rank, unique when the rank is injective; every lexicographic order on finite sets is of this form. A policy takes the active set as an explicit argument, because the paper's inventory vector carries its index set $A_t$; the time is not an argument (footnote 2, p.5). The inventory update subtracts in $\mathbb N$; a sold resource always has positive stock along feasible play.
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, §2, pp.4–5, Eq. (1)

import Mathlib

set_option autoImplicit false

namespace StatefulPricing

/-- **DRACC instance** (dynamic resource allocation with capacity constraints), arXiv:2005.01869v2,
§2, p.4: "Consider N dynamic resources and T strategic myopic users arriving sequentially over
rounds t = 1, . . . , T … Resource i ∈ [N] arrives at the beginning of round ta(i) and departs at
the end of round te(i), where 1 ≤ ta(i) ≤ te(i) ≤ T; upon arrival, it includes c(i) ∈ Z>0 units.
… Let C and W be upper bounds on maxi∈[N] c(i) and maxt∈[T] |At|, respectively. The arriving user
at time t has a valuation function vt : 2^At → [0, 1) … We assume that vt(∅) = 0".

An instance with horizon `T` and bounds `C` (capacities) and `W` (simultaneously active
resources).

**Formalization Note.** Resources are natural numbers; the resources of the instance are the
finite set `R` (so `N = |R|` is arbitrary and not bounded by any parameter). Rounds are `1, …, T`.
The valuation `v t A` matters only for `1 ≤ t ≤ T` and `A ⊆ A_t`, where it lies in `[0,1)`;
no other condition (monotonicity, additivity) is imposed. -/
structure Instance (T C W : ℕ) where
  /-- The finite set of resources. -/
  R : Finset ℕ
  /-- The arrival round `ta(i)`. -/
  ta : ℕ → ℕ
  /-- The departure round `te(i)`. -/
  te : ℕ → ℕ
  /-- The initial capacity `c(i)`. -/
  cap : ℕ → ℕ
  /-- The valuation `v_t(A)` of user `t` for the bundle `A`. -/
  v : ℕ → Finset ℕ → ℝ
  one_le_ta : ∀ i ∈ R, 1 ≤ ta i
  ta_le_te : ∀ i ∈ R, ta i ≤ te i
  te_le_T : ∀ i ∈ R, te i ≤ T
  one_le_cap : ∀ i ∈ R, 1 ≤ cap i
  cap_le_C : ∀ i ∈ R, cap i ≤ C
  card_active_le_W : ∀ t, 1 ≤ t → t ≤ T → (R.filter (fun i => ta i ≤ t ∧ t ≤ te i)).card ≤ W
  v_nonneg : ∀ t, 1 ≤ t → t ≤ T → ∀ A ⊆ R.filter (fun i => ta i ≤ t ∧ t ≤ te i), 0 ≤ v t A
  v_lt_one : ∀ t, 1 ≤ t → t ≤ T → ∀ A ⊆ R.filter (fun i => ta i ≤ t ∧ t ≤ te i), v t A < 1
  v_empty : ∀ t, v t ∅ = 0

namespace Instance

variable {T C W : ℕ}

/-- The set `A_t` of resources active at time `t`: `ta(i) ≤ t ≤ te(i)` (arXiv:2005.01869v2,
p.4). -/
def active (I : Instance T C W) (t : ℕ) : Finset ℕ :=
  I.R.filter (fun i => I.ta i ≤ t ∧ t ≤ I.te i)

/-- The utility `v_t(A) − Σ_{i∈A} p(i)` of user `t` for the bundle `A` at prices `p`
(quasi-linear users, arXiv:2005.01869v2, p.4). -/
def utility (I : Instance T C W) (t : ℕ) (p : ℕ → ℝ) (A : Finset ℕ) : ℝ :=
  I.v t A - ∑ i ∈ A, p i

/-- The demand set `Â^p_t = argmax_{A⊆At} (vt(A) − Σ_{i∈A} p(i))`, Eq. (1) (arXiv:2005.01869v2,
p.5), "consistently breaking argmax ties according to the lexicographic order on At".

**Formalization Note.** Ties are broken by a fixed order on bundles, given as a rank function
`rank : Finset ℕ → ℕ`: the demand set is a maximizer of least rank. When `rank` is injective (as
every statement assumes) it is the unique such maximizer; every lexicographic order on finite sets
of resources is induced by an injective rank. The set of maximizers is never empty (finitely many
bundles); the fallback `∅` is never used. -/
noncomputable def demand (rank : Finset ℕ → ℕ) (I : Instance T C W) (t : ℕ) (p : ℕ → ℝ) :
    Finset ℕ := by
  classical
  exact
    let best := (I.active t).powerset.filter
      (fun A => ∀ B ∈ (I.active t).powerset, I.utility t p B ≤ I.utility t p A)
    if h : best.Nonempty then Classical.choose (best.exists_min_image rank h) else ∅

/-- The payment `q̂^p_t = Σ_{i∈Â^p_t} p(i)` of user `t` at prices `p`, Eq. (1)
(arXiv:2005.01869v2, p.5). -/
noncomputable def pay (rank : Finset ℕ → ℕ) (I : Instance T C W) (t : ℕ) (p : ℕ → ℝ) : ℝ :=
  ∑ i ∈ I.demand rank t p, p i

/-- The initial inventory vector: `λ₁(i) = c(i)` for `i ∈ A₁`.

**Formalization Note.** An inventory vector is a function `ℕ → ℕ` that is `0` off the active
set. -/
def initInv (I : Instance T C W) : ℕ → ℕ :=
  fun i => if i ∈ I.active 1 then I.cap i else 0

/-- The inventory update at the end of round `t` when the set `sold` of resources is sold
(arXiv:2005.01869v2, p.5 and the display of §3.1, p.7):
`λ_{t+1}(i) = λ_t(i) − 1_{i∈sold}` for `i ∈ A_{t+1} ∩ A_t`, `λ_{t+1}(i) = c(i)` for
`i ∈ A_{t+1} \ A_t`, and `0` off `A_{t+1}`.

**Formalization Note.** The subtraction is in `ℕ`; along feasible play a sold resource has
`λ_t(i) ≥ 1` (its price would otherwise be `1`, and no user buys a bundle containing a resource
priced `1`), so the truncation is never reached there. -/
def step (I : Instance T C W) (t : ℕ) (inv : ℕ → ℕ) (sold : Finset ℕ) : ℕ → ℕ := by
  classical
  exact fun i =>
    if i ∈ I.active (t + 1) then
      (if i ∈ I.active t then inv i - (if i ∈ sold then 1 else 0) else I.cap i)
    else 0

/-- The inventory trajectory produced by a pricing rule: `rule t λ` is the price vector posted at
round `t` when the current inventory is `λ`. `traj … 1 = λ₁` and
`traj … (t+1) = step t (traj … t) (Â^{rule t (traj … t)}_t)`. Round `0` is unused. -/
noncomputable def traj (rank : Finset ℕ → ℕ) (I : Instance T C W)
    (rule : ℕ → (ℕ → ℕ) → (ℕ → ℝ)) : ℕ → (ℕ → ℕ)
  | 0 => I.initInv
  | 1 => I.initInv
  | t + 2 => I.step (t + 1) (traj rank I rule (t + 1))
      (I.demand rank (t + 1) (rule (t + 1) (traj rank I rule (t + 1))))

/-- The total payment `Σ_{t=1}^T q̂_t` collected by a pricing rule along its own trajectory. -/
noncomputable def ruleRevenue (rank : Finset ℕ → ℕ) (I : Instance T C W)
    (rule : ℕ → (ℕ → ℕ) → (ℕ → ℝ)) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, I.pay rank t (rule t (I.traj rank rule t))

end Instance

/-- A price vector `p` is feasible for the inventory vector `λ` on the active set `A`
(arXiv:2005.01869v2, p.5): prices lie in `(0,1]` and "p(i) = 1 for every i ∈ At such that
λt(i) = 0".

**Formalization Note.** Prices are functions `ℕ → ℝ`; only their values on the active set matter.
They are required to lie in `(0,1]` at every resource, not only on `A` (a price vector on `A` is
extended by `1` elsewhere; this changes no demand set, payment or inventory). -/
def Feasible (A : Finset ℕ) (inv : ℕ → ℕ) (p : ℕ → ℝ) : Prop :=
  (∀ i, 0 < p i ∧ p i ≤ 1) ∧ ∀ i ∈ A, inv i = 0 → p i = 1

/-- A pricing policy: it maps the active set `A_t` and an inventory vector `λ` on it to a price
vector (arXiv:2005.01869v2, p.5: "A (feasible) pricing policy γ is a function that maps each
inventory vector λ ∈ {0, 1, . . . , C}^At, t ∈ [T], to a price vector p = γ(λ)").

**Formalization Note.** The domain of the paper's inventory vector is `A_t`, so a policy may
depend on `A_t`; here `A_t` is an explicit argument. The time `t` is not an argument
(footnote 2, p.5). -/
abbrev Policy := Finset ℕ × (ℕ → ℕ) → (ℕ → ℝ)

/-- A policy is feasible if `γ(A, λ)` is feasible for `λ` on `A` for every `A` and `λ`
(arXiv:2005.01869v2, p.5). -/
def IsFeasiblePolicy (γ : Policy) : Prop :=
  ∀ A inv, Feasible A inv (γ (A, inv))

namespace Instance

variable {T C W : ℕ}

/-- The pricing rule of a policy: at round `t` it posts `γ(A_t, λ)`. -/
def policyRule (I : Instance T C W) (γ : Policy) : ℕ → (ℕ → ℕ) → (ℕ → ℝ) :=
  fun t inv => γ (I.active t, inv)

/-- The inventory vector `λ^γ_t` obtained by applying `γ` recursively from round `1`
(arXiv:2005.01869v2, p.5). -/
noncomputable def policyInv (rank : Finset ℕ → ℕ) (I : Instance T C W) (γ : Policy) :
    ℕ → (ℕ → ℕ) :=
  I.traj rank (I.policyRule γ)

/-- The price vector `p^γ_t = γ(λ^γ_t)` posted by `γ` at round `t` (arXiv:2005.01869v2, p.5). -/
noncomputable def policyPrice (rank : Finset ℕ → ℕ) (I : Instance T C W) (γ : Policy) (t : ℕ) :
    ℕ → ℝ :=
  γ (I.active t, I.policyInv rank γ t)

/-- The revenue `Σ_{t=1}^T q̂^γ_t` of the decision maker who repeatedly plays `γ`
(arXiv:2005.01869v2, p.5). -/
noncomputable def policyRevenue (rank : Finset ℕ → ℕ) (I : Instance T C W) (γ : Policy) : ℝ :=
  I.ruleRevenue rank (I.policyRule γ)

end Instance

end StatefulPricing


