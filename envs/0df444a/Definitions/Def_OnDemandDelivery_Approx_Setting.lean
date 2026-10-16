-- Prove2me | Definitions.Def_OnDemandDelivery_Approx_Setting
-- name    : OnDemandDelivery_Approx_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:05.964666+00:00
-- url     : https://prove2.me/theorems/5ae2c54a-49b3-4df7-b362-bc4830706f33
-- title:
--   §3–§4 — the dispatching and routing dynamic program JDR (1)–(9), the single-period cost ℋ^s, the approximation APT^n (10) and static myopic policies
-- statement:
--   This file sets up the joint dispatching and routing model **JDR** of Liu and Luo for on-demand delivery from a store, together with the approximation **APT** and the class of static myopic policies.
--
--   **Primitives.** A finite set $\mathcal I$ of potential customer locations and a depot $0$; $N$ periods $n = 1,\dots,N$ with strictly increasing decision epochs $t_1 < \dots < t_N$; a fleet of $\bar K$ drivers, each carrying at most $Q$ items per trip; an on-site service time $s \ge 0$; travel times $\tau(i,j) \ge 0$ between the depot and the locations; a delivery time target $L_{\max}$. In period $n$ the realized demand is a set $\mathcal I^n \subseteq \mathcal I$ of locations with an order and quantities $q^n_i \in \mathbb N$, drawn from a law $\mathbb Q^n$.
--
--   **Standing assumptions.** $N \ge 1$; the epochs are strictly increasing; each $\mathbb Q^n$ has finite support; on that support $q^n_i = 0$ for $i \notin \mathcal I^n$.
--
--   **Single-period decisions.** A decision $Y^n$ is a list of routes $0 \to i_1 \to \dots \to i_m \to 0$, one per dispatched driver. Along such a route the delivery times are
--   $$u_{i_1} = \tau(0,i_1), \qquad u_{i_{k+1}} = u_{i_k} + s + \tau(i_k, i_{k+1}),$$
--   and the route duration is $l = u_{i_m} + s + \tau(i_m, 0)$. The decision is feasible for demand $(\mathcal I^n, q^n)$ with $A$ available drivers if it has at most $A$ routes, every route is nonempty, every order of $\mathcal I^n$ lies on exactly one route and no other location is visited, every route carries at most $Q$ items, and every delivery time is at most $L_{\max}$. Its cost is $\sum_{i \in \mathcal I^n} u_i(Y^n)$.
--
--   **Single-period cost.** $\mathcal H^s(K, \mathcal I^n, q^n)$ is the minimum cost over decisions feasible with at most $K$ routes, and $+\infty$ when there is none.
--
--   **Dynamic program.** The driver status $\zeta^n = (\zeta^n_1, \dots, \zeta^n_N)$ counts, for each period $n'$, the drivers still en route in period $n'$. After decision $Y^n$ the status becomes, for $n' > n$,
--   $$\zeta^{n+1}_{n'} = \zeta^n_{n'} + \#\{\text{routes of } Y^n \text{ with duration } > t_{n'} - t_n\},$$
--   entries with $n' \le n$ being left unchanged. The cost-to-go is
--   $$\mathcal H_n(\mathcal I^n, q^n, \zeta^n) = \min_{Y^n} \Big\{ \sum_{i \in \mathcal I^n} u_i(Y^n) + \mathbb E_{\mathbb Q^{n+1}}\big[\mathcal H_{n+1}(\mathcal I^{n+1}, q^{n+1}, \zeta^{n+1})\big] \Big\} \quad (n < N),$$
--   and $\mathcal H_N$ is the minimum single-period cost alone, the minimum running over decisions feasible with $\bar K - \zeta^n_n$ available drivers ($+\infty$ if none). The expectations $\mathbb E_{\mathbb Q^n}[\mathcal H_n]$ and $\mathbb E_{\mathbb Q^n}[\mathcal H^s(K, \cdot)]$ are taken over the demand of period $n$.
--
--   **APT.** For parameters $\omega^{n'}_m(K) \ge 0$ ($n \le m < n'$), the problem $\mathbf{APT}^n(\zeta^n)$ is
--   $$V^n_{APT}(\zeta^n) = \min_{K^{n'} \in \mathbb N} \sum_{n'=n}^N \mathbb E_{\mathbb Q^{n'}}\big[\mathcal H^s(K^{n'}, \mathcal I^{n'}, q^{n'})\big] \quad \text{s.t.} \quad K^{n'} + \sum_{m=n}^{n'-1} \omega^{n'}_m(K^m) \le \bar K - \zeta^n_{n'}, \ n' = n, \dots, N,$$
--   with value $+\infty$ when no $K$ is feasible.
--
--   **Static myopic policies.** Such a policy dispatches a state-independent number $K^{n,sm}$ of drivers in period $n$ and routes them optimally for the single period: whenever $\mathcal H^s(K^{n,sm}, \mathcal I^n, q^n) < \infty$ its decision is feasible with at most $K^{n,sm}$ routes and costs exactly $\mathcal H^s(K^{n,sm}, \mathcal I^n, q^n)$. It is feasible for $\mathbf{JDR}^n(\zeta^n)$ if along every path reachable from $(n, \zeta^n)$ (demands in the supports of the $\mathbb Q^{n'}$) it has $K^{n',sm} \le \bar K - \zeta^{n'}_{n'}$ and a finite single-period cost. Its expected cost from $(n, \zeta^n)$ is the expected single-period cost of its decision plus, for $n < N$, its expected cost from the resulting state.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Locations are a type `L` and the depot is `none : Option L`; periods are indexed by `ℕ` with the paper's 1-based numbering, and the statements carry $1 \le n \le N$. Costs and values live in $[0, \infty]$ (`ℝ≥0∞`), expectations are sums against the probability mass function of $\mathbb Q^n$, and every minimum is an infimum equal to $+\infty$ on an empty feasible set. Periods are independent: (7) takes an unconditional expectation under $\mathbb Q^{n+1}$. Readings of the page: $\mathcal H^s$ allows *at most* $K$ routes (slip 1 of the moderation notes: "with $K$ dispatched drivers" is used in the proofs as "with $K$ available drivers"); every order must be served (stated on p. 8, missing from (1)–(6)); the delivery time is the (39) recursion with equality, started with the depot leg; travel times do not depend on the period; $\omega^{n'}_{n'}(K) = K$ is written into the constraint. The number of available drivers in the dynamic program is the truncated difference $\bar K - \zeta^n_n$ in $\mathbb N$; in APT the right-hand side is the real number $\bar K - \zeta^n_{n'}$.
-- source:
--   Liu, Luo, On-Demand Delivery from Stores: Dynamic Dispatching and Routing with Random Demand, arXiv:2107.13058v3, pp. 7–12 and 34, (1)–(10), Appendix C, static myopic policies p. 12

import Mathlib

open scoped ENNReal NNReal

namespace OnDemandDelivery.Approx

/-- The orders realized in one period: the set `I` of customer locations with an order (ℐⁿ) and the
order quantities `q` (qⁿ). -/
structure Demand (L : Type*) where
  I : Finset L
  q : L → ℕ

/-- A route is the list of customers `[i₁, …, iₘ]` visited in this order on a trip
`0 → i₁ → ⋯ → iₘ → 0` from the depot and back. -/
abbrev Route (L : Type*) := List L

/-- A single-period dispatching and routing decision Yⁿ: one route per dispatched driver. -/
abbrev Decision (L : Type*) := List (Route L)

/-- The primitives of the dispatching and routing model JDR (§3). Locations are `L`; the depot
(location 0) is `none : Option L`. -/
structure Model (L : Type*) where
  /-- number of periods N (periods are `1, …, N`) -/
  N : ℕ
  /-- fleet size K̄ -/
  Kbar : ℕ
  /-- capacity Q (items per trip) -/
  Q : ℕ
  /-- delivery time target L_max -/
  Lmax : ℝ≥0
  /-- on-site service time s -/
  s : ℝ≥0
  /-- travel times between depot (`none`) and customer locations -/
  τ : Option L → Option L → ℝ≥0
  /-- decision epochs tₙ -/
  t : ℕ → ℝ
  /-- the demand law ℚⁿ of period n -/
  law : ℕ → PMF (Demand L)

namespace Model

variable {L : Type*}

/-- Standing assumptions: at least one period, strictly increasing epochs, finitely supported demand
laws, and qⁿᵢ = 0 for i ∉ ℐⁿ on the support. -/
structure Standing (M : Model L) : Prop where
  one_le_N : 1 ≤ M.N
  t_strictMono : StrictMono M.t
  finite_support : ∀ n, (M.law n).support.Finite
  q_zero : ∀ n, ∀ d ∈ (M.law n).support, ∀ i, i ∉ d.I → d.q i = 0

/-- Delivery times along a route: leaving `prev` at time `clock`, the next customer `i` is served at
`clock + τ(prev, i)`, and the driver leaves it `s` later. Started at the depot at time 0 this gives
u_{i₁} = τ(0, i₁) and u_{i_{k+1}} = u_{i_k} + s + τ(i_k, i_{k+1}). -/
def deliveryTimes (M : Model L) : Option L → ℝ≥0 → Route L → List ℝ≥0
  | _, _, [] => []
  | prev, clock, i :: r =>
      (clock + M.τ prev (some i)) :: deliveryTimes M (some i) (clock + M.τ prev (some i) + M.s) r

/-- Time at which a driver leaving `prev` at time `clock` is back at the depot after serving the
remaining customers `r`. -/
def returnTime (M : Model L) : Option L → ℝ≥0 → Route L → ℝ≥0
  | prev, clock, [] => clock + M.τ prev none
  | prev, clock, i :: r => returnTime M (some i) (clock + M.τ prev (some i) + M.s) r

/-- The route duration lₖ: travel time of all legs including the return to the depot, plus the
service time at every customer. -/
def routeDuration (M : Model L) (r : Route L) : ℝ≥0 := M.returnTime none 0 r

/-- Total delivery time Σ_{i on r} uᵢ of a route. -/
def routeCost (M : Model L) (r : Route L) : ℝ≥0 := (M.deliveryTimes none 0 r).sum

/-- Single-period cost Σ_{i∈ℐⁿ} uᵢ(Yⁿ) of a decision. -/
def cost (M : Model L) (Y : Decision L) : ℝ≥0 := (Y.map M.routeCost).sum

/-- Single-period feasibility ((1)–(6), with the assignment of every order): at most `A` routes
(only the available drivers are dispatched), every route nonempty, every order of `d` on exactly one
route and no other customer visited, load at most `Q` on every route, every delivery time at most
`L_max`. -/
def SingleFeasible (M : Model L) (A : ℕ) (d : Demand L) (Y : Decision L) : Prop :=
  Y.length ≤ A ∧
  (∀ r ∈ Y, r ≠ []) ∧
  Y.flatten.Nodup ∧
  (∀ i, i ∈ Y.flatten ↔ i ∈ d.I) ∧
  (∀ r ∈ Y, (r.map d.q).sum ≤ M.Q) ∧
  (∀ r ∈ Y, ∀ u ∈ M.deliveryTimes none 0 r, u ≤ M.Lmax)

/-- ℋˢ(K, ℐ, q): the single-period optimal delivery cost with `K` available drivers, i.e. the
minimum cost over feasible decisions using at most `K` routes (`⊤` if none is feasible). -/
noncomputable def Hs (M : Model L) (K : ℕ) (d : Demand L) : ℝ≥0∞ :=
  ⨅ (Y : Decision L) (_ : M.SingleFeasible K d Y), (M.cost Y : ℝ≥0∞)

/-- Transition (9): after decision `Y` in period `n`, for every later period `n' > n` the drivers
whose route lasts strictly longer than `t_{n'} − t_n` are added to the en route count; entries for
`n' ≤ n` are left unchanged. -/
noncomputable def next (M : Model L) (n : ℕ) (ζ : ℕ → ℕ) (Y : Decision L) : ℕ → ℕ :=
  fun n' =>
    if n < n' then
      ζ n' + Y.countP (fun r => decide (M.t n' - M.t n < (M.routeDuration r : ℝ)))
    else ζ n'

/-- The cost-to-go ℋₙ(ℐⁿ, qⁿ, ζⁿ) of JDR ((7)–(8)): in period `n` with demand `d` and driver status
`ζ`, minimize over decisions feasible with `K̄ − ζₙ` available drivers the single-period cost plus,
if `n < N`, the expected cost-to-go of period `n + 1` under ℚⁿ⁺¹. -/
noncomputable def H (M : Model L) (n : ℕ) (d : Demand L) (ζ : ℕ → ℕ) : ℝ≥0∞ :=
  if _h : n < M.N then
    ⨅ (Y : Decision L) (_ : M.SingleFeasible (M.Kbar - ζ n) d Y),
      ((M.cost Y : ℝ≥0∞) + ∑' d' : Demand L, M.law (n + 1) d' * M.H (n + 1) d' (M.next n ζ Y))
  else
    ⨅ (Y : Decision L) (_ : M.SingleFeasible (M.Kbar - ζ n) d Y), (M.cost Y : ℝ≥0∞)
termination_by M.N - n
decreasing_by omega

/-- The expected cost-to-go 𝔼_{ℚⁿ}[ℋₙ(ℐⁿ, qⁿ, ζⁿ)]. -/
noncomputable def EH (M : Model L) (n : ℕ) (ζ : ℕ → ℕ) : ℝ≥0∞ :=
  ∑' d : Demand L, M.law n d * M.H n d ζ

/-- The expected single-period optimal cost 𝔼_{ℚⁿ}[ℋˢ(K, ℐⁿ, qⁿ)]. -/
noncomputable def EHs (M : Model L) (n : ℕ) (K : ℕ) : ℝ≥0∞ :=
  ∑' d : Demand L, M.law n d * M.Hs K d

/-- Feasibility for APTⁿ(ζⁿ) (10): `ω n' m k` is ω^{n'}_m(k) ≥ 0 for `n ≤ m < n'`; the diagonal term
ω^{n'}_{n'}(K^{n'}) = K^{n'} is written out. -/
def AptFeasible (M : Model L) (n : ℕ) (ζ : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → ℝ≥0) (K : ℕ → ℕ) : Prop :=
  ∀ n' ∈ Finset.Icc n M.N,
    (K n' : ℝ) + ∑ m ∈ Finset.Ico n n', (ω n' m (K m) : ℝ) ≤ (M.Kbar : ℝ) - (ζ n' : ℝ)

/-- V^n_{APT}(ζⁿ): the optimal value of APTⁿ(ζⁿ) for the parameters `ω` (`⊤` if infeasible). -/
noncomputable def Vapt (M : Model L) (n : ℕ) (ζ : ℕ → ℕ) (ω : ℕ → ℕ → ℕ → ℝ≥0) : ℝ≥0∞ :=
  ⨅ (K : ℕ → ℕ) (_ : M.AptFeasible n ζ ω K), ∑ n' ∈ Finset.Icc n M.N, M.EHs n' (K n')

/-- A static myopic policy: a state-independent number `K n` of drivers to dispatch in period `n`
and a routing rule `sel` that, whenever the single-period problem with `K n` drivers is feasible,
returns an optimal decision of it. -/
structure StaticMyopic (M : Model L) where
  K : ℕ → ℕ
  sel : ℕ → Demand L → Decision L
  myopic : ∀ n d, M.Hs (K n) d < ⊤ →
    M.SingleFeasible (K n) d (sel n d) ∧ (M.cost (sel n d) : ℝ≥0∞) = M.Hs (K n) d

/-- A static myopic policy is feasible for JDRⁿ(ζⁿ) if along every path reachable from period `n`
with status `ζ` (demand in the support of each ℚ^{n'}) its count fits into the available drivers,
`K n' ≤ K̄ − ζ^{n'}_{n'}`, and its single-period problem is feasible. -/
def StaticMyopic.Feasible {M : Model L} (π : M.StaticMyopic) (n : ℕ) (ζ : ℕ → ℕ) : Prop :=
  if h : n < M.N then
    ∀ d ∈ (M.law n).support, π.K n + ζ n ≤ M.Kbar ∧ M.Hs (π.K n) d < ⊤ ∧
      π.Feasible (n + 1) (M.next n ζ (π.sel n d))
  else
    ∀ d ∈ (M.law n).support, π.K n + ζ n ≤ M.Kbar ∧ M.Hs (π.K n) d < ⊤
termination_by M.N - n
decreasing_by omega

/-- The expected cost of following the policy from period `n` with status `ζ` to the end of the
horizon: the expected single-period cost of its decision plus, if `n < N`, the expected cost from
the resulting state. -/
noncomputable def StaticMyopic.cost {M : Model L} (π : M.StaticMyopic) (n : ℕ) (ζ : ℕ → ℕ) : ℝ≥0∞ :=
  if _h : n < M.N then
    ∑' d : Demand L, M.law n d *
      ((M.cost (π.sel n d) : ℝ≥0∞) + π.cost (n + 1) (M.next n ζ (π.sel n d)))
  else
    ∑' d : Demand L, M.law n d * (M.cost (π.sel n d) : ℝ≥0∞)
termination_by M.N - n
decreasing_by omega

end Model

end OnDemandDelivery.Approx


