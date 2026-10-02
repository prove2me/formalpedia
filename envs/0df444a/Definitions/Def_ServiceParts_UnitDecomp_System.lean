-- Prove2me | Definitions.Def_ServiceParts_UnitDecomp_System
-- name    : ServiceParts_UnitDecomp_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T21:41:54.176985+00:00
-- url     : https://prove2.me/theorems/2fd756c9-7889-4f00-9bd0-6eb39f858ca0
-- title:
--   The whole unit-customer system $\mathcal S$: states, dynamics, policies, monotone and committed policies, base-stock releases
-- statement:
--   Fix a model and a horizon of $N$ periods. The **system** $\mathcal S$ contains countably many units and countably many customers, both indexed $0, 1, 2, \dots$ (index $j$ here is the book's index $j+1$). Its configuration at the beginning of a period records the location $z_j \in \{0,\dots,m+1\}$ of every unit and the distance $y_j$ of every customer; with the Markov state it is the book's state $x_n = (s_n,(z_{1n},y_{1n}),(z_{2n},y_{2n}),\dots)$.
--
--   In period $n$ a policy releases a finite set $R$ of units. Then every unit moves as in event 2 (released iff it is in $R$ and at the supplier), every customer moves as in event 3, and the units on hand and the waiting customers are matched as far as possible, the lowest-indexed units on hand serving the lowest-indexed waiting customers (event 4); matched units go to location $0$ and matched customers to distance $0$. The cost of the period is
--   $$h \cdot \#\{j : z_j = 1\} + b\cdot \#\{j : y_j = 1\}$$
--   after matching (event 5). A **policy** for $\mathcal S$ maps $(n, s_n, \text{configuration})$ to a finite set of units to release; $C^\pi_n$ is its expected discounted cost in periods $n,\dots,N$ and $V^{\mathcal S}_n = \inf_\pi C^\pi_n$ the optimal cost.
--
--   A **starting configuration** in period 1 is built as on pp. 23–24 from $v_0$ waiting customers and $a_\ell$ units at each location $\ell = 1,\dots,m$: units are indexed serially by location, all remaining units are at the supplier, customers $0,\dots,v_0-1$ are waiting and customer $v_0+k$ is at distance $k+2$.
--
--   A policy is **monotone** if, whenever it releases a unit at the supplier, it also releases every lower-indexed unit at the supplier. It is **committed** if, from every starting configuration and along every realisation of the Markov chain and of the demands, unit $j$ is used exactly when customer $j$ is served. The **inventory position** of a configuration is the number of units at locations $1,\dots,m$ minus the number of waiting customers, and the **order-up-to release** with level $L$ releases the $L - \mathrm{IP}$ lowest-indexed units at the supplier (none if $L \le \mathrm{IP}$).
--
--   These objects carry Lemma 1, Theorem 4 and Theorem 5.
--
--   **Formalization Note** Counts in the cost are taken in $\mathbb N\cup\{\infty\}$, so a configuration with infinitely many units on hand costs $\infty$ rather than a junk value. The inventory position uses finite cardinalities, which are exact on every configuration reachable from a starting configuration (finitely many units off the supplier, finitely many waiting customers). "Any starting state $x_1$" in Theorem 4 is read as the starting configurations built on pp. 23–24: units indexed from location 1 upward and customers from the waiting ones upward; for arbitrarily labelled states Theorem 4 is false.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 23-27, Section 2.2.1.1 (indexing, state x_n, events 1-5, policy, monotone and committed policies), Definitions 1-2 (p. 26)

import Mathlib
import Definitions.Def_ServiceParts_UnitDecomp_Model

open scoped ENNReal NNReal

namespace ServiceParts.UnitDecomp

variable {σ : Type} [Fintype σ]

/-- The physical part of the state `xₙ = (sₙ, (z₁ₙ, y₁ₙ), (z₂ₙ, y₂ₙ), …)` of the whole system
`S` (p. 24): `loc j` is the location `z_{jn}` of unit `j` and `dist j` the distance `y_{jn}` of
customer `j`. Units and customers are indexed by `ℕ` from `0`: index `j` here is the book's
index `j + 1`. -/
structure SysState where
  /-- location of each unit -/
  loc : ℕ → ℕ
  /-- distance of each customer -/
  dist : ℕ → ℕ

/-- The number of indices `i < j` satisfying `p` (the rank of `j` among the indices
satisfying `p`). -/
def rankIn (p : ℕ → Prop) [DecidablePred p] (j : ℕ) : ℕ :=
  ((Finset.range j).filter p).card

open Classical in
/-- Events 2–4 of a period in the whole system `S` (pp. 24–25) when the units in `R` are
released and the demand is `d`: every unit moves by `unitMove` (released iff it is in `R`
and at the supplier), every customer by `custMove`; then the units on hand and the waiting
customers are matched as far as possible, the lowest-indexed units on hand serving the
lowest-indexed waiting customers (p. 25). Matched units go to location `0` and matched
customers to distance `0`. -/
noncomputable def Model.sysPost (M : Model σ) (x : SysState) (R : Set ℕ) (d : ℕ) : SysState :=
  let z : ℕ → ℕ := fun j => unitMove M.m (x.loc j) (decide (j ∈ R))
  let y : ℕ → ℕ := fun j => custMove d (x.dist j)
  { loc := fun j =>
      if z j = 1 ∧ ((rankIn (fun i => z i = 1) j : ℕ) : ℕ∞) < {i | y i = 1}.encard then 0
      else z j
    dist := fun j =>
      if y j = 1 ∧ ((rankIn (fun i => y i = 1) j : ℕ) : ℕ∞) < {i | z i = 1}.encard then 0
      else y j }

/-- Event 5 in `S`: `h` per unit on hand plus `b` per waiting customer at the end of the
period (numbers of units and customers counted in `ℕ∞`, so an infinite count costs `∞`). -/
noncomputable def Model.sysStage (M : Model σ) (x : SysState) : ℝ≥0∞ :=
  (M.h : ℝ≥0∞) * ENat.toENNReal {j | x.loc j = 1}.encard +
    (M.b : ℝ≥0∞) * ENat.toENNReal {j | x.dist j = 1}.encard

/-- A policy for `S` (p. 25): in each period, from the Markov state and the configuration, the
set of units released from the supplier; only finitely many units are released in a period
(the order quantity `qₙ` is a nonnegative integer). Units of the set that are not at the
supplier are unaffected. -/
structure SPolicy (σ : Type) where
  /-- the units released in period `n` from Markov state `s` and configuration `x` -/
  act : ℕ → σ → SysState → Set ℕ
  finite : ∀ n s x, (act n s x).Finite

/-- Expected discounted cost of the policy `π` for `S` in periods `n, …, N`. -/
noncomputable def Model.sysCost (M : Model σ) (N : ℕ) (π : SPolicy σ) (n : ℕ) (s : σ)
    (x : SysState) : ℝ≥0∞ :=
  M.costToGo M.sysPost M.sysStage π.act (N + 1 - n) n s x

/-- Optimal expected discounted cost of `S` in periods `n, …, N`: the infimum of `sysCost`
over all policies for `S`. -/
noncomputable def Model.sysOpt (M : Model σ) (N n : ℕ) (s : σ) (x : SysState) : ℝ≥0∞ :=
  ⨅ π : SPolicy σ, M.sysCost N π n s x

/-- A starting configuration of `S` in period 1 (p. 23–24): `v₀` customers are waiting and
`a ℓ` units are at location `ℓ` for `ℓ = 1, …, m` (the values `a ℓ` for other `ℓ` are not
used); all other units are at the supplier. Units are indexed serially by location (location 1
first), customers `0, …, v₀ − 1` are the waiting ones and customer `v₀ + k` is at distance
`k + 2`. -/
def Model.initState (M : Model σ) (a : ℕ → ℕ) (v₀ : ℕ) : SysState where
  loc j := 1 + ((Finset.Icc 1 M.m).filter (fun ℓ => ∑ i ∈ Finset.Icc 1 ℓ, a i ≤ j)).card
  dist j := if j < v₀ then 1 else j - v₀ + 2

/-- A monotone policy (p. 25): whenever it releases a unit from the supplier, it also releases
every lower-indexed unit at the supplier. -/
def Model.IsMonotone (M : Model σ) (π : SPolicy σ) : Prop :=
  ∀ n s x j k, j ∈ π.act n s x → x.loc j = M.m + 1 → x.loc k = M.m + 1 → k < j →
    k ∈ π.act n s x

/-- The configuration of `S` at the beginning of period `k + 1` under policy `π` from `x₁`,
along a realisation `s` of the Markov chain and `D` of the demands (`s n`, `D n` are those of
period `n`). -/
noncomputable def Model.trajectory (M : Model σ) (π : SPolicy σ) (x₁ : SysState) (s : ℕ → σ)
    (D : ℕ → ℕ) : ℕ → SysState
  | 0 => x₁
  | k + 1 =>
      let x := Model.trajectory M π x₁ s D k
      M.sysPost x (π.act (k + 1) (s (k + 1)) x) (D (k + 1))

/-- A committed policy (p. 25): from every starting configuration and along every realisation,
unit `j` is used exactly when customer `j` is served, i.e. unit `j` only ever serves
customer `j`. -/
def Model.IsCommitted (M : Model σ) (π : SPolicy σ) : Prop :=
  ∀ (a : ℕ → ℕ) (v₀ : ℕ) (s : ℕ → σ) (D : ℕ → ℕ) (k j : ℕ),
    (M.trajectory π (M.initState a v₀) s D k).loc j = 0 ↔
      (M.trajectory π (M.initState a v₀) s D k).dist j = 0

/-- The inventory position of a configuration: units on hand or in transit (locations
`1, …, m`) minus waiting customers. Counts use `Set.ncard`; every configuration reached from
`initState` has finitely many of both. -/
noncomputable def Model.inventoryPosition (M : Model σ) (x : SysState) : ℤ :=
  ({j | 1 ≤ x.loc j ∧ x.loc j ≤ M.m}.ncard : ℤ) - ({j | x.dist j = 1}.ncard : ℤ)

/-- The units released by an order-up-to decision with level `L`: the `L − IP` lowest-indexed
units at the supplier (none if `L ≤ IP`), where `IP` is the inventory position. -/
def Model.baseStockRelease (M : Model σ) (L : ℤ) (x : SysState) : Set ℕ :=
  {j | x.loc j = M.m + 1 ∧
    ((rankIn (fun i => x.loc i = M.m + 1) j : ℕ) : ℤ) < L - M.inventoryPosition x}

end ServiceParts.UnitDecomp


