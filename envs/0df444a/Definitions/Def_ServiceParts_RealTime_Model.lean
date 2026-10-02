-- Prove2me | Definitions.Def_ServiceParts_RealTime_Model
-- name    : ServiceParts_RealTime_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T23:48:00.019106+00:00
-- url     : https://prove2.me/theorems/97218c15-717a-4f8f-a03d-434bca4d5d51
-- title:
--   Item data of the stock allocation models: lead times, known cumulative supplies, costs, cumulative demand; G, Q, CN
-- statement:
--   Fix one item $i$ of a two-echelon service parts system in which a depot warehouse supplies a finite set $J$ of bases. The index $i$ is suppressed below. Time is measured in whole periods $t = 0, 1, 2, \dots$, and the demands are random variables on a probability space $(\Omega, P)$.
--
--   The data of the item are:
--
--   1. the repair lead time $T_{i0}$, and for each base $j$ the regular and expedited transportation lead times $T^r_{ij}$, $T^e_{ij}$ from the depot warehouse, integers with $1 \le T^e_{ij} < T^r_{ij}$;
--   2. the known cumulative supply $\tilde S_{i0t}$ at the depot warehouse through period $t$ (stock on hand at the start of the horizon plus arrivals through $t$), nonnegative and nondecreasing in $t$;
--   3. the known cumulative supply $\tilde S_{ijt}$ at base $j$ through period $t$ (net inventory, possibly negative, plus arrivals), an integer nondecreasing in $t$ with $\tilde S_{ijt} = \tilde S_{ij(T^r_{ij}-1)}$ for $t \ge T^r_{ij}$;
--   4. an incremental holding cost $h_{ij} > 0$, a unit shortage cost $b_{ij} > 0$ and an incremental expedited-shipment cost $e_{ij} \ge 0$ per base;
--   5. the cumulative demand $X_{ijt}$ at base $j$ through period $t$, a nonnegative integer-valued random variable with finite mean, nondecreasing in $t$ for every outcome.
--
--   From these, the single-period expected holding and backorder cost at base $j$ in period $t$ is
--   $$G_{ijt}(S) = h_{ij}\, E[S - X_{ijt}]^+ + b_{ij}\, E[X_{ijt} - S]^+, \qquad S \in \mathbb Z,$$
--   and the expected end-of-horizon holding cost is
--   $$Q_{ij}(S) = h_{ij} \sum_{t = T^r_{ij} + T_{i0} + 1}^{\infty} E[S - X_{ijt}]^+ ,$$
--   whose series is assumed to converge for every $S$. The distribution function of the cumulative demand is $F_{X_{ijt}}(s) = P(X_{ijt} \le s)$.
--
--   The constrained newsvendor problem $\mathrm{CN}_{ijt}$ is: minimize $G_{ijt}(S)$ over integers $S \ge \tilde S_{ijt}$. An integer $\hat S$ is its largest optimal solution when it is feasible, minimizes $G_{ijt}$ over the feasible integers, and every feasible minimizer is at most $\hat S$. Finally, a function $f$ on the integers is discretely convex when $f(S+1) - f(S) \le f(S+2) - f(S+1)$ for all $S$.
--
--   These are the objects of Sections 10.2 and 10.4 of the book, on which the allocation models SAM and ESAM are built.
--
--   **Formalization Note** The model is the structure `ItemModel J Ω P`, one per item. The demand $X_{ijt}$ is given for every $t \in \mathbb N$ because $Q_{ij}$ uses periods beyond the horizon. Positivity of $h$ and $b$, nonnegativity of $e$, finite means and convergence of the series in $Q$ are not written in the book; they are the conditions under which its costs are finite real numbers and "the largest optimal solution" exists.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 232-234 and 237, Section 10.2 (time, supply and demand parameters, G_ijt, Q_ij (10.1)) and Section 10.4.2 (CN_ijt (10.18))

import Mathlib

open MeasureTheory

namespace ServiceParts.RealTime

/-- The data of one item `i` in the stock allocation models of Muckstadt (2005), §10.2,
pp. 231–234, for a set `J` of bases, with the random cumulative demands defined on a
probability space `(Ω, P)`. All times are integer numbers of periods. The index `i` of the
book is suppressed: every field is the book's quantity for the fixed item `i`.

* `T0` is the repair lead time `T_{i0}`; `Tr j` and `Te j` are the regular and expedited
  transportation lead times `T^r_{ij}`, `T^e_{ij}`, with `1 ≤ T^e_{ij} < T^r_{ij}` (p. 232).
* `depotSupply t` is the known cumulative supply `S̃_{i0t}` at the depot warehouse through
  period `t` (used for `t = 0, …, T_{i0}`); it is on-hand stock plus arrivals, hence
  nonnegative and nondecreasing.
* `baseSupply j t` is the known cumulative supply `S̃_{ijt}` at base `j` through period `t`
  (net inventory, possibly negative, plus arrivals), nondecreasing in `t` (p. 244), with
  `S̃_{ijt} = S̃_{ij(T^r_{ij}-1)}` for `t ≥ T^r_{ij}` (p. 232).
* `h j`, `b j`, `e j` are the incremental holding cost, the unit shortage cost and the
  incremental expedited-shipment cost (p. 233).
* `X j t` is the cumulative demand `X_{ijt}` of the item at base `j` through period `t`:
  a nonnegative integer random variable, nondecreasing in `t`, with finite mean.
* `Q_summable` says that the series defining the end-of-horizon cost `Q_{ij}` (10.1)
  converges at every stock level. -/
structure ItemModel (J : Type*) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  T0 : ℕ
  Tr : J → ℕ
  Te : J → ℕ
  one_le_Te : ∀ j, 1 ≤ Te j
  Te_lt_Tr : ∀ j, Te j < Tr j
  depotSupply : ℕ → ℤ
  depotSupply_nonneg : 0 ≤ depotSupply 0
  depotSupply_mono : Monotone depotSupply
  baseSupply : J → ℕ → ℤ
  baseSupply_mono : ∀ j, Monotone (baseSupply j)
  baseSupply_const : ∀ j t, Tr j ≤ t → baseSupply j t = baseSupply j (Tr j - 1)
  h : J → ℝ
  b : J → ℝ
  e : J → ℝ
  h_pos : ∀ j, 0 < h j
  b_pos : ∀ j, 0 < b j
  e_nonneg : ∀ j, 0 ≤ e j
  X : J → ℕ → Ω → ℕ
  X_measurable : ∀ j t, Measurable (X j t)
  X_mono : ∀ j ω, Monotone (fun t => X j t ω)
  X_integrable : ∀ j t, Integrable (fun ω => (X j t ω : ℝ)) P
  Q_summable : ∀ j (S : ℤ), Summable (fun n : ℕ =>
    ∫ ω, max ((S : ℝ) - (X j (Tr j + T0 + 1 + n) ω : ℝ)) 0 ∂P)

namespace ItemModel

variable {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The single-period expected holding and backorder cost at base `j` in period `t`,
`G_{ijt}(S) = h_{ij} E[S - X_{ijt}]^+ + b_{ij} E[X_{ijt} - S]^+` (p. 233). -/
noncomputable def G (M : ItemModel J Ω P) (j : J) (t : ℕ) (S : ℤ) : ℝ :=
  M.h j * ∫ ω, max ((S : ℝ) - (M.X j t ω : ℝ)) 0 ∂P
    + M.b j * ∫ ω, max ((M.X j t ω : ℝ) - (S : ℝ)) 0 ∂P

/-- The end-of-horizon expected holding cost at base `j`,
`Q_{ij}(S) = h_{ij} Σ_{t = T^r_{ij} + T_{i0} + 1}^{∞} E[S - X_{ijt}]^+` (10.1), p. 234;
the summation index `n` corresponds to `t = T^r_{ij} + T_{i0} + 1 + n`. -/
noncomputable def Q (M : ItemModel J Ω P) (j : J) (S : ℤ) : ℝ :=
  M.h j * ∑' n : ℕ, ∫ ω, max ((S : ℝ) - (M.X j (M.Tr j + M.T0 + 1 + n) ω : ℝ)) 0 ∂P

/-- The distribution function `F_{X_{ijt}}(s) = P(X_{ijt} ≤ s)` of the cumulative demand,
evaluated at an integer `s` (p. 237). -/
noncomputable def demandCDF (M : ItemModel J Ω P) (j : J) (t : ℕ) (s : ℤ) : ℝ :=
  (P {ω | ((M.X j t ω : ℕ) : ℤ) ≤ s}).toReal

/-- `s` is the largest optimal solution `Ŝ_{ijt}` of the constrained newsvendor problem
`CN_{ijt}` (10.18), p. 237: minimize `G_{ijt}(S)` subject to `S ≥ S̃_{ijt}`, `S` integer.
That is, `s` is feasible, minimizes `G_{ijt}` over the feasible set, and every feasible
minimizer is at most `s`. -/
def IsLargestCNSolution (M : ItemModel J Ω P) (j : J) (t : ℕ) (s : ℤ) : Prop :=
  M.baseSupply j t ≤ s ∧
    (∀ S : ℤ, M.baseSupply j t ≤ S → M.G j t s ≤ M.G j t S) ∧
    ∀ S : ℤ, M.baseSupply j t ≤ S → M.G j t S ≤ M.G j t s → S ≤ s

end ItemModel

/-- Discrete convexity of a function on the integers: nondecreasing first differences,
`f(S+1) - f(S) ≤ f(S+2) - f(S+1)` for every integer `S`. -/
def DiscreteConvex (f : ℤ → ℝ) : Prop :=
  ∀ S : ℤ, f (S + 1) - f S ≤ f (S + 2) - f (S + 1)

end ServiceParts.RealTime


