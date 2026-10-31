-- Prove2me | Definitions.Def_MinBuying_CanonicalAlgebra
-- name    : MinBuying_CanonicalAlgebra
-- status  : Definition
-- author  : @mikeh
-- created : 2026-10-30T16:14:36.766033+00:00
-- url     : https://prove2.me/theorems/14ed2cf8-b9c1-4ff2-be96-2eb08e2cdd72
-- title:
--   Canonical triangular parameters and continuation formulas
-- statement:
--   A canonical parameter system has a terminal cap $P>1$ and $N\ge0$ additional caps $P>v_1>\cdots>v_N>1$ with positive parameters $a_i$. Defines strict rejection for triangular laws, the continuation update $(a+C)/(1+a/v)$, its finite iteration from $P/(P+1)$, and the product formula for uniform revenue at every nonnegative price. Exact normalization means all such revenues are at most one and one price attains one.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . Section 4.2.2 pp.19–22, Eqs.(13)–(14).

import Definitions.Def_MinBuying_Analytic

open Set
open scoped BigOperators

noncomputable section

namespace MinBuying

/-- Canonical triangular parameters from Section 4.2.2. Item zero is the
terminal `Tri(1,P)` item; the `count` additional caps decrease with the index.
The empty collection of additional items is explicitly allowed. -/
structure CanonicalInstance where
  count : ℕ
  terminalCap : ℝ
  a : Fin count → ℝ
  cap : Fin count → ℝ
  terminal_one_lt : 1 < terminalCap
  a_pos : ∀ i, 0 < a i
  cap_one_lt : ∀ i, 1 < cap i
  cap_lt_terminal : ∀ i, cap i < terminalCap
  caps_decreasing : StrictAnti cap

/-- Probability of strict rejection `V < p` for `V ~ Tri(a,v)`.
In particular, at the cap `p=v`, the atom is accepted and the rejection
probability is `v/(v+a)`, not one. Used for positive `a` and `v`. -/
def triangularReject (a v p : ℝ) : ℝ :=
  if p ≤ 0 then 0 else if p ≤ v then p / (p + a) else 1

/-- Equation (13), adding a cheaper cap-priced triangular item. -/
def continuationStep (a v C : ℝ) : ℝ :=
  (a + C) / (1 + a / v)

/-- Continuation revenue after adding the first `k` additional items in
strictly decreasing cap order. For `k=0`, this is `P/(P+1)`. Statements about
an intermediate stage restrict `k ≤ count`; the final stage is `count`. -/
def canonicalContinuation (I : CanonicalInstance) (k : ℕ) : ℝ :=
  ((List.finRange I.count).take k).foldl
    (fun C i => continuationStep (I.a i) (I.cap i) C)
    (I.terminalCap / (I.terminalCap + 1))

/-- The final scalar continuation value of the designated cap pricing. -/
def canonicalCapRevenue (I : CanonicalInstance) : ℝ :=
  canonicalContinuation I I.count

/-- Actual common-price revenue, including all price regimes and cap atoms.
The nonnegative feasible-price restriction is in the revenue statements. -/
def canonicalUniformRevenueAt (I : CanonicalInstance) (p : ℝ) : ℝ :=
  p * (1 - triangularReject 1 I.terminalCap p *
    ∏ i : Fin I.count, triangularReject (I.a i) (I.cap i) p)

/-- Exact normalization: all feasible common prices earn at most one, and
some feasible common price attains one. -/
def CanonicalNormalized (I : CanonicalInstance) : Prop :=
  (∀ p : ℝ, 0 ≤ p → canonicalUniformRevenueAt I p ≤ 1) ∧
    ∃ p : ℝ, 0 ≤ p ∧ canonicalUniformRevenueAt I p = 1

end MinBuying


