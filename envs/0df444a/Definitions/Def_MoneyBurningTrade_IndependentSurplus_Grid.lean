-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_Grid
-- name    : MoneyBurningTrade_IndependentSurplus_Grid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:18.828082+00:00
-- url     : https://prove2.me/theorems/8b504400-e7f1-442c-94d3-af171dc9f6be
-- title:
--   Normalized finite grid and condition (19)
-- statement:
--   A grid has a length $n$ and points $q_0,\ldots,q_n$. Its normalization predicate is
--
--   $$n\ge2,\qquad0=q_0<q_1<\cdots<q_n=1.$$
--
--   Its smallest gap is $L=\min_{1\le i\le n}(q_i-q_{i-1})$. The separate grid-condition predicate is exactly $q_{j-1}-q_i\le4\delta(q_j-q_{i-1})$ for $1\le i<j\le n$. These definitions describe only grid data. They carry no incentive or performance claims. Points use the source's natural indices; values outside $0,\ldots,n$ are unused.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 4.3 and Definition 4.4, printed p. 23–25 (PDF p. 24–26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- A grid's input data, with the source's zero-based endpoints 0,...,n.
Entries outside this range are unused in all statements. -/
structure Grid where
  n : ℕ
  q : ℕ → ℝ

/-- The grid hypotheses of Lemma 4.3. No mechanism property is bundled here. -/
def IsGrid (G : Grid) : Prop :=
  2 ≤ G.n ∧ G.q 0 = 0 ∧ G.q G.n = 1 ∧
  ∀ i j : ℕ, i < j → j ≤ G.n → G.q i < G.q j

/-- Minimum of the n consecutive gaps. For IsGrid, this is a nonempty finite
set of positive reals; outside that domain an empty set has Lean's default infimum 0. -/
noncomputable def minGap (G : Grid) : ℝ :=
  sInf {d : ℝ | ∃ i : ℕ, 1 ≤ i ∧ i ≤ G.n ∧ d = G.q i - G.q (i - 1)}

/-- Equation (19), with its constant 4 and its full pair-index range. -/
def gridCondition (G : Grid) (δ : ℝ) : Prop :=
  ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ G.n →
    G.q (j - 1) - G.q i ≤ 4 * δ * (G.q j - G.q (i - 1))

end MoneyBurningTrade.IndependentSurplus


