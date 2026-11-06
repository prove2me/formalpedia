-- Prove2me | Definitions.Def_IntervalToDynamic_greedyEnd
-- name    : IntervalToDynamic_greedyEnd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:10.970506+00:00
-- url     : https://prove2.me/theorems/06735f53-ac42-45cf-bbfd-9afe2cc8e4fe
-- title:
--   The right end of a greedy interval
-- statement:
--   Starting a greedy interval at $a$, let $t$ be the first point of $(a,T]$ with $P_{[a,t]}>B/(t-a+1)^\varepsilon$. The interval closes immediately before $t$, at $t-1$. If there is no such $t$, it closes at $T$.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Lemma 11 and its proof, p.29

import Mathlib
import Definitions.Def_IntervalToDynamic_pathLengthOn

namespace IntervalToDynamic

open Classical in
/-- The right end of the greedy interval started at `a`. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, proof of Lemma 11, p.29: "close the
current interval immediately before the first `t` for which `P_{[a,t]} > B/(t − a + 1)^ε`". If no
such `t ∈ (a, T]` exists the interval runs to `T`. -/
noncomputable def greedyEnd {E : Type*} [NormedAddCommGroup E] (B ε : ℝ) (u : ℕ → E) (T a : ℕ) : ℕ :=
  if h : ∃ t, a < t ∧ t ≤ T ∧ B / ((t - a + 1 : ℕ) : ℝ) ^ ε < pathLengthOn u a t then
    Nat.find h - 1
  else T

end IntervalToDynamic


