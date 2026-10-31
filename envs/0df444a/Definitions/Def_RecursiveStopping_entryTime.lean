-- Prove2me | Definitions.Def_RecursiveStopping_entryTime
-- name    : RecursiveStopping_entryTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:59.662004+00:00
-- url     : https://prove2.me/theorems/3b700562-d575-4fc6-a811-bc69bc4e2479
-- title:
--   First entry time of the flow into a set, before a bound
-- statement:
--   For a flow $X$, a starting point $x$, a set $A\subseteq S$ and a bound $b\in[0,\infty]$, the **first entry time** is
--
--   $$
--   \tau_A(\omega):=\inf\{s\ge0:\ s\le b,\ X^x_s(\omega)\in A\},\qquad\inf\emptyset=\infty .
--   $$
--
--   With $b=\infty$ this is the time $\inf\{s\ge0: X_s\in A\}$ of (16) and (17); with $b=T-t$ it is the finite-horizon version, where the infimum is taken over $s\in[0,T-t]$ (p.11).
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, (16), p.10; (17) and the remark on T < ∞, p.11

import Mathlib

open scoped NNReal ENNReal

namespace RecursiveStopping

/-- The first entry time, before the bound `b`, of the flow started at `x` into a set `A`:
`inf{s ≥ 0 : s ≤ b, X^x_s ∈ A}`, with `inf ∅ = ∞`.

With `b = ∞` this is the stopping time (16)/(17) of Colaneri & De Angelis,
arXiv:1905.02650v4, pp.10–11, `inf{s ≥ 0 : X_s ∈ A}`; with `b = T − t` it is the finite-horizon
version, where "given `z = (t, x)`, the infimum in (16) is taken on `s ∈ [0, T − t]`" (p.11). -/
noncomputable def entryTime {S Ω : Type*} (X : S → ℝ≥0 → Ω → S) (x : S) (A : Set S)
    (b : ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : (s : ℝ≥0∞) ≤ b ∧ X x s ω ∈ A), (s : ℝ≥0∞)

end RecursiveStopping


