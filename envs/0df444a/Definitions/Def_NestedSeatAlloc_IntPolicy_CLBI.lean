-- Prove2me | Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI
-- name    : NestedSeatAlloc_IntPolicy_CLBI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:18:01.197994+00:00
-- url     : https://prove2.me/theorems/005353cb-e41e-4224-9f0c-d5c8e0ff3abb
-- title:
--   p. 132 — CLBI: concave on s ≥ 0 and linear between integers
-- statement:
--   A function $g : \mathbb R \to \mathbb R$ is **CLBI** ("Concave and Linear Between Integers") if
--
--   1. $g$ is concave on $[0, \infty)$, and
--   2. for every integer $m \ge 0$ there are constants $a, b$ with
--   $$g(s) = a + b\,s \qquad \text{for all } s \in [m, m+1].$$
--
--   Equivalently, on $s \ge 0$ the function is concave and piecewise linear, with changes in slope only at integer values of the domain. In the paper the term is applied to the revenue and expected revenue functions $s \mapsto ER_k[s; p; X]$ when demands and protection levels are integers. Its use is the covering property: between a right derivative and a larger left derivative, every value is a subgradient at some integer point, which is how integer optimal protection levels are produced.
--
--   **Formalization Note** Linearity between integers is stated on each closed unit interval $[m, m+1]$, $m \in \mathbb N$; together with concavity on $[0,\infty)$ this is the paper's "concave and piecewise linear with changes in slope only at integer values". Nothing is required for $s < 0$.
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), §3, definition of CLBI preceding Theorem 2, p. 132

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

/-- CLBI, "Concave and Linear Between Integers" (Brumelle–McGill 1993, p. 132): `g` is concave on `s ≥ 0`
and affine on every unit interval `[m, m + 1]`, `m ∈ ℕ`, so that it is piecewise linear on `s ≥ 0` with
changes in slope only at integer values. -/
def IsCLBI (g : ℝ → ℝ) : Prop :=
  ConcaveOn ℝ (Set.Ici 0) g ∧ ∀ m : ℕ, ∃ a b : ℝ, ∀ s ∈ Set.Icc (m : ℝ) (m + 1), g s = a + b * s

end NestedSeatAlloc.IntPolicy


