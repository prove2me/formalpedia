-- Prove2me | Definitions.Def_FixedPriceTrade_J
-- name    : FixedPriceTrade_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:44.088829+00:00
-- url     : https://prove2.me/theorems/0b6ffaed-a756-4d7d-afda-49101987b810
-- title:
--   The control functional $J_d(h)$
-- statement:
--   For $d>0$ and a measurable control $h:[0,1]\to[0,1]$ put
--   $$
--   g(t)=d+\int_0^t h(u)\,du,\qquad k(t)=\int_0^t h(u)^2\,du,
--   $$
--   and
--   $$
--   J_d(h)=\int_0^1\Big[\frac{h(t)}{g(t)}+\frac{d^2-k(t)}{g(t)^2}\Big]dt .
--   $$
--   Here $d$ is the initial state $g(0)$. After reversing time, a buyer survival function $H$ gives the nondecreasing control $h=H(1-\cdot)$; the paper maximizes $J_d$ over the whole measurable box.
--
--   **Formalization Note** A control is a measurable $h:\mathbb R\to\mathbb R$ with values in $[0,1]$ on $[0,1]$. Since $d\le g\le d+1$ on $[0,1]$, no division by zero occurs.
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), §3, (6), p.11

import Mathlib

set_option autoImplicit false

namespace FixedPriceTrade

open Set

/-- A **control**: a measurable `h : [0, 1] → [0, 1]` (p.11).

**Formalization Note.** `h` is a function on `ℝ`, measurable, with values in `[0,1]` on `[0,1]`;
its values outside `[0,1]` never enter any formula. -/
def IsControl (h : ℝ → ℝ) : Prop :=
  Measurable h ∧ ∀ t ∈ Icc (0 : ℝ) 1, h t ∈ Icc (0 : ℝ) 1

/-- `g(t) = d + ∫_0^t h(u) du` ((6), p.11). -/
noncomputable def gState (d : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ := d + ∫ u in (0 : ℝ)..t, h u

/-- `k(t) = ∫_0^t h(u)² du` ((6), p.11). -/
noncomputable def kState (h : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, h u ^ 2

/-- **The control functional** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee of
Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), (6), p.11: for
`d > 0` and a measurable `h : [0,1] → [0,1]`,
`J_d(h) = ∫_0^1 [h(t)/g(t) + (d² − k(t))/g(t)²] dt`.

**Formalization Note.** For `d > 0` and a control, `d ≤ g ≤ d + 1` on `[0,1]`, so no division
by zero occurs and the integrand is bounded and measurable. -/
noncomputable def J (d : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (h t / gState d h t + (d ^ 2 - kState h t) / gState d h t ^ 2)

end FixedPriceTrade


