-- Prove2me | Definitions.Def_MultimodularDocks_IsMultimodular
-- name    : MultimodularDocks_IsMultimodular
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:43.286274+00:00
-- url     : https://prove2.me/theorems/76ee2032-3121-48c2-9008-0bda18cd5844
-- title:
--   Multimodular function on the quadrant (Definition 1, corrected)
-- statement:
--   A function $f:\mathbb Z\times\mathbb Z\to\mathbb R$ of a number $d$ of empty docks and a number $b$ of bikes is **multimodular** if
--
--   $$
--   \begin{aligned}
--   f(d+1,b+1)-f(d+1,b)&\ge f(d,b+1)-f(d,b), &&(1)\\
--   f(d-1,b+1)-f(d-1,b)&\ge f(d,b)-f(d,b-1), &&(2)\\
--   f(d+1,b-1)-f(d,b-1)&\ge f(d,b)-f(d-1,b) &&(3)
--   \end{aligned}
--   $$
--
--   whenever every argument occurring in the inequality is nonnegative, that is, for $d,b\ge 0$ in (1) and $d,b\ge 1$ in (2) and (3).
--
--   The three inequalities are discrete diminishing-returns properties: an extra full dock helps less once an empty dock has been added (1), and moving between empty and full docks has the convexity properties (2) and (3). Every result of the mission assumes that each station cost is multimodular in this sense.
--
--   **Formalization Note** The paper states (1)–(3) for all $d,b\in\mathbb Z$ for an $f$ with values in $\mathbb R\cup\{\infty\}$ and the convention $\infty-\infty=\infty$. With that convention Lemma 2.1 fails at $d=-1$, so the definition is stated for real $f$ on the quadrant $d,b\ge 0$, where every station cost of the paper is finite; the value $+\infty$ outside a station's band is modeled by feasibility constraints instead.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Definition 1, p.10 (corrected; see the mission's Lemma 2.1 item)

import Mathlib

namespace MultimodularDocks

/-- **Multimodularity on the quadrant** (Freund, Henderson, Shmoys, *Minimizing Multimodular
Functions and Allocating Capacity in Bike-Sharing Systems*, arXiv:1611.09304v5, Definition 1,
p.10). A function `f : ℤ → ℤ → ℝ` is multimodular if

* (1) `f (d+1) (b+1) - f (d+1) b ≥ f d (b+1) - f d b`,
* (2) `f (d-1) (b+1) - f (d-1) b ≥ f d b - f d (b-1)`,
* (3) `f (d+1) (b-1) - f d (b-1) ≥ f d b - f (d-1) b`,

whenever all arguments occurring in the inequality are nonnegative (that is, `0 ≤ d, 0 ≤ b` for
(1) and `1 ≤ d, 1 ≤ b` for (2) and (3)).

**Formalization Note** The page states (1)–(3) "for all d, b" for an `f : ℤ² → ℝ ∪ {∞}` with the
convention `∞ − ∞ = ∞`. With that convention Lemma 2.1 (p.11) is false (at `d = −1` inequality
(1) reads `0 ≥ ∞`), so the definition is corrected to a real-valued `f` and the inequalities on
the quadrant `d, b ≥ 0`, where every station cost of the paper is finite. The value `+∞` of a
station cost outside its band is carried separately (`InBand`, `Feasible`). -/
def IsMultimodular (f : ℤ → ℤ → ℝ) : Prop :=
  (∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
      f d (b + 1) - f d b ≤ f (d + 1) (b + 1) - f (d + 1) b) ∧
  (∀ d b : ℤ, 1 ≤ d → 1 ≤ b →
      f d b - f d (b - 1) ≤ f (d - 1) (b + 1) - f (d - 1) b) ∧
  (∀ d b : ℤ, 1 ≤ d → 1 ≤ b →
      f d b - f (d - 1) b ≤ f (d + 1) (b - 1) - f d (b - 1))

end MultimodularDocks


