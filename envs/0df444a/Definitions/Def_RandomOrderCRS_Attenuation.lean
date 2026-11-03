-- Prove2me | Definitions.Def_RandomOrderCRS_Attenuation
-- name    : RandomOrderCRS_Attenuation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:20:27.364388+00:00
-- url     : https://prove2.me/theorems/40d32f43-061d-4b35-8273-196faf66c965
-- title:
--   The attenuation function $a_1$, the functions $s$, $\ell$, $\tau$, $T$ and the constant $c^*$
-- statement:
--   The analysis of Algorithm 2 uses the following explicit functions. For an attenuation function $a:[0,1]\to[0,1]$,
--
--   $$s(x):=x\,a(x),\qquad \ell(x,y):=1-y\,s(x),$$
--
--   where $s(x)$ is the probability that an edge of value $x$ survives and $\ell(x,y)$ is the probability that it is irrelevant at arrival time $y$. The attenuation function used on general graphs is
--
--   $$a_1(x):=(1-(3-e)x)^2.$$
--
--   The auxiliary function of Lemma 3 of the paper is
--
--   $$T(x,y):=\frac{s(1-x)}{x}\left(1-\frac{1-e^{-xy}}{xy}\right),$$
--
--   and the constant of Theorem 3 is
--
--   $$c^*:=\frac{e^2-4e^3+e^4+20e-22}{4e^2}.$$
--
--   **Formalization Note** To remove the $0/0$ in $T$, set $\tau(t):=(t-1+e^{-t})/t^2$ for $t\ne0$ and $\tau(0):=1/2$, and define $T(x,y)=s(1-x)\,y\,\tau(xy)$. This equals the printed formula when $xy\ne0$, equals the limit $a(1)y/2$ of p.ec18 at $x=0$, and vanishes at $y=0$. The file also proves that $a_1$ maps $[0,1]$ to $[0,1]$. In Lean $a_1$ is a polynomial on $\mathbb R$, and only its values on $[0,1]$ have a meaning; here $a$ is a function `ℝ → ℝ`.
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, p.17 (a₁, s), p.19 (ℓ), Lemma 3, p.20 (T), Theorem 3, p.17 (c*), ec18 (limit of T)

import Mathlib

open Real

namespace RandomOrderCRS

/-- The quadratic attenuation function `a₁(x) := (1 − (3 − e)x)²`, arXiv:2209.07520v2, p.17.

**Formalization Note.** The paper has `a : [0, 1] → [0, 1]`; `a₁` is a polynomial on all of `ℝ`, and
only its values on `[0, 1]` have a meaning. -/
noncomputable def a₁ (x : ℝ) : ℝ := (1 - (3 - exp 1) * x) ^ 2

/-- `a₁` maps `[0, 1]` to `[0, 1]`: it is an attenuation function in the sense of p.17. -/
theorem a₁_mem_Icc : ∀ t ∈ Set.Icc (0 : ℝ) 1, a₁ t ∈ Set.Icc (0 : ℝ) 1 := by
  intro t ht
  have h2 : (2 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have h3 : exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have h0 : 0 ≤ (3 - exp 1) * t := mul_nonneg (by linarith) ht.1
  have h1 : (3 - exp 1) * t ≤ 1 := by nlinarith [ht.1, ht.2]
  constructor
  · exact sq_nonneg _
  · unfold a₁; nlinarith

/-- The survival probability `s(x) := x a(x)`, arXiv:2209.07520v2, p.17. -/
noncomputable def survival (a : ℝ → ℝ) (x : ℝ) : ℝ := x * a x

/-- `ℓ(x, y) := 1 − y s(x)`, arXiv:2209.07520v2, p.19: "the probability that f is irrelevant". -/
noncomputable def ell (a : ℝ → ℝ) (x y : ℝ) : ℝ := 1 - y * survival a x

/-- The auxiliary function `τ(t) := (t − 1 + e^{−t}) / t²` with `τ(0) := 1/2`, its limit at `0`.

**Formalization Note.** Not in the paper. It removes the `0/0` of the printed formulas for `T` and
for the right side of Lemma 2: `(1/z)(1 − (1 − e^{−zy})/(zy)) = y τ(zy)` when `zy ≠ 0`. -/
noncomputable def tau (t : ℝ) : ℝ := if t = 0 then 1 / 2 else (t - 1 + exp (-t)) / t ^ 2

/-- `T(x, y) := (s(1 − x)/x)(1 − (1 − e^{−xy})/(xy))`, arXiv:2209.07520v2, Lemma 3, p.20.

**Formalization Note.** Stated as `s(1 − x) · y · τ(xy)`. For `x y ≠ 0` this is the printed formula.
At `x = 0` it is the limit `a(1)y/2` that the paper uses ("`lim_{x→0⁺} T(x, y)` exists, and is equal
to `a(1)y/2`", ec18), and at `y = 0` it is `0`. In Lean the printed formula would give junk at
`xy = 0`, since `0/0 = 0` there. Only `x ∈ [0, 1]` has a meaning, because `a` is defined on
`[0, 1]`. -/
noncomputable def T (a : ℝ → ℝ) (x y : ℝ) : ℝ := survival a (1 - x) * y * tau (x * y)

/-- The constant `c* := (e² − 4e³ + e⁴ + 20e − 22)/(4e²)` of Theorem 3, arXiv:2209.07520v2, p.17. -/
noncomputable def cStar : ℝ :=
  (exp 1 ^ 2 - 4 * exp 1 ^ 3 + exp 1 ^ 4 + 20 * exp 1 - 22) / (4 * exp 1 ^ 2)

end RandomOrderCRS


