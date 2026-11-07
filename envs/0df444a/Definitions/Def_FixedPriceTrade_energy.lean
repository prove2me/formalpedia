-- Prove2me | Definitions.Def_FixedPriceTrade_energy
-- name    : FixedPriceTrade_energy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:24.40199+00:00
-- url     : https://prove2.me/theorems/3f19e5b4-b10c-4a6c-a3cf-50a253113d5b
-- title:
--   The reciprocal clock, the reciprocal state $p$ and the energy $\mathcal F_d[p]$
-- statement:
--   For a control $h$ with state $g$ (as in $J_d$), the **reciprocal clock** and the **reciprocal state** are
--   $$
--   A(t)=\int_t^1 g(u)^{-2}\,du,\qquad a_0=A(0),\qquad p(A(t))=\frac1{g(t)},\qquad x=p(0)=\frac1{g(1)},
--   $$
--   with $p$ extended by the constant $1/d$ for $a\ge a_0$. For a positive function $p$ on $[0,\infty)$ with $x=p(0)$, the **energy** is
--   $$
--   \mathcal F_d[p]=-\log(d\cdot x)+\int_0^\infty\Big[d^2-p^{-2}-a\big((\log p)'\big)^2\Big]da .
--   $$
--   Lemma 5.1 shows $J_d(h)-1=\mathcal F_d[p]$, which turns the nonlocal objective into a local one.
--
--   **Formalization Note** $A$ is continuous and strictly decreasing on $[0,1]$, so the time at tail time $a\in[0,a_0]$ is written $\sup\{t\in[0,1]: a\le A(t)\}$. $p$ is a function on $\mathbb R$; only its values on $[0,\infty)$ matter. $(\log p)'$ is Mathlib's `deriv`; the integral is a Lebesgue integral over $(0,\infty)$.
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), §5, (16), p.12; Lemma 5.1, (E), p.13

import Mathlib
import Definitions.Def_FixedPriceTrade_J

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set

/-- The reciprocal clock `A(t) = ∫_t^1 g(u)^{−2} du` ((16), p.12). -/
noncomputable def Aclock (d : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in t..(1 : ℝ), 1 / gState d h u ^ 2

/-- The reciprocal-state endpoint `x = p(0) = 1/g(1) = (d + ∫_0^1 h)^{−1}` ((16), p.12;
Theorem C, p.19). -/
noncomputable def recipX (d : ℝ) (h : ℝ → ℝ) : ℝ := 1 / gState d h 1

/-- The original time at tail time `a`: the `t ∈ [0,1]` with `A(t) = a` for `0 ≤ a ≤ a₀`,
written as `sup {t ∈ [0,1] | a ≤ A(t)}`.

**Formalization Note.** `A` is continuous and strictly decreasing on `[0,1]` from `a₀ = A(0)` to
`A(1) = 0` (`d ≤ g ≤ d + 1`), so for `0 ≤ a ≤ a₀` this supremum is the unique solution of
`A(t) = a`. -/
noncomputable def recipTime (d : ℝ) (h : ℝ → ℝ) (a : ℝ) : ℝ :=
  sSup {t | t ∈ Icc (0 : ℝ) 1 ∧ a ≤ Aclock d h t}

/-- The reciprocal state `p` of (16), p.12: `p(A(t)) = 1/g(t)` for `t ∈ [0,1]`, extended by the
constant `1/d` for `a ≥ a₀ = A(0)`.

**Formalization Note.** A function on `ℝ`; only its values on `[0, ∞)` enter any statement. At
`a = 0` it is `1/g(1) = x`. -/
noncomputable def recipP (d : ℝ) (h : ℝ → ℝ) (a : ℝ) : ℝ :=
  if Aclock d h 0 ≤ a then 1 / d else 1 / gState d h (recipTime d h a)

/-- **The energy** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee of Fixed-Price
Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), Lemma 5.1, (E), p.13:
`F_d[p] = −log(d · x) + ∫_0^∞ [d² − p^{−2} − a((log p)′)²] da`, with `x = p(0)`;
together with the reciprocal clock `A`, the endpoint `x` and the reciprocal state `p` of (16).

**Formalization Note.** `p` is a function on `ℝ` and `x = p(0)` is read off from it. The
derivative `(log p)′` is Mathlib's `deriv`, which agrees almost everywhere with the derivative of
the (absolutely continuous) functions the paper applies `F_d` to. The integral is a Lebesgue
integral over `(0, ∞)`; every statement that uses it states its integrability. -/
noncomputable def energy (d : ℝ) (p : ℝ → ℝ) : ℝ :=
  -Real.log (d * p 0) +
    ∫ a in Ioi (0 : ℝ), (d ^ 2 - 1 / p a ^ 2 - a * deriv (fun b => Real.log (p b)) a ^ 2)

end FixedPriceTrade


