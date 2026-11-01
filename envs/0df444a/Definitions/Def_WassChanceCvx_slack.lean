-- Prove2me | Definitions.Def_WassChanceCvx_slack
-- name    : WassChanceCvx_slack
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:01.229027+00:00
-- url     : https://prove2.me/theorems/6e028b41-d2d4-46cc-ad59-2ba7391c4ed9
-- title:
--   Normalized slack $f(x,\zeta)$
-- statement:
--   For rows $a_1,\dots,a_k$ (continuous linear functionals on $E$) and $\beta\in\mathbb R^k$, let $I=\{i: a_i=0\}$ and, for $\zeta\in E$,
--
--   $$
--   f(\zeta)=\min_{i\in[k]\setminus I}\ \frac{\beta_i-a_i(\zeta)}{\|a_i\|_*}.
--   $$
--
--   With $a=A(x)$ and $\beta=b(x)$ this is the paper's $f(x,\zeta)$, the scaled slack of the most violated nonzero safety row; when no zero row is violated, $d(\zeta,\mathcal S^c(x))=(f(x,\zeta))^+$.
--
--   **Formalization Note** $\|a_i\|_*$ is the operator norm of $a_i$, i.e. the dual norm. The minimum is the real infimum over the finite set $[k]\setminus I$; it is the paper's minimum when $A(x)\ne0$. When every row vanishes the paper's $f$ is undefined and Lean's value is $0$; every statement using $f$ assumes $A(x)\ne0$.
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, p.7 (display defining f and I(x))

import Mathlib

namespace WassChanceCvx

/-- **The normalized slack `f(x, ζ)`.**
Shen, Jiang, arXiv:2111.02486v2, p.7: "we define function `f : ℝⁿ × ℝ^m → ℝ`,
`f(x, ζ) := min_{i∈[m]∖I(x)} {(bᵢ(x) − aᵢ(x)ᵀζ)/‖aᵢ(x)‖_*}`, where `I(x) := {i ∈ [m] : aᵢ(x) = 0}`."

`slack a β ζ = min_{i : aᵢ ≠ 0} (βᵢ − aᵢ(ζ)) / ‖aᵢ‖_*`; with `a = A(x)`, `β = b(x)` it is
`f(x, ζ)`.

**Formalization Note.** `‖aᵢ‖_*` is the operator norm of the functional `aᵢ`, i.e. the dual norm
of the norm of `E`. The minimum is the real infimum over the finite index set `[m] ∖ I(x)`; it is
the paper's minimum when some row is nonzero (`A(x) ≠ 0`). When all rows vanish the paper's `f`
is undefined and the value is Lean's junk `0`; every statement using `slack` assumes `A(x) ≠ 0`. -/
noncomputable def slack {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (a : Fin k → StrongDual ℝ E) (β : Fin k → ℝ) (ζ : E) : ℝ :=
  ⨅ i : {i : Fin k // a i ≠ 0}, (β i - a i ζ) / ‖a i‖

end WassChanceCvx


