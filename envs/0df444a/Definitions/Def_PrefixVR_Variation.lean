-- Prove2me | Definitions.Def_PrefixVR_Variation
-- name    : PrefixVR_Variation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:48.093352+00:00
-- url     : https://prove2.me/theorems/da82289d-6af7-4831-b805-50644e248b44
-- title:
--   Condition (2): variation of component-gradient differences
-- statement:
--   Let $g_1,\dots,g_n:\mathbb R^d\to\mathbb R^d$ be component gradient maps and write $\bar g(x)=\frac1n\sum_{i=1}^n g_i(x)$ for their average (when $g_i=\nabla f_i$, $\bar g=\nabla f$ for $f=\frac1n\sum_i f_i$). For $\delta\in\mathbb R$, **condition (2)** holds if for all $x,y\in\mathbb R^d$
--   $$
--   \frac1n\sum_{i=1}^n\big\|g_i(x)-g_i(y)-\bar g(x)+\bar g(y)\big\|^2\le\delta^2\,\|x-y\|^2 .
--   $$
--   It bounds the centered variation of component-gradient differences, which is what a sampled difference $g_i(x)-g_i(y)$ adds as error; it can be much smaller than the component smoothness constant.
--
--   The module also defines the average map $\bar g$ (`gradAvg`).
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with the Euclidean norm, components are `Fin n`. The condition $\delta\ge0$ of Assumption 3 is not part of (2); it is kept in `Assumption3`. At $n=0$ the average is the junk value $0$; the algorithmic statements assume $n\ge1$.
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), Assumption 3, Eq. (2), p.4 (PDF p.4)

import Mathlib

namespace PrefixVR

/-- **The average of the component gradients**, `(1/n) ∑ᵢ gᵢ(x)`.
Jiang, Wang, Yang, Li, Zhang, *Memory-efficient Finite-sum Optimization without Full Gradient
Refreshes* (manuscript, sha256 ed33106a…), Problem (1), p.1, and Algorithm 1, line 1, p.5: when
`gᵢ = ∇fᵢ`, this is `∇f(x)` for `f = (1/n) ∑ᵢ fᵢ`.

**Formalization Note.** The paper's components `i = 1, …, n` are `Fin n` (paper index `i` is
`i − 1`). The value is the junk `0` at `n = 0`; every algorithmic statement assumes `NeZero n`. -/
noncomputable def gradAvg {n d : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i, g i x

/-- **Condition (2): variation of component-gradient differences.**
Jiang, Wang, Yang, Li, Zhang (manuscript, sha256 ed33106a…), Assumption 3, Eq. (2), p.4:
for all `x, y ∈ ℝᵈ`,
`(1/n) ∑_{i=1}^n ‖∇fᵢ(x) − ∇fᵢ(y) − ∇f(x) + ∇f(y)‖² ≤ δ² ‖x − y‖²`.

`Variation g δ` states (2) for component maps `g i` in place of `∇fᵢ`, with `∇f` replaced by
their average `gradAvg g`.

**Formalization Note.** The space `ℝᵈ` is `EuclideanSpace ℝ (Fin d)` (Euclidean norm, p.4). The
gradients enter only through the maps `g i`; when `g i = ∇fᵢ` the average `gradAvg g` is `∇f`, so
this is exactly (2). The sign condition `δ ≥ 0` of Assumption 3 is not part of (2) and is kept in
`Assumption3`. -/
def Variation {n d : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (δ : ℝ) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin d),
    (n : ℝ)⁻¹ * ∑ i, ‖g i x - g i y - gradAvg g x + gradAvg g y‖ ^ 2 ≤ δ ^ 2 * ‖x - y‖ ^ 2

end PrefixVR


