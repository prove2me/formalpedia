-- Prove2me | Definitions.Def_ChurnServiceMode_IsReflectedOUPath
-- name    : ChurnServiceMode_IsReflectedOUPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:38.589654+00:00
-- url     : https://prove2.me/theorems/abf96429-e96c-4efd-ab5c-f074c0e79c55
-- title:
--   Reflected Ornstein–Uhlenbeck path (Definition 3)
-- statement:
--   Let $\sigma>0$, $\theta\in\mathbb R$ and $x\ge0$. A path $z$ on $[0,\infty)$ is a **$(\sigma,\theta)$ reflected O-U path** started at $x$, driven by the path $b$ with regulator $l$, if
--   1. $z_t=x+\theta t-\int_0^tz_s\,ds+\sigma b_t+l_t$ for $t\ge0$;
--   2. $z_t\ge0$ for $t\ge0$;
--   3. $l$ is non-decreasing with $l_{0-}=0$;
--   4. $\int_0^\infty\mathbb 1\{z_t>0\}\,dl_t=0$.
--
--   A process is a reflected O-U process (driven by a Brownian motion $B$) when almost every path satisfies this definition. It is the comparison process of Lemma 7.
--
--   **Formalization Note** Condition 3 is: $l$ extended by $0$ to negative times is monotone. Condition 4 uses the Lebesgue–Stieltjes measure of that extension (built from right limits, so a jump of $l$ at time $t$, including $t=0$, is an atom at $t$): it gives measure zero to $\{t\ge0:z_t>0\}$. No continuity of $z$ or $l$ is assumed.
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Definition 3, p.23 (after Reed et al., Definition 3.1)

import Mathlib

open MeasureTheory
open scoped NNReal

namespace ChurnServiceMode

/-- A path `l : [0, ∞) → ℝ` extended by `0` to negative times (so that `l_{0−} = 0`). -/
noncomputable def extendByZero (l : ℝ≥0 → ℝ) (r : ℝ) : ℝ :=
  if r < 0 then 0 else l r.toNNReal

/-- **Reflected O-U path** (Definition 3, Kanoria, Lobel & Lu, SSRN 3188226, p.23, from Reed et
al. Definition 3.1): the path `z` is a `(σ, θ)` reflected O-U path started at `x ≥ 0`, driven by
the path `b` with regulator `l`, if `σ > 0` and

1. `z_t = x + θt − ∫₀ᵗ z_s ds + σ b_t + l_t` for `t ≥ 0`;
2. `z_t ≥ 0` for `t ≥ 0`;
3. `l` is non-decreasing with `l_{0−} = 0`;
4. `∫₀^∞ 1{z_t > 0} dl_t = 0`.

**Formalization Note.** Conditions 3–4: `l` extended by `0` before time `0` is monotone (this is
"non-decreasing with `l_{0−} = 0`", i.e. `l` non-decreasing and `l₀ ≥ 0`), and the
Lebesgue–Stieltjes measure `dl` of that extension (built from right limits, so a jump of `l` at
`t` is an atom at `t`, including at `t = 0`) gives measure zero to `{t ≥ 0 : z_t > 0}`. No
continuity of `z` or `l` is assumed. The process version of Definition 3 asks this of almost every
path. -/
def IsReflectedOUPath (σ θ x : ℝ) (b z l : ℝ≥0 → ℝ) : Prop :=
  0 < σ ∧ 0 ≤ x ∧
  (∀ t : ℝ≥0, z t = x + θ * t - (∫ s in (0 : ℝ)..(t : ℝ), z s.toNNReal) + σ * b t + l t) ∧
  (∀ t, 0 ≤ z t) ∧
  ∃ hl : Monotone (extendByZero l),
    hl.stieltjesFunction.measure {r : ℝ | 0 ≤ r ∧ 0 < z r.toNNReal} = 0

end ChurnServiceMode


