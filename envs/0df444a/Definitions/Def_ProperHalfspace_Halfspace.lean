-- Prove2me | Definitions.Def_ProperHalfspace_Halfspace
-- name    : ProperHalfspace_Halfspace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:40.937233+00:00
-- url     : https://prove2.me/theorems/ab5f01e5-bd73-42b7-afe9-2b7edd37190f
-- title:
--   The sign convention, halfspaces, $\mathrm{err}_f$, $\mathrm{corr}_f$ and $\mathrm{OPT}_f$
-- statement:
--   The sign function is
--   $$\operatorname{sign}(t)=\begin{cases}+1&t\ge0,\\-1&t<0.\end{cases}$$
--   The class $\mathcal H_n$ consists of the functions $h(x)=\operatorname{sign}(w\cdot x-\theta)$ on $\{\pm1\}^n$ with $w\in\mathbb R^n$ and $\theta\in\mathbb R$, the constants ($w=0$) included. For $f,g:\{\pm1\}^n\to\mathbb R$,
--   $$\mathrm{err}_f(g)=\Pr_x[f(x)\ne g(x)],\qquad \mathrm{corr}_f(g)=\mathbf E_x[f(x)g(x)],\qquad \mathrm{OPT}_f=\min_{h\in\mathcal H_n}\mathrm{err}_f(h).$$
--
--   These define the learning goal: to output a member of $\mathcal H_n$ whose error is within $\varepsilon$ of $\mathrm{OPT}_f$.
--
--   **Formalization Note** Mathlib's `Real.sign` has `Real.sign 0 = 0` and is not used. $\mathrm{OPT}_f$ is written as an infimum over all parameters $(w,\theta)$; only finitely many functions on the cube arise, so the infimum is attained.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), §1, p.1; §2, p.11; §2.3, p.13

import Mathlib
import Definitions.Def_ProperHalfspace_Cube

namespace ProperHalfspace

/-!
# Signs, halfspaces, error, correlation and OPT

De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026), §1, p.1; §2, p.11; §2.3, p.13.

**Formalization Note.** `sgn` is the page's `sign`, with `sign(0) = +1`. It is not Mathlib's `Real.sign`, which has
`Real.sign 0 = 0`. Constant halfspaces (`w = 0`) are included, as on p.13. `opt` is the page's minimum, written as an
infimum over the nonempty parameter type; the cube is finite, so the infimum is attained.
-/

/-- `sign(t) = +1` for `t ≥ 0` and `−1` for `t < 0` (p.13). -/
noncomputable def sgn (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

/-- The halfspace `h(x) = sign(w · x − θ)` on the cube (p.1, p.13). -/
noncomputable def ltf {n : ℕ} (w : Fin n → ℝ) (θ : ℝ) (x : Cube n) : ℝ :=
  sgn (∑ i, w i * coord x i - θ)

/-- `err_f(g) = Pr_x[f(x) ≠ g(x)]` (p.1). -/
noncomputable def err {n : ℕ} (f g : Cube n → ℝ) : ℝ := cubeProb fun x => f x ≠ g x

/-- `corr_f(g) = E[f g]` (p.11). -/
noncomputable def corr {n : ℕ} (f g : Cube n → ℝ) : ℝ := cubeAvg fun x => f x * g x

/-- `OPT_f = min_{h ∈ H_n} err_f(h)` (p.1), the infimum over all parameters `(w, θ)`. -/
noncomputable def opt {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  ⨅ p : (Fin n → ℝ) × ℝ, err f (ltf p.1 p.2)

end ProperHalfspace


