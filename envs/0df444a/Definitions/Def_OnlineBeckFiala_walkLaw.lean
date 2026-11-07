-- Prove2me | Definitions.Def_OnlineBeckFiala_walkLaw
-- name    : OnlineBeckFiala_walkLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:50.129268+00:00
-- url     : https://prove2.me/theorems/732010a5-700e-4b26-9670-2c3ea51530d8
-- title:
--   One step of the Metropolis walk of §2.1 and the law of $X_t$
-- statement:
--   Let $\mu$ be a probability density on $\mathbb R^n$, positive on $(-L,L)^n$ and zero off it, with transition probabilities $p^\pm_v$, $p^0_v$ as in (4)–(6). Given non-random vectors $v_1,v_2,\dots$, the **walk** of §2.1 starts at $X_0\sim\mu$ and moves by
--   $$X_t=X_{t-1}+\delta_t v_t,\qquad P\{\delta_t=s\mid X_{t-1}\}=p^s_{v_t}(X_{t-1}),\quad s\in\{+,-,0\}.$$
--   The **one-step law** from a state $x$ in the cube is the mixture $p^+_v(x)\,\delta_{x+v}+p^-_v(x)\,\delta_{x-v}+p^0_v(x)\,\delta_x$ of point masses, and the **law of $X_t$** is the initial law $\mu$ pushed through the one-step laws of $v_1,\dots,v_t$ in turn.
--
--   This is the walk whose stationarity is Lemma 2.2; three coupled copies of it give the algorithm of Proposition 2.7.
--
--   **Formalization Note** Off the cube the paper defines no step; here the state stays where it is. That branch has probability zero, because the walk starts from $\mu$, which lives on the cube. The law of $X_t$ is computed with `Measure.bind`, as a fold over the list $[v_1,\dots,v_t]$.
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), p.4, §2.1, display following (6)

import Mathlib
import Definitions.Def_OnlineBeckFiala_IsBalanced

open MeasureTheory

namespace OnlineBeckFiala

open Classical in
/-- The one-step transition law of the walk of §2.1, p.4 (Altschuler, Tikhomirov, arXiv:2607.14238,
held version, sha256 5a1529d2…): from a state `x ∈ (−L, L)^n`, move to `x + v`, `x − v`, `x` with
probabilities `p⁺_v(x)`, `p⁻_v(x)`, `p⁰_v(x)` of (4)–(6).

**Formalization Note.** Off the cube the paper does not define a step; here the state stays put
(`dirac x`). That branch is never reached, since the walk starts from `µ`, which lives on the cube. -/
noncomputable def stepMeasure {n : ℕ} (μ : (Fin n → ℝ) → ℝ) (L : ℝ) (v x : Fin n → ℝ) :
    Measure (Fin n → ℝ) :=
  if x ∈ cube L then
    ENNReal.ofReal (pPlus μ v x) • Measure.dirac (x + v) +
      ENNReal.ofReal (pMinus μ v x) • Measure.dirac (x - v) +
      ENNReal.ofReal (pZero μ v x) • Measure.dirac x
  else Measure.dirac x

/-- The law `µ` on `ℝ^n` with density the function `μ` (Lebesgue measure on `Fin n → ℝ`). -/
noncomputable def densityLaw {n : ℕ} (μ : (Fin n → ℝ) → ℝ) : Measure (Fin n → ℝ) :=
  volume.withDensity (fun x => ENNReal.ofReal (μ x))

/-- The law of `X_t` for the walk of §2.1, p.4, driven by the non-random vectors `vs = [v₁, …, v_t]`
and started from `X₀ ∼ µ`: the initial law pushed through the one-step laws of `v₁, …, v_t` in turn.

**Formalization Note.** `Measure.bind` composes an initial law with the step map. -/
noncomputable def walkLaw {n : ℕ} (μ : (Fin n → ℝ) → ℝ) (L : ℝ) (vs : List (Fin n → ℝ)) :
    Measure (Fin n → ℝ) :=
  vs.foldl (fun ν v => ν.bind (stepMeasure μ L v)) (densityLaw μ)

end OnlineBeckFiala


