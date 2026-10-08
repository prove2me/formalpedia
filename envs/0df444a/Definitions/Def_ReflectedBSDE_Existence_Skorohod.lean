-- Prove2me | Definitions.Def_ReflectedBSDE_Existence_Skorohod
-- name    : ReflectedBSDE_Existence_Skorohod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:09.475434+00:00
-- url     : https://prove2.me/theorems/83265535-307c-4c00-8a0a-56024d3042c5
-- title:
--   Lemma 2.1, pp. 704–705 — the Stieltjes measure $dk$ of a continuous nondecreasing path and the Skorohod problem
-- statement:
--   Let $k:[0,\infty)\to\mathbb R$ be continuous and nondecreasing. Its **Lebesgue–Stieltjes measure** $dk$ is the Borel measure on $\mathbb R$ obtained from the extension $x\mapsto k(\max(x,0))$, so that
--   $$dk\big((a,b]\big)=k(b)-k(a),\qquad 0\le a\le b,$$
--   and $dk$ gives no mass to $(-\infty,0]$ and no mass to any single point. Integrals $\int_0^\infty y_t\,dk_t$ of nonnegative functions are taken against this measure.
--
--   Let $x:[0,\infty)\to\mathbb R$ be continuous. A pair $(y,k)$ of functions on $[0,\infty)$ **solves the Skorohod problem** for $x$ if
--
--   1. $y=x+k$;
--   2. $y_t\ge 0$ for all $t\ge 0$;
--   3. $k$ is continuous and nondecreasing, $k_0=0$, and $\displaystyle\int_0^\infty y_t\,dk_t=0$.
--
--   Condition 3 says that $k$ increases only at times when $y$ sits at $0$: $k$ is the minimal push that keeps $x+k$ nonnegative. This is the deterministic prototype of the reflection in the reflected backward SDE, where the increasing process $K$ pushes $Y$ upwards only when $Y$ touches the obstacle $S$.
--
--   **Formalization Note** The measure is Mathlib's `StieltjesFunction.measure` of $x\mapsto k(x^+)$. For a path that is not continuous and nondecreasing the definition returns the zero measure; every use of it in this mission requires the path to be continuous and nondecreasing. "Positive" and "increasing" in the paper mean $\ge 0$ and nondecreasing.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), pp. 704–705 (PDF pp. 3–4), Lemma 2.1

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedBSDE.Existence

/-- The function `x ↦ k(x⁺)` on `ℝ`: a path `k` on `[0, ∞[` extended to the whole line by its
value at `0` on `]-∞, 0]`. -/
noncomputable def extendPath (k : ℝ≥0 → ℝ) : ℝ → ℝ := fun x => k x.toNNReal

lemma extendPath_monotone {k : ℝ≥0 → ℝ} (hk : Monotone k) : Monotone (extendPath k) :=
  fun _ _ h => hk (Real.toNNReal_le_toNNReal h)

lemma extendPath_continuous {k : ℝ≥0 → ℝ} (hk : Continuous k) : Continuous (extendPath k) :=
  hk.comp continuous_real_toNNReal

open Classical in
/-- The Lebesgue–Stieltjes measure `dk` on `ℝ` of a continuous nondecreasing path
`k : [0, ∞[ → ℝ` (extended constantly to the left of `0`, so `dk` charges no point and no part of
`]-∞, 0[`): `dk(]a, b]) = k(b) − k(a)` for `0 ≤ a ≤ b`. For a path that is not continuous and
nondecreasing the value is the zero measure; it is used only for continuous nondecreasing paths. -/
noncomputable def pathMeasure (k : ℝ≥0 → ℝ) : Measure ℝ :=
  if h : Monotone k ∧ Continuous k then
    (StieltjesFunction.mk (extendPath k) (extendPath_monotone h.1)
      (fun _ => (extendPath_continuous h.2).continuousWithinAt)).measure
  else 0

/-- Lemma 2.1 (pp. 704–705): `(y, k)` solves the Skorohod problem for the path `x` on `[0, ∞[`:
(a) `y = x + k`; (b) `y ≥ 0`; (c) `k` is continuous and nondecreasing, `k_0 = 0`, and
`∫₀^∞ y_t dk_t = 0`, the integral being taken against the Stieltjes measure `dk` of `k`. -/
def IsSkorohodSolution (x y k : ℝ≥0 → ℝ) : Prop :=
  y = x + k ∧ (∀ t, 0 ≤ y t) ∧ Continuous k ∧ Monotone k ∧ k 0 = 0 ∧
    ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (y t.toNNReal) ∂(pathMeasure k) = 0

end ReflectedBSDE.Existence


