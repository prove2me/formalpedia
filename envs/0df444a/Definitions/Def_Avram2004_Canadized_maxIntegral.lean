-- Prove2me | Definitions.Def_Avram2004_Canadized_maxIntegral
-- name    : Avram2004_Canadized_maxIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:28:25.189396+00:00
-- url     : https://prove2.me/theorems/672795b1-a3e9-4a86-9b9c-b9949b69f398
-- title:
--   Lebesgue–Stieltjes integral against the running maximum: ∫_0^T e^{−at+Y_t} dX̄_t
-- statement:
--   Let $X$ be a spectrally negative Lévy process, and consider the process started from position $x$ with prior maximum $s\ge x$ (the paper's $\mathbb P_{s,x}$). Its running maximum $\overline X_t=\max\{s,\sup_{0\le u\le t}(x+X_u)\}$ is a nondecreasing function of $t$, and $Y=\overline X-X$ is the reflected process. The random measure $d\overline X_t$ is the Lebesgue–Stieltjes measure of the path $t\mapsto\overline X_t$, and for a random time $T$ and $a\in\mathbb R$ we define, path by path,
--   $$
--   \int_0^T e^{-at+Y_t}\,d\overline X_t,
--   $$
--   the integral taken over $(0,T]$ (over $(0,\infty)$ when $T=\infty$).
--
--   This is the integral appearing in the paper's Itô identity (34) and in the proof of Lemma 3: the running maximum grows only when $X$ is at its supremum, and the integral measures the discounted payoff accumulated at those times.
--
--   **Formalization Note** The path $t\mapsto\overline X_t$ is extended to $t<0$ by its value at $0$ and turned into Mathlib's Stieltjes measure (using the right-continuous version, which coincides with the path since $\overline X$ is continuous for a process without upward jumps). On a path along which $t\mapsto\overline X_t$ were not nondecreasing, a placeholder zero measure is used; this never happens for càdlàg paths. The integral is a lower Lebesgue integral with values in $[0,\infty]$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 232, Eq. (34) (the term dX̄_t), and p. 233, proof of Lemma 3; running maximum as in §4, p. 220

import Mathlib
import Definitions.Def_Avram2004_Shared_reflected

open MeasureTheory
open scoped NNReal ENNReal

namespace Avram2004.Canadized

/-- The running-maximum path `t ↦ X̄_t` of `ℙ_{s,x}` (§4, p. 220), extended to `t < 0` by its value
at `0` (namely `max s x`), as a function on `ℝ`. -/
noncomputable def maxPath {Ω : Type*} (s x : ℝ) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ :=
  fun t => Shared.runMax s x X t.toNNReal ω

/-- The Lebesgue–Stieltjes measure `dX̄_t` of the (nondecreasing) running-maximum path of `ℙ_{s,x}`.
For a path along which `t ↦ X̄_t` is nondecreasing (every càdlàg path) this is the Stieltjes measure
of that path; the value `0` on other paths is only a placeholder. -/
noncomputable def maxMeasure {Ω : Type*} (s x : ℝ) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℝ :=
  open Classical in
  if h : Monotone (maxPath s x X ω) then h.stieltjesFunction.measure else 0

/-- The pathwise Lebesgue–Stieltjes integral `∫_0^T e^{-a t + Y_t} dX̄_t` under `ℙ_{s,x}`
(`Y = refl s x X`) up to a random time `T` (over `(0, T]`, and over `(0, ∞)` when `T = ∞`), as an
extended nonnegative real. -/
noncomputable def maxIntegral {Ω : Type*} (a s x : ℝ) (X : ℝ≥0 → Ω → ℝ) (T : Ω → WithTop ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t in {t : ℝ | 0 < t ∧ (((t.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ T ω)},
    ENNReal.ofReal (Real.exp (-a * t + Shared.refl s x X t.toNNReal ω)) ∂(maxMeasure s x X ω)

end Avram2004.Canadized


