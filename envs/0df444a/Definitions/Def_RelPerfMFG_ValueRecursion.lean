-- Prove2me | Definitions.Def_RelPerfMFG_ValueRecursion
-- name    : RelPerfMFG_ValueRecursion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:27:36.660728+00:00
-- url     : https://prove2.me/theorems/6fe16627-16bb-4df8-9d05-879bee99f2ad
-- title:
--   Value functions (4.10)–(4.11), their optimizers $a_t(x)$ and the feedback controls (4.18)
-- statement:
--   Fix the common-noise path $Y$, costs $C_t$ and a terminal reward $J$. Write $\mathbb E_t[\cdot]=\mathbb E[\cdot\mid\mathcal F^Y_t]$.
--
--   1. **Value functions** (Lemma 4.1, p.21):
--   $$V_N(x):=J(x,Y),\qquad V_t(x):=\sup_{a\ge0}\big\{\mathbb E_t[V_{t+1}(x+a)]-C_t(a)\big\},\quad x\in\mathbb R_+,\ t=N-1,\dots,0.\quad(4.10)\text{–}(4.11)$$
--   $V_t(x,y)$ is $V_t(x)$ on $\{Y=y\}$; it depends on $y$ only through $y_1,\dots,y_t$.
--   2. **Optimizers** (`IsOptimizer`): functions $a_t(x,y)\ge0$ attaining the supremum in (4.11), for almost every $y$, all $t\le N-1$ and $x\ge0$.
--   3. **Feedback controls** (4.18), p.23: $\hat a_0=a_0(0)$ and $\hat a_{t+1}=a_{t+1}(\hat a_0+\dots+\hat a_t)$.
--
--   These are the objects of the backward-induction analysis of §4.3 (Lemmas 4.1–4.7), which proves that the team-wise problem has a unique solution.
--
--   **Formalization Note** $\mathbb E_t$ is the integral against the regular conditional distribution of $Y$ given its first $t$ coordinates, evaluated at the $t$-prefix of $y$, so $V_t(x,y)$ is defined for every $y$. The supremum is taken in $[0,\infty]$ (`valueENN`, no junk value; the term at $a=0$ is nonnegative, so truncating negative differences changes nothing); `value` is its real part. Optimality in (2) is written additively in $[0,\infty]$ with a finite objective at the optimizer. Periods are 0-based.
-- source:
--   Zhou, Optimal relative performance criteria in mean field contribution games, SSRN 3742584 (Nov. 13, 2022), Lemma 4.1, p.21 ((4.10), (4.11)); Lemmas 4.2–4.7, pp.22–24 (optimizers); (4.18), p.23

import Mathlib
import Definitions.Def_RelPerfMFG_Setup

open MeasureTheory ProbabilityTheory

namespace RelPerfMFG

variable {Ω : Type*} [MeasurableSpace Ω] {N e : ℕ}

/-- The cost of period `t` with a natural-number index: `C_t` for `t < N`, and `0` otherwise
(never used for `t ≥ N`). -/
noncomputable def costAt (C : Fin N → ℝ → ℝ) (t : ℕ) (a : ℝ) : ℝ :=
  if h : t < N then C ⟨t, h⟩ a else 0

/-- The regular conditional distribution of the common-noise path `Y` given
`F^Y_t = σ(Y₁, …, Y_t)` (Lean `Y j`, `j < t`): `E_t[h(Y)](ω) = ∫ h dκ_t(truncPath t (Y ω))`,
Zhou, *Optimal relative performance criteria in mean field contribution games*, SSRN 3742584
(Nov. 13, 2022), §4.3, p.21 (`E_t[·] = E[· | F^Y_t]`). -/
noncomputable def noiseKernel (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → NoisePath N e)
    (t : ℕ) : ProbabilityTheory.Kernel (NoisePath N e) (NoisePath N e) :=
  condDistrib Y (fun ω => truncPath t (Y ω)) μ

/-- Auxiliary backward recursion for (4.10)–(4.11), indexed by the number `s = N − t` of
remaining periods. -/
noncomputable def valueAux (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → NoisePath N e)
    (C : Fin N → ℝ → ℝ) (J : ℝ → NoisePath N e → ℝ) : ℕ → ℝ → NoisePath N e → ENNReal
  | 0 => fun x y => ENNReal.ofReal (J x y)
  | s + 1 => fun x y =>
      ⨆ a ∈ Set.Ici (0 : ℝ),
        (∫⁻ y', valueAux μ Y C J s (x + a) y' ∂(noiseKernel μ Y (N - (s + 1))
            (truncPath (N - (s + 1)) y))) - ENNReal.ofReal (costAt C (N - (s + 1)) a)

/-- **The value functions (4.10)–(4.11)**, SSRN 3742584 (Nov. 13, 2022), Lemma 4.1, p.21, with
values in `[0, ∞]`: `V_N(x) := J(x) = J(x, Y)` and, for `t = N − 1, …, 0`,
`V_t(x) := sup_{a ≥ 0} {E_t[V_{t+1}(x + a)] − C_t(a)}`, `x ∈ ℝ₊`; `valueENN … t x y` is
`V_t(x)|_{Y = y}`.

**Formalization Note.** `E_t` is the integral against the regular conditional distribution
`noiseKernel μ Y t` evaluated at the `t`-prefix of `y`, so `V_t(x, y)` is defined for every `y`
and depends on `y` only through `Y₁, …, Y_t`. The supremum is taken in `[0, ∞]` (no junk value);
since the term at `a = 0` is `E_t[V_{t+1}(x)] ≥ 0`, truncating negative differences at `0` does not
change it. 0-based periods. Meaningful for `t ≤ N`. -/
noncomputable def valueENN (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → NoisePath N e)
    (C : Fin N → ℝ → ℝ) (J : ℝ → NoisePath N e → ℝ) (t : ℕ) (x : ℝ) (y : NoisePath N e) :
    ENNReal :=
  valueAux μ Y C J (N - t) x y

/-- The real-valued value function `V_t(x, y)`: `valueENN` as a real number (meaningful where
`valueENN` is finite, which Lemma 4.1 asserts almost surely). -/
noncomputable def value (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → NoisePath N e)
    (C : Fin N → ℝ → ℝ) (J : ℝ → NoisePath N e → ℝ) (t : ℕ) (x : ℝ) (y : NoisePath N e) : ℝ :=
  (valueENN μ Y C J t x y).toReal

/-- The objective of (4.11) at control level `a`: `E_t[V_{t+1}(x + a)]` given `Y = y`, in
`[0, ∞]`. -/
noncomputable def stageObjective (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → NoisePath N e)
    (C : Fin N → ℝ → ℝ) (J : ℝ → NoisePath N e → ℝ) (t : ℕ) (x : ℝ) (y : NoisePath N e)
    (a : ℝ) : ENNReal :=
  ∫⁻ y', valueENN μ Y C J (t + 1) (x + a) y' ∂(noiseKernel μ Y t (truncPath t y))

/-- **`a_t(x)` is the optimizer for `V_t(x)`**, SSRN 3742584 (Nov. 13, 2022), Lemmas 4.1–4.7,
pp.21–24: for `P_Y`-a.e. `y`, every `t = 0, …, N − 1` and every `x ≥ 0`, `a_t(x) ≥ 0` attains the
supremum in (4.11): `E_t[V_{t+1}(x + a_t(x))] − C_t(a_t(x)) ≥ E_t[V_{t+1}(x + a)] − C_t(a)` for all
`a ≥ 0`, with a finite objective at `a_t(x)`.

**Formalization Note.** `aOpt t x y` is `a_t(x)|_{Y=y}`. The inequality is written additively
in `[0, ∞]` to avoid truncated subtraction. -/
def IsOptimizer (μ : Measure Ω) [IsFiniteMeasure μ] (Y : Ω → NoisePath N e)
    (C : Fin N → ℝ → ℝ) (J : ℝ → NoisePath N e → ℝ) (aOpt : ℕ → ℝ → NoisePath N e → ℝ) :
    Prop :=
  ∀ᵐ ω ∂μ, ∀ t : ℕ, t < N → ∀ x : ℝ, 0 ≤ x →
    0 ≤ aOpt t x (Y ω) ∧ stageObjective μ Y C J t x (Y ω) (aOpt t x (Y ω)) < ⊤ ∧
    ∀ a : ℝ, 0 ≤ a →
      stageObjective μ Y C J t x (Y ω) a + ENNReal.ofReal (costAt C t (aOpt t x (Y ω))) ≤
        stageObjective μ Y C J t x (Y ω) (aOpt t x (Y ω)) + ENNReal.ofReal (costAt C t a)

/-- The cumulative effort `â₀ + … + â_{t−1}` along the feedback recursion (4.18). -/
noncomputable def feedbackCum (aOpt : ℕ → ℝ → NoisePath N e → ℝ) : ℕ → NoisePath N e → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun y => feedbackCum aOpt t y + aOpt t (feedbackCum aOpt t y) y

/-- **The feedback controls (4.18)**, SSRN 3742584 (Nov. 13, 2022), p.23: `â₀ = a₀(0)` and
`â_{t+1} = a_{t+1}(â₀ + … + â_t)` for `t = 0, …, N − 2`; `feedback aOpt t y` is `â_t` given
`Y = y` (the random variable is `feedback aOpt t (Y ω)`). -/
noncomputable def feedback (aOpt : ℕ → ℝ → NoisePath N e → ℝ) (t : ℕ) (y : NoisePath N e) : ℝ :=
  aOpt t (feedbackCum aOpt t y) y

end RelPerfMFG


