-- Prove2me | Definitions.Def_ReflectedBSDE_Existence_OptimalStopping
-- name    : ReflectedBSDE_Existence_OptimalStopping
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:13.154406+00:00
-- url     : https://prove2.me/theorems/cb744eb5-258d-41fb-992f-d307e26b4e87
-- title:
--   Proposition 2.3, p. 705 — stopping times $\mathcal T_t$, the essential supremum, and the stopping reward
-- statement:
--   Let $(\mathcal F_t)_{t\ge0}$ be a filtration on $(\Omega,\mathcal F,P)$ and $T\ge0$.
--
--   1. **Stopping times.** $\mathcal T$ is the set of all $\mathcal F_t$-stopping times dominated by $T$, and for $t\in[0,T]$
--   $$\mathcal T_t=\{v\in\mathcal T:\ t\le v\le T\}.$$
--   2. **Essential supremum.** Let $\mathcal G\subseteq\mathcal F$ be a $\sigma$-algebra and $(F_i)_{i\in I}$ a family of random variables. A random variable $X$ is the **essential supremum** of the family relative to $\mathcal G$, written $X=\operatorname{ess\,sup}_{i\in I}F_i$, if $X\ge F_i$ almost surely for every $i$, and $X\le W$ almost surely for every $\mathcal G$-measurable $W$ with $W\ge F_i$ almost surely for every $i$.
--   3. **Reward.** For processes $Y,Z,S$, a terminal value $\xi$, a coefficient $f$, a time $t$ and $v\in\mathcal T_t$, the reward of stopping at $v$ is
--   $$\int_t^v f(s,Y_s,Z_s)\,ds+S_v\mathbf 1_{\{v<T\}}+\xi\,\mathbf 1_{\{v=T\}}.$$
--
--   These objects state the optimal-stopping representation of the solution of the reflected BSDE (Proposition 2.3).
--
--   **Formalization Note** A stopping time bounded by $T$ is represented by its finite values $v:\Omega\to[0,\infty)$, and the stopping-time property is Mathlib's `IsStoppingTime` of its coercion to `WithTop ℝ≥0`. The essential supremum is a predicate on a candidate $X$, not a pointwise supremum. When the family consists of $\mathcal G$-measurable variables (conditional expectations given $\mathcal G=\mathcal F_t$), comparing only with $\mathcal G$-measurable upper bounds gives the usual essential supremum. `CondConvexRisk.Representation.EssSup` is not available in this environment, so the predicate is defined here.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 705 (PDF p. 4), Proposition 2.3, (2)

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedBSDE.Existence

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `𝒯_t = {v ∈ 𝒯 ; t ≤ v ≤ T}` (p. 705): the `𝓕`-stopping times `v` with `t ≤ v ≤ T`. A
stopping time bounded by `T` is represented by its finite values `v : Ω → [0, ∞[`. -/
def stoppingTimesBetween (𝓕 : Filtration ℝ≥0 mΩ) (t T : ℝ≥0) : Set (Ω → ℝ≥0) :=
  {v | IsStoppingTime 𝓕 (fun ω => (v ω : WithTop ℝ≥0)) ∧ ∀ ω, t ≤ v ω ∧ v ω ≤ T}

/-- `X` is the essential supremum of the family `(F i)_{i ∈ I}` of random variables, relative to
the σ-algebra `m` (the family consists of `m`-measurable variables): `X ≥ F i` almost surely for
every `i`, and `X ≤ W` almost surely for every `m`-measurable `W` with `W ≥ F i` almost surely for
every `i`. -/
def IsEssSupOver {ι : Type*} (P : Measure Ω) (m : MeasurableSpace Ω) (F : ι → Ω → ℝ)
    (X : Ω → ℝ) : Prop :=
  (∀ i, F i ≤ᵐ[P] X) ∧
    ∀ W : Ω → ℝ, StronglyMeasurable[m] W → (∀ i, F i ≤ᵐ[P] W) → X ≤ᵐ[P] W

/-- The reward of stopping at `v` in Proposition 2.3 (p. 705), seen from time `t`:
`∫ₜᵛ f(s, Y_s, Z_s) ds + S_v 1_{v<T} + ξ 1_{v=T}`. -/
noncomputable def stoppingReward {d : ℕ} (T : ℝ≥0) (ξ : Ω → ℝ)
    (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → ℝ)
    (Z : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0) (v : Ω → ℝ≥0) (ω : Ω) : ℝ :=
  (∫ s in Icc (t : ℝ) (v ω), f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω))
    + (if v ω < T then S (v ω) ω else 0) + (if v ω = T then ξ ω else 0)

end ReflectedBSDE.Existence


