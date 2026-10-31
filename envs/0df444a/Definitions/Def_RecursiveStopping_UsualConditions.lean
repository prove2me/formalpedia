-- Prove2me | Definitions.Def_RecursiveStopping_UsualConditions
-- name    : RecursiveStopping_UsualConditions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:49.359439+00:00
-- url     : https://prove2.me/theorems/6d92d5d2-f34c-4ef3-b8aa-1d7d5956a205
-- title:
--   Usual conditions: right-continuous, complete filtration with $\mathcal F_\infty=\mathcal F$
-- statement:
--   Let $(\Omega,\mathcal F,\mathsf P)$ be a probability space and $\mathbb F=(\mathcal F_t)_{t\ge0}$ a filtration. The pair satisfies the **standing conditions** of the paper when
--
--   1. $\mathbb F$ is right-continuous: $\mathcal F_t=\bigcap_{s>t}\mathcal F_s$ for every $t\ge0$;
--   2. $\mathbb F$ is complete: every $\mathsf P$-null set (every set of outer measure $0$) belongs to $\mathcal F_0$;
--   3. $\mathcal F_\infty:=\bigvee_{t\ge0}\mathcal F_t$ is the whole $\sigma$-algebra $\mathcal F$.
--
--   These are the conditions under which stopping times, entry times and optional sampling behave as in the general theory of optimal stopping; every result of the mission is stated on such a filtered probability space.
--
--   **Formalization Note** Time is indexed by $[0,\infty)$ (`ℝ≥0`); right-continuity is Mathlib's `Filtration.IsRightContinuous`.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, §2, p.5

import Mathlib

open MeasureTheory
open scoped NNReal

namespace RecursiveStopping

/-- The standing conditions on the filtered probability space of Colaneri & De Angelis,
arXiv:1905.02650v4, §2, p.5: "We fix a probability space `(Ω, F, P)` endowed with a
right-continuous and complete filtration `F = (F_t)_{t≥0}` with `F_∞ = ⋁_{t≥0} F_t =: F`."

`UsualConditions P 𝔽` asserts:
1. `𝔽` is right-continuous (Mathlib's `Filtration.IsRightContinuous`, `F_t = ⋂_{s>t} F_s`);
2. `𝔽` is complete: every `P`-null set (outer measure zero, measurable or not) lies in `F_0`;
3. the ambient σ-algebra is `F_∞ = ⋁_{t≥0} F_t`.

**Formalization Note** Time is indexed by `ℝ≥0`. -/
def UsualConditions {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ≥0 mΩ) : Prop :=
  𝔽.IsRightContinuous ∧ (∀ s : Set Ω, P s = 0 → MeasurableSet[𝔽 0] s) ∧ (⨆ t, 𝔽 t) = mΩ

end RecursiveStopping


