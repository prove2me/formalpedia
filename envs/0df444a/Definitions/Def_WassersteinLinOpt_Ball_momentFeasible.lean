-- Prove2me | Definitions.Def_WassersteinLinOpt_Ball_momentFeasible
-- name    : WassersteinLinOpt_Ball_momentFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T16:23:03.566737+00:00
-- url     : https://prove2.me/theorems/5d1def6b-6340-4933-9c1e-b31783c511ed
-- title:
--   Feasible region $\mathcal F$ of the moment problem (11)
-- statement:
--   Let $Z$ be a topological space with its Borel $\sigma$-algebra, $m\in\mathbb N$, $\varphi_1,\dots,\varphi_m:Z\to\mathbb R$ Borel functions and $v\in\mathbb R^m$. Problem (11) is
--
--   $$\text{maximize}_\gamma\ \int_Z\psi(z)\,d\gamma(z)\quad\text{s.t.}\quad\gamma\in\mathcal M_+(Z),\ \ \int_Z\varphi_i(z)\,d\gamma(z)=v_i\ \ (i=1,\dots,m),$$
--
--   where $\mathcal M_+(Z)$ is the set of non-negative finite Borel measures on $Z$. Its feasible region $\mathcal F$ is the set of $\gamma\in\mathcal M_+(Z)$ satisfying the $m$ moment constraints.
--
--   **Formalization Note.** A constraint $\int\varphi_i\,d\gamma=v_i$ with $v_i$ real requires the integral to exist and be finite, so `momentFeasible φ v` requires `IsFiniteMeasure γ`, `Integrable (φ i) γ` and `∫ z, φ i z ∂γ = v i` for each `i`. Without the integrability clause, the Bochner integral's value `0` on non-integrable functions would make spurious measures feasible whenever `v i = 0`.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1120, problem (11)

import Mathlib

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- The feasible region `𝓕` of problem (11), p. 1120: the non-negative finite Borel measures
`γ ∈ ℳ₊(Z)` with `∫_Z φ_i(z) dγ(z) = v_i` for all `i = 1, …, m`. Since `v_i` is a real number,
the paper's constraint requires `∫_Z φ_i dγ` to exist and be finite; this is written as
`Integrable (φ i) γ` so that the Bochner integral's junk value `0` on non-integrable functions
cannot make a measure feasible. -/
def momentFeasible {Z : Type*} [MeasurableSpace Z] {m : ℕ} (φ : Fin m → Z → ℝ)
    (v : Fin m → ℝ) : Set (Measure Z) :=
  {γ | IsFiniteMeasure γ ∧ ∀ i, Integrable (φ i) γ ∧ ∫ z, φ i z ∂γ = v i}

end WassersteinLinOpt.Ball


