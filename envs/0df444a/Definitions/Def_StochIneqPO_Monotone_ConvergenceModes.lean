-- Prove2me | Definitions.Def_StochIneqPO_Monotone_ConvergenceModes
-- name    : StochIneqPO_Monotone_ConvergenceModes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:10:16.966521+00:00
-- url     : https://prove2.me/theorems/496a5a2a-fdde-45c2-9ee3-94776c704227
-- title:
--   Theorem 6 (i)–(iv), p. 908 — tightness, weak convergence, convergence in probability and a.s. convergence of a random sequence
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a measure space (a probability space in all uses), let $E$ be a topological space with its Borel $\sigma$-algebra, and let $X_1,X_2,\dots:\Omega\to E$ be random elements of $E$ with distributions $P_i=\mu\circ X_i^{-1}$. This file defines the four modes of convergence of Theorem 6:
--
--   1. **(i) tightness**: the family $\{P_i : i\ge 1\}$ is tight, i.e. for every $\varepsilon>0$ there is a compact $K\subseteq E$ with $P_i(E\setminus K)\le\varepsilon$ for all $i$;
--   2. **(ii) weak convergence to a probability measure**: there is a probability measure $P$ on $E$ with
--   $$
--   \int_E f\,dP_i\;\longrightarrow\;\int_E f\,dP\qquad (i\to\infty)
--   $$
--   for every bounded continuous $f:E\to\mathbb R$;
--   3. **(iii) convergence in probability** (for $E$ a metric space with metric $d$): there is a measurable $Y:\Omega\to E$ such that $\mu\{\omega : d(X_i(\omega),Y(\omega))\ge\varepsilon\}\to 0$ for every $\varepsilon>0$;
--   4. **(iv) almost sure convergence**: there is $Y:\Omega\to E$ such that $X_i(\omega)\to Y(\omega)$ for $\mu$-almost every $\omega$.
--
--   These are the standard notions; they are collected here so that the statement of Theorem 6 and its proof steps can refer to them by name.
--
--   **Formalization Note** Tightness is Mathlib's `IsTightMeasureSet` applied to the range of $i\mapsto P_i$. Weak convergence is stated through integrals of bounded continuous functions, which is equivalent to convergence in Mathlib's topology on probability measures whenever the $X_i$ are measurable and $\mu$ is a probability measure (as in every theorem of the mission). Convergence in probability is Mathlib's `TendstoInMeasure`, written with the extended distance, which on a metric space is $d$; the limit is required to be measurable, i.e. a random variable. The a.s. limit in (iv) is not required to be measurable: a.s. convergence only asks that the sequence converge for almost every $\omega$.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Theorem 6 (i)–(iv), p. 908 (PDF p. 10)

import Mathlib

namespace StochIneqPO.Monotone

open MeasureTheory Filter Topology BoundedContinuousFunction

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Theorem 6 (i), p. 908: the family of distributions `Pᵢ = μ ∘ Xᵢ⁻¹`, `i ≥ 1`, is tight. -/
def LawsTight [TopologicalSpace E] (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  IsTightMeasureSet (Set.range fun i => μ.map (X i))

/-- Theorem 6 (ii), p. 908: the distributions `Pᵢ = μ ∘ Xᵢ⁻¹` converge weakly to a probability
measure `P`, i.e. `∫ f dPᵢ → ∫ f dP` for every bounded continuous `f : E → ℝ`. -/
def LawsConvergeWeakly [TopologicalSpace E] (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∃ P : ProbabilityMeasure E, ∀ f : E →ᵇ ℝ,
    Tendsto (fun i => ∫ x, f x ∂(μ.map (X i))) atTop (𝓝 (∫ x, f x ∂(P : Measure E)))

/-- Theorem 6 (iii), p. 908: `Xᵢ` converges in probability to a measurable random variable `Y`:
for every `ε > 0`, `μ {ω | d(Xᵢ ω, Y ω) ≥ ε} → 0`. -/
def ConvergesInProbability [PseudoMetricSpace E] (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∃ Y : Ω → E, Measurable Y ∧ TendstoInMeasure μ X atTop Y

/-- Theorem 6 (iv), p. 908: `Xᵢ` converges almost surely: for `μ`-almost every `ω` the sequence
`Xᵢ ω` converges in `E` (to `Y ω`). -/
def ConvergesAS [TopologicalSpace E] (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∃ Y : Ω → E, ∀ᵐ ω ∂μ, Tendsto (fun i => X i ω) atTop (𝓝 (Y ω))

end StochIneqPO.Monotone


