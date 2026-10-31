-- Prove2me | Definitions.Def_DeltaSLearning_IsDemandProcess
-- name    : DeltaSLearning_IsDemandProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:43.305986+00:00
-- url     : https://prove2.me/theorems/2456662d-5a0d-459c-becb-47966bc5194b
-- title:
--   Assumption 1: i.i.d. demands with density bounded by $\rho$
-- statement:
--   A sequence of real random variables $D_0,D_1,\dots$ on a probability space $(\Omega,P)$ satisfies Assumption 1 with constant $\rho$ if the $D_t$ are measurable, mutually independent and identically distributed, and their common law has a Lebesgue density $f$ with $f\le\rho$ that vanishes on $(-\infty,0)$:
--   $$P\circ D_0^{-1}\ \le\ \rho\cdot\mathrm{Leb}|_{[0,\infty)} .$$
--
--   This is the only probabilistic assumption of the paper: no moment of the demand is assumed.
--
--   **Formalization Note** Periods are 0-based: $D_t$ is the demand of the paper's period $t+1$. The paper bounds $f$ on $d\ge0$; the measure inequality also puts the law on $[0,\infty)$, i.e. demands are nonnegative, as Lemma 2 ("positive") and the proof of Lemma 3 use. The probability measure is an instance argument of each theorem.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Assumption 1, p.9; §2, p.7

import Mathlib

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- Assumption 1: the demands `D 0, D 1, …` are i.i.d. and their common law has a density
bounded by `ρ` and supported on `[0, ∞)`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Assumption 1, p.9, and §2 p.7 ("i.i.d. continuous random variables").

**Formalization Note** Periods are 0-based: `D t` is the demand of the paper's period `t + 1`.
The density condition is encoded as `P.map (D 0) ≤ ρ • volume.restrict [0, ∞)`, which holds
exactly when the law of `D 0` has a Lebesgue density `f` with `f ≤ ρ` a.e. and `f = 0` on
`(-∞, 0)`. The paper bounds `f` only on `d ≥ 0`; demands are nonnegative (Lemma 2 calls them
"positive"). No moment of the demand is assumed, as in the paper. The probability measure is a
separate instance argument of each theorem. -/
def IsDemandProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℕ → Ω → ℝ)
    (ρ : ℝ) : Prop :=
  (∀ t, Measurable (D t)) ∧ iIndepFun D P ∧ (∀ t, IdentDistrib (D t) (D 0) P P) ∧
    P.map (D 0) ≤ ENNReal.ofReal ρ • volume.restrict (Set.Ici (0 : ℝ))

end DeltaSLearning


