-- Prove2me | Definitions.Def_ConsistentBanditPolicy
-- name    : ConsistentBanditPolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-19T18:22:30.25162+00:00
-- url     : https://prove2.me/theorems/e8d8f3e4-74cd-4e13-a492-904acb5460db
-- statement:
--   A policy $\pi$ is consistent over a class of bandits $\mathcal{E}$ if for all $\nu \in \mathcal{E}$ and all $p > 0$,
--
--   $$\lim_{n\to\infty} \frac{R_n(\pi,\nu)}{n^p} = 0.$$
--
--   Also defines
--
--   $$d_{\inf}(P, \mu^*, \mathcal{M}) = \inf_{P'\in\mathcal{M}}\{D(P,P') : \mu(P') > \mu^*\}.$$
-- source:
--   L&S Definition 16.1 and d_inf, p.207

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Definitions.Def_banditRegret

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapter 16, p.207:

* Definition 16.1: a policy `π` is *consistent* over a class of bandits `𝓔`
  if for all `ν ∈ 𝓔` and all `p > 0`, `R_n(π, ν) / n^p → 0`.
* The minimal informational cost of making an arm optimal:
  `d_inf(P, μ*, 𝓜) = inf { D(P, P') : P' ∈ 𝓜, μ(P') > μ* }`
  (value in `ℝ≥0∞`; the infimum of the empty set is `∞`, matching the book).
-/

open MeasureTheory ProbabilityTheory Filter ENNReal

namespace BanditAlgorithm

/-- Definition 16.1: `π` is consistent over the class `𝓔` if its regret is
subpolynomial on every instance of the class. -/
def IsConsistentPolicy {k : ℕ} (𝓔 : Set (StochasticBandit k))
    (π : BanditPolicy k) : Prop :=
  ∀ ν ∈ 𝓔, ∀ p : ℝ, 0 < p →
    Tendsto (fun n : ℕ ↦ banditRegret ν π n / (n : ℝ) ^ p) atTop (nhds 0)

/-- `d_inf(P, μ*, 𝓜)`: the least relative entropy from `P` to a distribution
in `𝓜` whose mean exceeds `μ*` (L&S p.207). -/
noncomputable def banditDInf (𝓜 : Set (Measure ℝ)) (P : Measure ℝ)
    (μstar : ℝ) : ℝ≥0∞ :=
  ⨅ P' ∈ {Q ∈ 𝓜 | μstar < ∫ x, x ∂Q}, InformationTheory.klDiv P P'

end BanditAlgorithm


