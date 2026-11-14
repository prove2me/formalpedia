-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FiniteProbability
-- name    : ConsistentSubmodular_Deterministic_Reduction_FiniteProbability
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:06:32.032519+00:00
-- url     : https://prove2.me/theorems/1e5321e3-8a68-4ba2-98c9-57ee6952bab2
-- title:
--   Finite probability laws: weights, expectation and probability of an event
-- statement:
--   For a finite type $\Omega$:
--
--   - `ConsistentSubmodular.FiniteLaw` $\Omega$: a probability law on $\Omega$ given by weights $\mu(\omega)\in\mathbb{R}$ with $\mu(\omega) \ge 0$ for all $\omega$ and $\sum_{\omega}\mu(\omega)=1$.
--   - `FiniteLaw.expect` $(\mu, X)$: the expectation of a real function $X:\Omega\to\mathbb{R}$,
--   $$\mathbb{E}_\mu[X]=\sum_{\omega\in\Omega}\mu(\omega)\,X(\omega).$$
--   - `FiniteLaw.probability` $(\mu, E)$: the probability of an event $E\subseteq\Omega$ (a predicate on $\Omega$),
--   $$\Pr_\mu[E]=\sum_{\omega\in E}\mu(\omega).$$
--
--   Finite laws make all probabilistic arguments of the deterministic part elementary sums over finite sets, with no measure theory. They are the basis of the sampling, rounding and shared-threshold constructions that realize mixtures $H_j(p)$ by explicit finite experiments (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/FiniteProbability.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonnegative : ∀ ω, 0 ≤ weight ω
  sum_one : (∑ ω, weight ω) = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

def expect (X : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * X ω

def probability (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then μ.weight ω else 0

end FiniteLaw

end ConsistentSubmodular

end


