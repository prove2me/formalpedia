-- Prove2me | Definitions.Def_CountingMatroid_Analysis_StationaryPathMoment
-- name    : CountingMatroid_Analysis_StationaryPathMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:06:26.011987+00:00
-- url     : https://prove2.me/theorems/f44bfc02-005c-42a3-be5a-3107bf22802e
-- title:
--   Finite-path weights and the second moment of an observation sum
-- statement:
--   Let $\Omega$ be finite, let $P$ be a Markov kernel on $\Omega$, let $\pi$ be a probability distribution, and let $g:\Omega\to\mathbb R$. For a path $x=(x_0,\ldots,x_N)$ with $N$ transitions, define
--   $$w_P(x)=\prod_{i=0}^{N-1}P(x_i,x_{i+1}),\qquad
--   S_g(x)=\sum_{i=0}^{N-1}g(x_i).$$
--   There are $N$ observations, at the first $N$ vertices; the final vertex is not observed. The path second moment is
--   $$M_2(\pi,P,g,N)=
--   \sum_{x\in\Omega^{N+1}}\pi(x_0)\,w_P(x)\,S_g(x)^2.$$
--   The observation sum is neither centered nor divided by $N$. These definitions apply without assuming that $\pi$ is stationary or that $g$ has mean zero.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StationaryPathMoment.lean#L18-L21

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace Arlib
end Arlib
section


set_option autoImplicit false

/-!
Finite product-path expectations and moments. The last transition is unused
by the observations, matching the stationary observation experiment.
-/
namespace CountingMatroid.Analysis.StationaryPathMoment

open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

variable {Ω : Type} [Fintype Ω]

/-- INTERNAL: Product weight of a path with N transitions. -/
noncomputable def pathWeight (P : FinChain Ω) (N : ℕ)
    (path : Fin (N + 1) → Ω) : ℝ :=
  ∏ i : Fin N, P (path i.castSucc) (path i.succ)

/-- INTERNAL: The N observations at the first N vertices of a path. -/
noncomputable def observationSum (g : Ω → ℝ) (N : ℕ)
    (path : Fin (N + 1) → Ω) : ℝ :=
  ∑ i : Fin N, g (path i.castSucc)











/-- INTERNAL: Unnormalised second moment of the sum of N observations. -/
noncomputable def pathSquaredSum (π : FinDist Ω) (P : FinChain Ω)
    (g : Ω → ℝ) (N : ℕ) : ℝ :=
  ∑ path : Fin (N + 1) → Ω,
    π (path 0) * pathWeight P N path * (observationSum g N path) ^ 2







end CountingMatroid.Analysis.StationaryPathMoment

end


