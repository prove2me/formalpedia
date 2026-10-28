-- Prove2me | Definitions.Def_CountingMatroid_Analysis_CappedReturnSubstationary
-- name    : CountingMatroid_Analysis_CappedReturnSubstationary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:09:06.313292+00:00
-- url     : https://prove2.me/theorems/0d6c28a7-30dc-4fe1-acc2-47c388a8453d
-- title:
--   Flow killed upon departure from a target
-- statement:
--   Let $\Omega$ be a finite state space, let $P$ be a stochastic transition matrix on $\Omega$, let $A\subseteq\Omega$, and let $\lambda:\Omega\to\mathbb R$ be any initial function, possibly signed. The killed-flow sequence is
--   $$
--   f_0(x)=\lambda(x),\qquad
--   f_{k+1}(y)=\sum_{x\in\Omega\setminus A}f_k(x)P(x,y).
--   $$
--   The natural number $k$ counts transitions. Mass arriving in $A$ appears in that layer but does not propagate to the next layer. No normalization or nonnegativity of $\lambda$ is required by this definition.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/CappedReturnSubstationary.lean#L19-L25

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Topology.Order.MonotoneConvergence

namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib
end Arlib
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
section


set_option autoImplicit false

/-!
Capped positive-time returns started from the stationary law restricted to
the target never put more mass on a target state than the stationary law
does. Iterating, any start dominated by a multiple of the restricted
stationary law stays dominated through every number of capped returns.
Lost (capped) mass is retained as a deficit, not renormalised.
-/
namespace CountingMatroid.Analysis.CappedReturnSubstationary

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: Mass flowing through off-target states, one underlying step at a
time, killed as soon as it reaches the target.
TEXLINE: main.tex:1072-1087 -/
noncomputable def killedFlow (P : FinChain Ω) (A : Finset Ω) (lam : Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => lam
  | s + 1 => fun w => ∑ z, (if z ∈ A then 0 else killedFlow P A lam s z) * P z w











end CountingMatroid.Analysis.CappedReturnSubstationary

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · killed-flow decomposition of finite hitting, cumulative flow bound by stationarity, capped-return sub-stationarity and its iterated domination form.
-/

end


