-- Prove2me | Definitions.Def_CountingMatroid_Analysis_StationaryReturnOccupation
-- name    : CountingMatroid_Analysis_StationaryReturnOccupation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:08:57.720807+00:00
-- url     : https://prove2.me/theorems/f7031fad-0202-47a4-a166-0f6db18108b9
-- title:
--   Finite positive-time return occupation
-- statement:
--   Let $\Omega$ be finite with decidable equality, $P$ stochastic, $A\subseteq\Omega$, $\mu$ a probability distribution, and $H\in\mathbb N$. Let $s_k(z)$ be the probability of avoiding $A$ at times $0,\ldots,k$ from $z$, with $s_0=\mathbf1_{\Omega\setminus A}$. Define
--   $$O_H=\sum_{x\in A}\mu(x)+\sum_{k=0}^{H-1}\sum_{x\in A}\mu(x)\sum_zP(x,z)s_k(z).$$
--   The initial term counts the first positive-time attempted transition; later terms are survival tails. There is no division by $\mu(A)$ and no stationarity or positive-target-mass assumption in this definition. Those conditions may be needed for later identities or conditional interpretations.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StationaryReturnOccupation.lean#L18-L26

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
Finite occupation bounds for positive-time returns. The first attempted step
is counted separately from the subsequent survival tails. Stationarity makes
the tails telescope, so neither irreducibility nor an infinite-expectation
interchange is needed. Operational finite-tape coupling is not asserted here.
-/
namespace CountingMatroid.Analysis.StationaryReturnOccupation

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: The stationary target mass plus the next H positive-time
survival tails, before dividing by target mass to condition the starting law.
The target mass counts the first attempted transition even on an immediate
return or a draw abort.
TEXLINE: main.tex:1072-1087 -/
noncomputable def returnOccupation (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (H : ℕ) : ℝ :=
  (∑ x ∈ A, μ x) + ∑ k ∈ Finset.range H,
    ∑ x, if x ∈ A then μ x * (∑ z, P x z * survive P A k z) else 0





end CountingMatroid.Analysis.StationaryReturnOccupation

end


