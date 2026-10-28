-- Prove2me | Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceHarmonic
-- name    : CountingMatroid_Analysis_PositiveTimeTraceHarmonic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:08:56.033272+00:00
-- url     : https://prove2.me/theorems/078131a2-78b1-4c8c-874c-b10b5346fcb4
-- title:
--   Uncapped hitting weights and harmonic extension
-- statement:
--   Let $\Omega$ be finite, let $P$ be a Markov chain on $\Omega$, and let $A\subseteq\Omega$. If $H_k(x,y)$ is the subkernel for hitting $A$ within $k$ transitions, including a time-zero hit, define
--   $$
--   H_\infty(x,y)=\sup_{k\in\mathbb N}H_k(x,y),\qquad
--   \widetilde h(x)=\sum_{y\in\Omega}H_\infty(x,y)h(y)
--   $$
--   for any real function $h:\Omega\to\mathbb R$. The second expression is the canonical extension formed from hitting weights. The definition uses unnormalized hitting mass; it assumes neither almost-sure hitting from every state nor a stationary distribution. Harmonicity is a property to be established separately.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PositiveTimeTraceHarmonic.lean#L31-L34

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

namespace Arlib
end Arlib
namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
section


set_option autoImplicit false

/-!
Harmonic extension for the concrete positive-time return subkernel. The
extension uses the increasing finite hitting kernels, so the first-step
identities do not assume almost-sure hitting from zero-weight states.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceHarmonic

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]





/-- INTERNAL: The uncapped zero-time hitting array, including immediate hits.
TEXLINE: main.tex:1047-1053 -/
noncomputable def uncappedHit (P : FinChain Ω) (A : Finset Ω) (x y : Ω) : ℝ :=
  ⨆ k, (hitWithin P A k).entry x y











/-- INTERNAL: Canonical harmonic extension obtained from uncapped hitting.
TEXLINE: main.tex:1047-1053 -/
noncomputable def harmonicExtension (P : FinChain Ω) (A : Finset Ω)
    (h : Ω → ℝ) (x : Ω) : ℝ := ∑ y, uncappedHit P A x y * h y











end CountingMatroid.Analysis.PositiveTimeTraceHarmonic

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · monotone hitting limits give the harmonic residual and boundary energy identity; symmetry proves trace detailed balance, and one-step returns preserve holding probabilities. No almost-sure-hitting assumption on zero-weight states is needed.
-/

end


