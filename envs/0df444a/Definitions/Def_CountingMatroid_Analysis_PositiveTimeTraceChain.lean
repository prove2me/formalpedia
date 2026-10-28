-- Prove2me | Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceChain
-- name    : CountingMatroid_Analysis_PositiveTimeTraceChain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:09:46.012103+00:00
-- url     : https://prove2.me/theorems/710a2b8b-00b0-4817-aafc-ead3a996a303
-- title:
--   Boundary conditioning and positive-time trace chains
-- statement:
--   Let $\Omega$ be finite with decidable equality and $A\subseteq\Omega$. The supplied sum lemma says that a real function $f$ vanishing off $A$ satisfies
--   $$\sum_{x\in\Omega}f(x)=\sum_{x\in A}f(x).$$
--   For a probability distribution $\mu$ with $\mu(A)>0$, define the distribution on the subtype $A$ by
--   $$\mu_A(x)=\frac{\mu(x)}{\mu(A)},\qquad \mu(A)=\sum_{z\in A}\mu(z).$$
--   Separately, let $P$ be stochastic, assume $\mu P=\mu$, and assume $\mu(x)>0$ at every $x\in A$. The trace-chain constructor restricts the uncapped positive-time first-return kernel to $A$:
--   $$P_A(x,y)=\Pr_x(X_{T_A^+}=y),\qquad T_A^+=\inf\{t\ge1:X_t\in A\}.$$
--   Almost-sure return at these positive-mass boundary states makes its rows sum to one. This is not all-stream return or termination. The law constructor requires positive total boundary mass; the chain constructor instead explicitly requires pointwise boundary positivity.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PositiveTimeTraceChain.lean#L18-L27

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceHarmonic
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
The concrete uncapped positive-time trace as a finite stochastic chain on its
boundary. Its law is the conditional underlying stationary law, and finite
powers agree with the previously constructed return subkernel iterates.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceChain

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.PositiveTimeTraceHarmonic

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: Rewrite a full finite sum supported on a boundary as its
subtype sum. This retains zero mass outside the trace state space. -/
theorem sum_on_target (A : Finset Ω) (f : Ω → ℝ)
    (hf : ∀ x, x ∉ A → f x = 0) :
    (∑ x, f x) = ∑ x : A, f x := by
  rw [← Finset.sum_subtype A (fun _ => Iff.rfl)]
  symm
  apply Finset.sum_subset (Finset.subset_univ A)
  intro x _ hx
  exact hf x hx

/-- INTERNAL: Restrict the underlying stationary law to a positive-mass
boundary and normalize it, giving the paper's transversal law.
TEXLINE: main.tex:1023-1037 -/
noncomputable def traceLaw (μ : FinDist Ω) (A : Finset Ω)
    (hA : 0 < ∑ x ∈ A, μ x) : FinDist A where
  p x := μ x / (∑ z ∈ A, μ z)
  p_nonneg x := div_nonneg (μ.coe_nonneg x) hA.le
  p_sum := by
    rw [← Finset.sum_div, ← Finset.sum_subtype A (fun _ => Iff.rfl)]
    exact div_self hA.ne'

/-- INTERNAL: Almost-sure return at positive stationary boundary states
makes the concrete return kernel stochastic on the boundary subtype.
TEXLINE: main.tex:1023-1037 -/
noncomputable def traceChain (μ : FinDist Ω) (P : FinChain Ω)
    (hstationary : Stationary μ P) (A : Finset Ω)
    (hμ : ∀ x ∈ A, 0 < μ x) : FinChain A where
  P x y := (uncappedReturn P A).entry x y
  P_nonneg x y := (uncappedReturn P A).nonneg x y
  P_sum x := by
    rw [← sum_on_target A (fun y => (uncappedReturn P A).entry x y)
      (fun y hy => uncappedReturn_supported P A x y hy)]
    exact uncappedReturn_mass_eq_one P A μ hstationary x x.property (hμ x x.property)









end CountingMatroid.Analysis.PositiveTimeTraceChain

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · constructed the stochastic trace on the boundary subtype, its reversible conditional law, holding probability, exact finite-power bridge, and harmonic-extension energy scaling.
-/

end


