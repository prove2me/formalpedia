-- Prove2me | Definitions.Def_NesterovSSAAudit_SSA_randomExecution
-- name    : NesterovSSAAudit_SSA_randomExecution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:42:17.204979+00:00
-- url     : https://prove2.me/theorems/eecdea66-fa03-4947-ade9-94db9dcd61af
-- title:
--   Finite iid history laws, admissible random executions and population cost
-- statement:
--   Let $\mu$ be a measure on an arbitrary measurable sample space $\Xi$. For each $n\ge0$, the history law is the finite product $\mu^{\otimes n}$ on $\Xi^n$. For the canonical state maps computed from $\pi,\gamma,x_0,a$, an admissible random execution means
--
--   $$h\mapsto x_n(h)\text{ and }h\mapsto s_n(h)\text{ are a.e. measurable under }\mu^{\otimes n}\quad\text{for every }n.$$
--
--   Both target spaces carry their norm Borel structures. Ordinary measurable history states satisfy this condition; the a.e. formulation also admits completed representatives. The predicate imposes no condition on oracle values at unqueried points and contains no independence or integrability assumption and no target identity or inequality.
--
--   For a real cost $f$, the population objective is defined by
--
--   $$\varphi(x)=\int_\Xi f(x,\xi)\,d\mu(\xi).$$
--
--   The theorem statements separately require a probability law and the source's finite integrability of every fixed feasible cost section. Adaptive integrability is asserted in their conclusions. This layer spells out the random vectors on p.26 and the objective in (6.1).
-- source:
--   Yu. Nesterov, Primal-dual subgradient methods for convex problems, September 2005 revised manuscript, SHA256 095a7bfedc1ebd85f8fbd9e7765194e180a95c38fdfbef172ecd27cbe920f96c, p.25–27, (6.1), random vectors after (6.3), Theorem 7

import Mathlib
import Definitions.Def_NesterovSSAAudit_SSA_historyStates

set_option autoImplicit false

namespace NesterovSSAAudit.SSA

open MeasureTheory

variable {E Ξ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Ξ]

/-- Independent sampling on histories of exactly n observations; n=0 is the empty history. -/
noncomputable def historyLaw (μ : Measure Ξ) (n : ℕ) : Measure (Fin n → Ξ) :=
  Measure.pi fun _ : Fin n => μ

/-- The actual two state maps are random vectors under every finite history law (p.26).
Borel structures are fixed by the norms. A.e. measurability allows completed representatives.
This contains no integrability, independence, expectation identity or accuracy assumptions. -/
def IsRandomExecution (μ : Measure Ξ) (π : ℝ → StrongDual ℝ E → E)
    (γ : ℝ) (x0 : E) (a : E → Ξ → StrongDual ℝ E) : Prop :=
  letI : MeasurableSpace E := borel E
  letI : MeasurableSpace (StrongDual ℝ E) := borel (StrongDual ℝ E)
  ∀ n : ℕ,
    AEMeasurable (fun h => (historyState π γ x0 a n h).1) (historyLaw μ n) ∧
    AEMeasurable (fun h => (historyState π γ x0 a n h).2) (historyLaw μ n)

/-- Population objective (6.1). Theorems require integrability of every feasible section. -/
noncomputable def population (μ : Measure Ξ) (f : E → Ξ → ℝ) (x : E) : ℝ :=
  ∫ ξ, f x ξ ∂μ

end NesterovSSAAudit.SSA


