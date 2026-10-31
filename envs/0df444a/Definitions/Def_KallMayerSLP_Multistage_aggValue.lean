-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_aggValue
-- name    : KallMayerSLP_Multistage_aggValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:19:44.250262+00:00
-- url     : https://prove2.me/theorems/5e77e25a-0c67-46c7-9ffe-5dcc09864f9a
-- title:
--   Optimal value of the aggregated problem (3.14)
-- statement:
--   The optimal value of the fully aggregated problem (3.14) for a scenario tree is the infimum of its objective over its feasible points.
--
--   **Formalization Note** An infimum in the extended reals: $+\infty$ if (3.14) is infeasible, $-\infty$ if it is unbounded.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.14), p.263 (PDF 272)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_IsAggFeasible
import Definitions.Def_KallMayerSLP_Multistage_aggObjective

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- The optimal value of the fully aggregated problem (3.14) (Kall & Mayer, *Stochastic Linear
Programming* (2005), Chapter 3, (3.14), p.263, PDF 272), for the scenario tree `𝒯`.

**Formalization Note.** An infimum in `EReal`: `+∞` if (3.14) is infeasible, `-∞` if unbounded. -/
noncomputable def aggValue {D : MSLP} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)} (𝒯 : ScenarioTree D Ξ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ∀ t, Ω → Fin (D.r t) → ℝ) : EReal :=
  ⨅ (X : ∀ t, 𝒯.Node t → Fin (D.n t) → ℝ) (_ : IsAggFeasible 𝒯 P ξ X),
    ((aggObjective 𝒯 P ξ X : ℝ) : EReal)

end KallMayerSLP.Multistage


