-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_value
-- name    : KallMayerSLP_Multistage_value
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:16:20.533607+00:00
-- url     : https://prove2.me/theorems/c8cde5c8-ff1b-4cfe-8fd0-a0a43ffb18ab
-- title:
--   Optimal value $\hat V$ of (3.10)
-- statement:
--   The optimal value $\hat V$ of problem (3.10) is the infimum of the objective over all feasible policies.
--
--   **Formalization Note** The book's $\min$ is an infimum in the extended reals: $+\infty$ if there is no feasible policy, $-\infty$ if the problem is unbounded.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.10), p.261 (PDF 270)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_IsFeasiblePolicy
import Definitions.Def_KallMayerSLP_Multistage_objective

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- The optimal value `V̂` of problem (3.10) (Kall & Mayer, *Stochastic Linear Programming* (2005),
Chapter 3, (3.10), p.261, PDF 270).

**Formalization Note.** The book's `min` is an infimum in `EReal` over the feasible policies:
`+∞` if there is no feasible policy, `-∞` if the problem is unbounded. No real `sInf` junk value is
involved. -/
noncomputable def value (D : MSLP) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : ∀ t, Ω → Fin (D.r t) → ℝ) : EReal :=
  ⨅ (x : ∀ t, Hist D.r t → Fin (D.n t) → ℝ) (_ : IsFeasiblePolicy D P ξ x),
    ((objective D P ξ x : ℝ) : EReal)

end KallMayerSLP.Multistage


