-- Prove2me | Definitions.Def_TotalVariationDist
-- name    : TotalVariationDist
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-15T14:35:14.170913+00:00
-- url     : https://prove2.me/theorems/c78cc7fb-5605-4d72-b13d-f1f13221dbe6
-- title:
--   Total variation distance $\|\mu-\nu\| = \sup_A |\mu(A)-\nu(A)|$
-- statement:
--   The total variation distance between two measures $\mu$ and $\nu$ on a measurable space $\mathsf{X}$, in the normalization standard in Markov chain theory:
--
--   $$
--   \|\mu - \nu\| \;=\; \sup_{A} \, |\mu(A) - \nu(A)|,
--   $$
--
--   the supremum ranging over all measurable sets $A \subseteq \mathsf{X}$. For probability measures it takes values in $[0, 1]$ and equals one half of the total variation norm of the signed measure $\mu - \nu$.
--
--   This is the distance in which every convergence-to-equilibrium statement of the mission is expressed; it applies to any pair of measures on any measurable space and is reusable far beyond this mission.
--
--   **Formalization Note** The distance is a real number defined as the supremum of the (nonempty, and for probability measures bounded) set of values $|\mu(A) - \nu(A)|$; it is only ever applied to probability measures in this mission.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 2 (arXiv v2 p. 3), the norm of eqs. (2)-(3)

import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
Total variation distance between measures, in the Markov-chain-theory
normalization.

Source: Galin L. Jones, *On the Markov Chain Central Limit Theorem*,
Probability Surveys 1 (2004) 299-320 (arXiv math/0409112v2), §2: the norm
`‖·‖` appearing in eqs. (2)-(3).
-/

namespace MarkovChainCLT

/-- **Total variation distance** between two measures, in the Markov-chain-theory
normalization: `tvDist μ ν = sup_A |μ(A) - ν(A)|` over measurable sets `A`.
For probability measures this lies in `[0, 1]`. (Jones 2004, §2: the norm `‖·‖`
of eqs. (2)-(3).) -/
noncomputable def tvDist {X : Type*} [MeasurableSpace X]
    (μ ν : MeasureTheory.Measure X) : ℝ :=
  sSup {r | ∃ A : Set X, MeasurableSet A ∧ r = |(μ A).toReal - (ν A).toReal|}

end MarkovChainCLT


