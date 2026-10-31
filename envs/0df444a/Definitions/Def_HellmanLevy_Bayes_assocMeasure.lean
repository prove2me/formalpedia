-- Prove2me | Definitions.Def_HellmanLevy_Bayes_assocMeasure
-- name    : HellmanLevy_Bayes_assocMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:17.406653+00:00
-- url     : https://prove2.me/theorems/22026ea7-93d7-4283-a128-d4fbef15dc5d
-- title:
--   Measure $\mu_T$ on the associated graphical game (4.5)
-- statement:
--   The measure on the vertices of the associated graphical game is
--   $$\mu_T=\frac{1}{|I|^2}\sum_{i,j\in I}t^i_*(\mu^j),$$
--   where $t^i_*(\mu^j)=\mu^j\circ(t^i)^{-1}$ is the push-forward of player $j$'s prior to player $i$'s type space. With a common prior $\mu$ it reduces to $\frac1{|I|}\sum_i t^i_*(\mu)$; it is a probability measure.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), eq. (4.5), p.20

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_typeOf

namespace HellmanLevy.Bayes

/-- The **measure `µ_T` on the vertices of the associated graphical game**:
`µ_T = |I|⁻² Σ_{i,j ∈ I} tⁱ_*(µʲ)`, where `tⁱ_*(µʲ) = µʲ ∘ (tⁱ)⁻¹` is the push-forward of
player `j`'s prior to player `i`'s type space.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), eq. (4.5), p.20.

**Formalization Note** The push-forward is along the measurable map `typeOf B i`
(measurable because `tⁱ` is), so `µ_T` is a probability measure. -/
noncomputable def assocMeasure {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    {A : I → Type*} (B : BayesianGame Ω I A) : MeasureTheory.Measure (TypeSpace B) :=
  ((Fintype.card I : ENNReal) ^ 2)⁻¹ • ∑ i, ∑ j, (B.μ j).map (typeOf B i)

end HellmanLevy.Bayes


