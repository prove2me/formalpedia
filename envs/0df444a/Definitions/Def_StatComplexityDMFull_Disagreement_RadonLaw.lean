-- Prove2me | Definitions.Def_StatComplexityDMFull_Disagreement_RadonLaw
-- name    : StatComplexityDMFull_Disagreement_RadonLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:52:30.738269+00:00
-- url     : https://prove2.me/theorems/53216381-0781-4cea-acbe-a1b32e0e4cd5
-- title:
--   Radon probability laws and the selected-decision pushforward
-- statement:
--   Let $X$ be a topological space with its Borel measurable structure. A Radon probability law is a probability measure $\mu$ that is inner regular by compact sets. Every measurable set is approximated in mass from within by compact subsets. For an index law $\mu$ on $Z$ and a selected decision map $a:Z\to\Pi$, define
--
--   $$\rho_\mu=a_\#\mu,\qquad P_{\mu,a}(S)=\mu(a^{-1}(S)).$$
--
--   The structural identity in this file identifies $P_{\mu,a}(S)$ with $\rho_\mu(S)$ whenever $a$ and $S$ are measurable. When $Z$ is discrete, every preimage is measurable; thus this also defines the canonical atomic event probability without assuming that a function-class existential event has a Borel description on $\Pi$.
--
--   This layer is separate from the bandit model. It includes countably infinite-support laws, such as $\mu(\{n\})=2^{-(n+1)}$ on discrete $\mathbb N$, and makes no finiteness or discrete-topology requirement on decisions. The pushforward's Radon admissibility for the main theorem is asserted as a conclusion, not assumed as an input.
-- source:
--   Foster, Kakade, Qian and Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, pp. 10–11, probability notation and footnote 5; p. 99, Borel/Radon convention; p. 45, Theorem 6.2 posterior law

import Mathlib

set_option autoImplicit false

namespace StatComplexityDMFull.Disagreement

/-- All inner-regular Borel probability measures, not just finite-support laws.
The ambient measurable space is required to be Borel at use sites. -/
structure RadonLaw (X : Type*) [TopologicalSpace X] [MeasurableSpace X] where
  val : MeasureTheory.Measure X
  probability : MeasureTheory.IsProbabilityMeasure val
  radon : MeasureTheory.Measure.InnerRegular val

instance {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (μ : RadonLaw X) :
    MeasureTheory.IsProbabilityMeasure μ.val := μ.probability

/-- The actual pushforward measure; admissibility is a conclusion for discrete-model priors. -/
noncomputable def posteriorLaw {Z A : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    (μ : MeasureTheory.Measure Z) (a : Z → A) : MeasureTheory.Measure A :=
  MeasureTheory.Measure.map a μ

/-- Canonical probability of an event under an indexed random decision.
For discrete Radon model priors every preimage is measurable, even for a non-Borel decision event. -/
noncomputable def pullbackProb {Z A : Type*} [MeasurableSpace Z]
    (μ : MeasureTheory.Measure Z) (a : Z → A) (S : Set A) : ℝ :=
  (μ (a ⁻¹' S)).toReal

/-- Identification with the pushforward on the source's measurable events. -/
theorem pullbackProb_eq_map {Z A : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    (μ : MeasureTheory.Measure Z) (a : Z → A) (ha : Measurable a)
    (S : Set A) (hS : MeasurableSet S) :
    pullbackProb μ a S = ((posteriorLaw μ a) S).toReal := by
  simp only [pullbackProb, posteriorLaw, MeasureTheory.Measure.map_apply ha hS]

end StatComplexityDMFull.Disagreement


