-- Prove2me | Definitions.Def_OLPRegret_innerMeasure
-- name    : OLPRegret_innerMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:02.836301+00:00
-- url     : https://prove2.me/theorems/13c292c8-3c3f-4bfd-bb39-7041e5c163d2
-- title:
--   Inner probability
-- statement:
--   For a possibly non-measurable event $A$, the **inner probability** is $P_*(A)=\sup\{P(B):B\text{ measurable},B\subseteq A\}$.
--
--   Events defined by a condition over all $b\in B_\delta(\beta)$ and all minimizers of a dual are not known to be measurable. An inner probability in a lower bound is the convention of the empirical-process results that the paper cites, and it is the strong direction.
--
--   **Formalization Note** Mathlib's `P A` of a non-measurable set is the outer measure, so a lower bound on it would say less. The matching outer expectation for upper bounds is the referenced `PlugInRisk.outerExp`.
-- source:
--   Bray, arXiv:1912.08917v6, Lemma 10, Online Appendix p.26 (convention of van der Vaart and Wellner, cited there)

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace OLPRegret

/-- The **inner probability** `P_*(A) = sup {P(B) : B measurable, B ⊆ A}` of a possibly non-measurable
event.

**Formalization Note** Mathlib's `P A` of a non-measurable `A` is the outer measure, so a lower bound
on it would say less than the lower bound on this inner measure (Bray, arXiv:1912.08917v6, Lemma 10,
Online Appendix p.26). -/
noncomputable def innerMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) : ℝ≥0∞ :=
  ⨆ (B : Set Ω) (_ : MeasurableSet B) (_ : B ⊆ A), P B

end OLPRegret


