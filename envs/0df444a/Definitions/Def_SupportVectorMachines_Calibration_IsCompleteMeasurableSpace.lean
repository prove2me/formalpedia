-- Prove2me | Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace
-- name    : SupportVectorMachines_Calibration_IsCompleteMeasurableSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:28:27.957726+00:00
-- url     : https://prove2.me/theorems/3f373e1e-b254-439e-b149-ba1123ce3c8c
-- title:
--   A complete measurable space (sufficient-condition rendering)
-- statement:
--   Several results of this chapter (Lemma 3.4, Lemma 3.11, Theorem 3.17, Corollary 3.19) assume
--   $X$ is a **complete measurable space** (Steinwart & Christmann, *Support Vector Machines*,
--   Springer 2008, Appendix, p. 482, after Lemma A.3.3): its $\sigma$-algebra $\mathcal A$ equals
--   its own universal completion $\hat{\mathcal A} := \bigcap_P \mathcal A_P$, the intersection
--   of the $P$-completions of $\mathcal A$ over every probability measure $P$ on $\mathcal A$.
--
--   The book itself records, as an immediate consequence: "$\mathcal A$ is complete if it is
--   $P$-complete for some $P$" (i.e. $\mathcal A = \mathcal A_P$ for a single $P$, which is a
--   sufficient but not visibly necessary condition for $\mathcal A = \hat{\mathcal A}$), and a
--   measurable space is $P$-complete exactly when every subset of a $P$-null measurable set is
--   itself measurable (a standard equivalent reformulation of $\mathcal A = \mathcal A_P$, since
--   $\mathcal A_P = \{A \cup B : A \in \mathcal A, \exists N \in \mathcal A,\ P(N)=0,\ B \subset
--   N\}$).
--
--   **Formalization Note** `IsCompleteMeasurableSpace X` is defined as this sufficient condition
--   ("$\exists$ a probability measure $\mu$ that is $\mu$-complete") rather than the exact
--   universal-completion equality, a deliberate, disclosed strengthening: every hypothesis in
--   this mission that invokes "$X$ complete measurable space" is satisfied by any $X$ meeting
--   this stronger condition, so no theorem here overclaims beyond what the book proves for
--   genuinely complete spaces.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 482, Lemma A.3.3 and the surrounding definitions

import Mathlib

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- `X` **is a complete measurable space** (Steinwart & Christmann, *Support Vector Machines*,
Springer 2008, Appendix, p. 482, after Lemma A.3.3): there exists a probability measure `μ` on
`X` whose σ-algebra is already `μ`-complete, i.e. every subset of a `μ`-null set is measurable.
The book's actual definition is that the σ-algebra equals its *universal* completion
`⋂_P A_P` (the intersection over every probability measure `P`); it also records, as a
consequence, that a σ-algebra which is `P`-complete for *some* single `P` is automatically
complete in this sense ("`A` is complete if it is `P`-complete for some `P`", p. 482). This
sufficient condition is used here as the operative definition — a deliberate, disclosed
simplification of the exact universal-completion statement, chosen because it is what the
book's own applications (e.g. Lemma 3.4, Theorem 3.17) actually invoke, and because it is a
*stronger* hypothesis than genuine completeness, so a theorem stated with it does not overclaim
beyond what the book proves for actually complete spaces. -/
def IsCompleteMeasurableSpace (X : Type*) [MeasurableSpace X] : Prop :=
  ∃ μ : Measure X, IsProbabilityMeasure μ ∧
    ∀ ⦃s : Set X⦄, (∃ t : Set X, MeasurableSet t ∧ μ t = 0 ∧ s ⊆ t) → MeasurableSet s

end SupportVectorMachines.Calibration


