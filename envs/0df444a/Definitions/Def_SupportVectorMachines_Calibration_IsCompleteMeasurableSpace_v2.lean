-- Prove2me | Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace_v2
-- name    : SupportVectorMachines_Calibration_IsCompleteMeasurableSpace_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:18:51.086013+00:00
-- url     : https://prove2.me/theorems/5a590127-c977-4855-ad8a-8888ab1de3c8
-- title:
--   Complete measurable space (Appendix A.3.3): the $\sigma$-algebra equals its universal completion — corrected
-- statement:
--   A measurable space $(X,\mathcal A)$ is **complete** (p. 482) if $\mathcal A$ equals its universal completion $\bigcap_P \mathcal A_P$, the intersection over all probability measures $P$ on $X$ of the $P$-completions $\mathcal A_P$. Since $\mathcal A \subseteq \bigcap_P \mathcal A_P$ always holds, this says: every set that lies in the $P$-completion for every probability measure $P$ is measurable. Mathlib's `NullMeasurableSet s μ` is exactly membership of $s$ in the $\mu$-completion.
--
--   **Formalization Note.** The retired module used, as its definition, the book's remark that $P$-completeness for a single probability measure $P$ suffices; that is a strictly stronger hypothesis (it implies universal completeness via $\mathcal A \subseteq \bigcap_Q \mathcal A_Q \subseteq \mathcal A_P = \mathcal A$), so the theorems stated with it were weaker than the book's. The corrected module states the book's own definition.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 482, Appendix A.3.3 (universal completion)

import Mathlib

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- `X` **is a complete measurable space** (Steinwart & Christmann, *Support Vector Machines*,
Springer 2008, Appendix A.3.3, p. 482): the σ-algebra of `X` equals its *universal completion*
`⋂_P 𝒜_P`, the intersection over all probability measures `P` on `X` of the `P`-completions
`𝒜_P` (the sets of the form `A ∪ N` with `A` measurable and `N` contained in a `P`-null
measurable set). Since the inclusion `𝒜 ⊆ ⋂_P 𝒜_P` always holds, completeness says: every set
that is `P`-null-measurable for *every* probability measure `P` is measurable. Mathlib's
`NullMeasurableSet s μ` is exactly membership of `s` in the `μ`-completion. The book's remark
that a σ-algebra which is `P`-complete for a single `P` is complete in this sense is a
consequence (`𝒜 ⊆ ⋂_Q 𝒜_Q ⊆ 𝒜_P = 𝒜`), not the definition; the retired module
`Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace` used that strictly stronger
sufficient condition as its definition, which is replaced here by the book's own. -/
def IsCompleteMeasurableSpace (X : Type*) [MeasurableSpace X] : Prop :=
  ∀ s : Set X, (∀ μ : Measure X, IsProbabilityMeasure μ → NullMeasurableSet s μ) →
    MeasurableSet s

end SupportVectorMachines.Calibration


