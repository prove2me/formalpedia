-- Prove2me | Definitions.Def_MDPFinance_PDMDP_Core
-- name    : MDPFinance_PDMDP_Core
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:04:12.209604+00:00
-- url     : https://prove2.me/theorems/294d9659-fa17-4891-b77f-09653f36c785
-- title:
--   The extended-real integral and the IB_b^+ regularity class (restated)
-- statement:
--   This chunk restates two pieces of shared vocabulary already used throughout this book's series in its own namespace, per this chunk's file-ownership boundary: the extended-real integral $\int v\,d\mu$ for $v : E \to \overline{\mathbb R}$ (`erealIntegral`, a total, junk-safe stand-in built from the positive/negative parts' lower integrals, restated from chunk `07a`'s `MDPFinance.Contracting.erealIntegral`), and the regularity class $IB_b^+ := \{v \in IM(E) \mid v^+(x) \le c\,b(x) \text{ for some } c \ge 0\}$ (Bäuerle–Rieder, p. 29, PDF 44), the class the Continuity and Compactness Assumptions of §8.2 (Definition 8.2.4's standing hypotheses) are stated against.
--
--   **Formalization Note.** Restated (not imported) from chunk `07a`, matching this whole book's series' convention that no chunk imports another chunk's Lean modules.
--
--   **Moderation note.** Unchanged: the `[-∞,∞]`-valued integral `∫ v⁺ − ∫ v⁻` (with `∞ − ∞ := −∞` via `⊤ + ⊥ = ⊥`), used throughout the chunk so that no value functional is a real Bochner integral that silently returns `0` when the integrand is not integrable.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 29, PDF 44 (restated; the general class also used by chunk `07a`)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.PDMDP

variable {E : Type*} [MeasurableSpace E]

/-- The extended-real integral, restated from `MDPFinance.Contracting.erealIntegral` (chunk
`07a`) per this chunk's own file-ownership boundary: a total, junk-safe stand-in for `∫ v dμ`
that is well-defined for every measurable `v : E → EReal`, used throughout this chunk for the
`IB_b^+`-valued (a priori not-yet-known-finite) side of the theory. -/
noncomputable def erealIntegral (μ : Measure E) (v : E → EReal) : EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

/-- `IB_b^+ := \{v \in IM(E) \mid v^+(x) \le c\,b(x)\}` (Bäuerle–Rieder, p. 29, PDF 44, restated),
the `EReal`-valued regularity class the Continuity and Compactness Assumptions (Def. 8.2.4's
standing hypotheses) are stated against. -/
def IBbPlus (b : E → ℝ) : Set (E → EReal) :=
  {v | Measurable v ∧ (∀ x, v x ≠ ⊤) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, (v x ⊔ 0) ≤ (c * b x : ℝ)}

end MDPFinance.PDMDP


