-- Prove2me | Definitions.Def_MDPFinance_Stationary_StructureAssumption
-- name    : MDPFinance_Stationary_StructureAssumption
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:44:27.741571+00:00
-- url     : https://prove2.me/theorems/511ffb94-9274-40bf-9ee9-2758c3f8fd9e
-- title:
--   The stationary Structure Assumption (SAN)
-- statement:
--   Sets $\mathrm{I\!M} \subseteq \mathrm{I\!M}(E)$ and $\Delta \subseteq F$ satisfy the
--   stationary **Structure Assumption (SAN)** if $g \in \mathrm{I\!M}$; $v \in \mathrm{I\!M}$
--   implies $Tv \in \mathrm{I\!M}$; and every $v \in \mathrm{I\!M}$ has a maximizer in $\Delta$.
--
--   **Formalization Note.** The book states this modified (SAN) as part of the statement of
--   Theorem 2.5.3 itself (it carries no separate definition number); it is extracted here as its
--   own item since it is reused, unmodified, as a hypothesis of Theorem 2.5.4.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 41, PDF 56, Theorem 2.5.3 (Structure Assumption (SAN))

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- The stationary Structure Assumption (SAN) (Bäuerle–Rieder, Theorem 2.5.3, p. 41, PDF 56 —
the book states this modified (SAN) as part of Theorem 2.5.3 itself, not under its own
definition number): there exist sets `IM ⊆ IM(E)` and `Δ ⊆ F` such that (i) `g ∈ IM`, (ii)
`v ∈ IM` implies `Tv ∈ IM`, (iii) every `v ∈ IM` has a maximizer `f ∈ Δ`. -/
def StructureAssumption (M : StationaryMarkovDecisionModel E A) (IMs : Set (E → EReal))
    (Delta : Set (E → A)) : Prop :=
  IMs ⊆ IM E ∧
  Delta ⊆ {f | IsDecisionRule M f} ∧
  (fun x => (M.g x : EReal)) ∈ IMs ∧
  (∀ v ∈ IMs, T M v ∈ IMs) ∧
  (∀ v ∈ IMs, ∃ f ∈ Delta, IsMaximizer M v f)

end MDPFinance.Stationary


