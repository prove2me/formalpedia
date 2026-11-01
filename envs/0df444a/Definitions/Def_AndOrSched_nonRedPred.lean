-- Prove2me | Definitions.Def_AndOrSched_nonRedPred
-- name    : AndOrSched_nonRedPred
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:00.75767+00:00
-- url     : https://prove2.me/theorems/fe05ff22-2930-4e91-ae88-22e11ef5ed29
-- title:
--   Non-redundant OR-predecessors
-- statement:
--   An OR-arc $(a,b)\in E_\vee$ is **redundant** if some other OR-predecessor $a'\in\mathcal P(b)$ is a transitive AND-predecessor of $a$: every feasible schedule completes $a'$ before $a$, so the arc $(a,b)$ adds nothing. The non-redundant OR-predecessors of $b$ are
--   $$\{a\in\mathcal P(b)\mid \text{no }a'\in\mathcal P(b),\ a'\ne a,\ \text{has }a'\to^+_{E_\wedge}a\}.$$
--
--   **Formalization Note** The paper assumes $E_\wedge$ transitively closed; here the transitive closure of the AND-arcs is used instead, which gives the same set without changing the instance.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §1, p.4, "We may further assume that there are no redundant OR-precedence constraints"

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_orPred
open scoped Classical NNReal

namespace AndOrSched

/-- The non-redundant OR-predecessors of `b ∈ B` (Happach, Schulz, arXiv:2001.07011v1, §1, p.4): an OR-arc `(a, b) ∈ E∨` is
redundant if some `a' ∈ 𝒫(b)`, `a' ≠ a`, is a (transitive) AND-predecessor of `a`, because then
"any feasible schedule has to schedule a′ before a". This is `𝒫(b)` after removing every redundant
OR-arc.

**Formalization Note** The paper assumes w.l.o.g. that `E∧` is transitively closed; here the
transitive closure `Relation.TransGen` of the AND-arcs inside `A` is used instead, which is the same
condition without changing the instance. -/
noncomputable def nonRedPred (I : Instance) (b : I.B) : Finset I.A :=
  (orPred I b).filter fun a => ¬ ∃ a' ∈ orPred I b, a' ≠ a ∧ Relation.TransGen I.andA a' a

end AndOrSched


