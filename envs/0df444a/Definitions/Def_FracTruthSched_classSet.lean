-- Prove2me | Definitions.Def_FracTruthSched_classSet
-- name    : FracTruthSched_classSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:13.798688+00:00
-- url     : https://prove2.me/theorems/f44a557e-c175-42a3-a441-f2675c42b64b
-- title:
--   The class $Q_{\{i,j\}}$ of parallel edges between two machines
-- statement:
--   For machines $i\ne j$, the class $Q_{\{i,j\}}$ is the set of the $\ell$ parallel edges of $MC_\ell$ between $i$ and $j$. For a root $i$, the classes $D_j=Q_{\{i,j\}}$, $j\ne i$, form its multi-star.
--
--   **Formalization Note.** Defined as the edges incident to both $i$ and $j$; used only for $j\ne i$.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Definition 3, p.9

import Mathlib
import Definitions.Def_FracTruthSched_incident

set_option autoImplicit false

namespace FracTruthSched

/-- The **class** `Q{i,j}` of the `ℓ` parallel core tasks between machines `i` and `j`
(Anastasiadis et al., arXiv:2611.06642v1, Definition 3, p.9): the edges incident to both `i` and
`j`. For a root `i`, the classes `D_j = Q{i,j}`, `j ≠ i`, are the classes of its multi-star.

**Formalization Note.** Used only with `j ≠ i`; for `i ≠ j` this set has exactly `ℓ` elements. -/
def classSet {n ℓ : ℕ} (i j : Fin n) : Finset (CoreTask n ℓ) :=
  Finset.univ.filter (fun e => e.isLeft ∧ incident i e ∧ incident j e)

end FracTruthSched


