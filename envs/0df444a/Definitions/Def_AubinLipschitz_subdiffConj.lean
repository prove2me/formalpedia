-- Prove2me | Definitions.Def_AubinLipschitz_subdiffConj
-- name    : AubinLipschitz_subdiffConj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:31.296991+00:00
-- url     : https://prove2.me/theorems/503b4ff1-5cc1-4235-8b44-e78b783d1ef9
-- title:
--   The subdifferential $\partial V^*(q)\subset Y$ of a conjugate function
-- statement:
--   Let $V:Y\to\mathbb R\cup\{+\infty\}$ with conjugate $V^*(q)=\sup_{y\in Y}(\langle q,y\rangle-V(y))$ on the dual $Y^*$. For $q\in Y^*$, the subdifferential of $V^*$ at $q$, taken in $Y$, is
--
--   $$
--   \partial V^*(q)=\{y\in Y\mid V^*(q)+\langle q'-q,y\rangle\le V^*(q')\ \text{ for all } q'\in Y^*\}.
--   $$
--
--   **Formalization Note** A subdifferential of a function on $Y^*$ is a subset of the bidual $Y^{**}$ when defined literally. The paper's spaces are finite dimensional and it identifies $Y^{**}$ with $Y$, so the set is written directly in $Y$.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, (4)ii, p.31

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Conj
open RockafellarMaxMono.Shared

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, (4)ii, p.31: the subdifferential `∂V*(q) ⊂ Y` of the conjugate of `V : Y → ℝ ∪ {+∞}`
at `q ∈ Y*`, that is, the set of `y ∈ Y` with `V*(q) + ⟨q' − q, y⟩ ≤ V*(q')` for all `q' ∈ Y*`.

**Formalization Note** `RockafellarMaxMono.Shared.subdiff (conj V) q` is a subset of the bidual
`Y**`. The paper identifies `Y**` with `Y` (its spaces are finite dimensional), so the set is
written here directly in `Y`. -/
def subdiffConj {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (V : Y → EReal)
    (q : StrongDual ℝ Y) : Set Y :=
  {y | ∀ q' : StrongDual ℝ Y, conj V q + (((q' - q) y : ℝ) : EReal) ≤ conj V q'}

end AubinLipschitz


