-- Prove2me | Definitions.Def_ROLDescent_WeightedComplex
-- name    : ROLDescent_WeightedComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:04.597945+00:00
-- url     : https://prove2.me/theorems/1ec6a1d6-c4c5-4d68-a943-8065eac995cd
-- title:
--   Weighted pure simplicial complex with facet size $d\ge 2$
-- statement:
--   Let $V$ be a finite vertex set. A **weighted pure complex** with facet size $d$ is a finite family $X$ of subsets of $V$ together with a weight function $w$ such that
--
--   1. $X$ is nonempty and closed under taking subsets (a finite simplicial complex; its elements are **faces**, including $\emptyset$);
--   2. $X$ is **pure**: every inclusion-maximal face (**facet**) has exactly $d$ elements;
--   3. $d \ge 2$;
--   4. every facet $F$ carries a positive weight $w_F > 0$.
--
--   These are the standing assumptions of Section 5.1 under which the spectral-descent theorem is stated.
--
--   **Formalization Note** Faces are `Finset V` over a `Fintype`-style vertex type; purity and downward closure are the public `SteurerHDX.IsPure`, which holds vacuously for the empty family, so nonemptiness is added (Definition 2.6 requires it). The weight is a function on all finite sets but is read only on facets.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1, p.29 (PDF 29); Definition 2.6, p.12 (PDF 12)

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_faces

namespace ROLDescent

/-- **Weighted pure complex** (the standing assumptions of Section 5.1). Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545),
Section 5.1, p.29 (PDF 29): "Let X be a finite pure simplicial complex whose facets have
cardinality d ≥ 2. Give each facet F a positive weight w_F." Definition 2.6, p.12 (PDF 12): "A
finite simplicial complex X is a nonempty family of subsets of a finite vertex set, closed under
taking subsets."

**Formalization Note** Faces are `Finset V` over a finite vertex type; the complex is a finite family
`X` that is nonempty, downward closed and pure with facets of cardinality `d` (public
`SteurerHDX.IsPure`, which is vacuous on the empty family, hence `X.Nonempty`). The weight `w` is a
function on all finite sets but is read only on facets (`SteurerHDX.faces X d`), where it is
positive. -/
def WeightedComplex {V : Type*} (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) : Prop :=
  X.Nonempty ∧ SteurerHDX.IsPure X d ∧ 2 ≤ d ∧ ∀ F ∈ SteurerHDX.faces X d, 0 < w F

end ROLDescent


