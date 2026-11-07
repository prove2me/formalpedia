-- Prove2me | Definitions.Def_SteurerHDX_degree
-- name    : SteurerHDX_degree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:29.816205+00:00
-- url     : https://prove2.me/theorems/19b9aa42-7bab-45d5-b4ce-1fdaf3a9af8c
-- title:
--   The degree $\Delta$ of a complex
-- statement:
--   The **degree** of a complex $\mathcal X$ (with respect to its top dimension $d$) is the largest number of facets containing a single vertex:
--   $$\Delta=\max_{x\in V}\,\bigl|\{\sigma\in\mathcal X(d) : x\in\sigma\}\bigr| .$$
--   A complex is **sparse** when $\Delta$ is small compared with the number of vertices.
--
--   **Formalization Note** The maximum ranges over the elements occurring in faces of $\mathcal X$; an element in no face contributes $0$, so this is the maximum over $V$.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.2, p.3

import Mathlib
import Definitions.Def_SteurerHDX_faces

namespace SteurerHDX

/-- **The degree of a complex.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.2, p.3: "Given X, the degree of X is
defined as max_{x∈V} |{σ ∈ X(d) : x ∈ σ}|."

**Formalization Note.** The maximum is taken over the elements occurring in some face of `X`
(`X.biUnion id`); a ground-set element in no face contributes 0, so this is the paper's maximum
over V. It is a natural number. -/
def degree {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ) : ℕ :=
  (X.biUnion id).sup (fun x => ((faces X d).filter (fun σ => x ∈ σ)).card)

end SteurerHDX


