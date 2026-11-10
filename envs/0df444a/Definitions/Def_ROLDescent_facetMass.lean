-- Prove2me | Definitions.Def_ROLDescent_facetMass
-- name    : ROLDescent_facetMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:05.476378+00:00
-- url     : https://prove2.me/theorems/84d115db-0933-43ab-9901-a43c257afe90
-- title:
--   Total extension weight $W_\tau$
-- statement:
--   For a face $\tau$ of a weighted pure complex $(X, w)$ with facet size $d$, the **total extension weight** is the total weight of the facets containing $\tau$:
--
--   $$W_\tau = \sum_{F \supseteq \tau,\ F \text{ facet}} w_F .$$
--
--   For a set $\tau$ that is not a face the sum is empty and $W_\tau = 0$; this is the convention $W_{\tau ij} = 0$ when $\tau \cup \{i,j\} \notin X$. The weights $W_\tau$ determine all transition probabilities of the hierarchy.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1, eq. (66), p.29 (PDF 29)

import Mathlib
import Definitions.Def_SteurerHDX_faces

namespace ROLDescent

/-- **Total extension weight** `W_τ`. Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1, eq. (66), p.29 (PDF 29):
"For a face τ, define its total extension weight … by W_τ := Σ_{F⊇τ} w_F".

**Formalization Note** The sum runs over the facets of `X` (faces of cardinality `d`, which are the
facets of a pure complex) that contain `τ`. For a set `τ` that is not a face the sum is empty and
`W_τ = 0`, which is the paper's convention "W_τij = 0 when τij ∉ X" (p.29). -/
def facetMass {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) (τ : Finset V) : ℝ :=
  ∑ F ∈ (SteurerHDX.faces X d).filter (fun F => τ ⊆ F), w F

end ROLDescent


