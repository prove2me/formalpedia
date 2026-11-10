-- Prove2me | Definitions.Def_ROLDescent_linkWalk
-- name    : ROLDescent_linkWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:02.454325+00:00
-- url     : https://prove2.me/theorems/82db3e6e-b987-43cb-a5b9-a6a1fbdf2cc1
-- title:
--   Link walk $P_\tau$
-- statement:
--   At a face $\tau$ the **link walk** is the Markov matrix on $N_\tau$ given by
--
--   $$P_\tau(i,j) = \frac{W_{\tau ij}}{(m_\tau - 1)\, W_{\tau i}} \quad (i \ne j), \qquad P_\tau(i,i) = 0,$$
--
--   where $\tau ij = \tau \cup \{i, j\}$ and $W_{\tau ij} = 0$ when $\tau ij$ is not a face. It is the non-lazy up–down walk $\tau i \to \tau ij \to \tau j$ on the link; its spectral gap enters the one-step Gram estimate.
--
--   **Formalization Note** Real division; at internal faces ($m_\tau \ge 2$) and for $i \in N_\tau$ the denominator is positive.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.1, eq. (69), p.29 (PDF 29)

import Mathlib
import Definitions.Def_ROLDescent_facetMass
import Definitions.Def_ROLDescent_remRank

namespace ROLDescent

/-- **Link walk** `P_τ`. Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.1, eq. (69), p.29 (PDF 29):
"P_τ(i, j) := W_τij / ((m_τ − 1) W_τi) (i ≠ j), P_τ(i, i) := 0. Here W_τij = 0 when τij ∉ X."

**Formalization Note** τij = τ ∪ {i, j} is `insert j (insert i τ)`. Real division; the denominator is
positive at internal faces (m_τ ≥ 2) for `i ∈ N_τ`. Read only for `i, j ∈ N_τ`. -/
noncomputable def linkWalk {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ)
    (w : Finset V → ℝ) (τ : Finset V) (i j : V) : ℝ :=
  if i = j then 0 else
    facetMass X d w (insert j (insert i τ)) /
      ((((remRank d τ : ℕ) : ℝ) - 1) * facetMass X d w (insert i τ))

end ROLDescent


