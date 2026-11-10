-- Prove2me | Definitions.Def_ROLDescent_outProb
-- name    : ROLDescent_outProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:23.179198+00:00
-- url     : https://prove2.me/theorems/a0f9e6ac-948a-4e6b-8fa6-39985ee30d22
-- title:
--   Outgoing probability $\pi_\tau(i)$
-- statement:
--   At a face $\tau$ the **outgoing probability** of the step $\tau \to \tau i$ is
--
--   $$\pi_\tau(i) = \frac{W_{\tau i}}{m_\tau W_\tau},$$
--
--   where $\tau i = \tau \cup \{i\}$. Equivalently, choose a facet $F \supseteq \tau$ with probability proportional to its weight and then a vertex of $F \setminus \tau$ uniformly. At internal faces $\pi_\tau$ is a probability distribution on $N_\tau$.
--
--   **Formalization Note** Real division; the denominator is positive at the faces where the quantity is used.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.1, eq. (69), p.29 (PDF 29)

import Mathlib
import Definitions.Def_ROLDescent_facetMass
import Definitions.Def_ROLDescent_remRank

namespace ROLDescent

/-- **Outgoing probability** `π_τ(i)`. Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.1, eq. (69), p.29 (PDF 29):
"π_τ(i) := W_τi / (m_τ W_τ)".

**Formalization Note** Real division; at internal faces of a weighted complex the denominator is
positive (eq. (70), milestone). Read only for `i ∈ N_τ`. -/
noncomputable def outProb {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ)
    (w : Finset V → ℝ) (τ : Finset V) (i : V) : ℝ :=
  facetMass X d w (insert i τ) / ((remRank d τ : ℝ) * facetMass X d w τ)

end ROLDescent


