-- Prove2me | Definitions.Def_ROLDescent_remRank
-- name    : ROLDescent_remRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:01.102049+00:00
-- url     : https://prove2.me/theorems/11a9ac64-1e5c-4352-bb91-39223c310f35
-- title:
--   Remaining rank $m_\tau = d - |\tau|$
-- statement:
--   For a face $\tau$ of a pure complex with facet size $d$, the **remaining rank** is $m_\tau = d - |\tau|$, the number of vertices still needed to complete $\tau$ to a facet. It need not equal $|N_\tau|$.
--
--   **Formalization Note** Natural-number subtraction, exact on faces (where $|\tau| \le d$); it is cast to the reals only after the subtraction.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1, eq. (66), p.29 (PDF 29)

import Mathlib

namespace ROLDescent

/-- **Remaining rank** `m_τ`. Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1, eq. (66), p.29 (PDF 29):
"m_τ := d − |τ|. … The number m_τ counts the vertices still needed to complete a facet."

**Formalization Note** Natural-number subtraction; it is exact on faces of a pure complex with facet
size `d`, where `τ.card ≤ d`. It is cast to ℝ only after the subtraction. -/
def remRank {V : Type*} (d : ℕ) (τ : Finset V) : ℕ := d - τ.card

end ROLDescent


