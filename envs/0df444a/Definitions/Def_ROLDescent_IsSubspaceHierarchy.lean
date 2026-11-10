-- Prove2me | Definitions.Def_ROLDescent_IsSubspaceHierarchy
-- name    : ROLDescent_IsSubspaceHierarchy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:13.158889+00:00
-- url     : https://prove2.me/theorems/a8e580a5-cf4a-4c86-9cb4-e7cbfd766d69
-- title:
--   Common-metric subspace hierarchy (73)
-- statement:
--   Fix a finite-dimensional complex Hilbert space $\mathcal K$. A family of subspaces $\mathcal I_\tau \subseteq \mathcal K$ indexed by faces is a **subspace hierarchy** if at every internal face $\tau$ (that is, $|\tau| + 2 \le d$)
--
--   $$\mathcal I_{\tau i} \subseteq \mathcal I_\tau \quad (i \in N_\tau), \qquad \sum_{i \in N_\tau} \mathcal I_{\tau i} = \mathcal I_\tau ,$$
--
--   where the sum is the linear span (not a direct sum): the child spaces may overlap and need not be orthogonal.
--
--   **Formalization Note** The span is the supremum in the lattice of submodules. Values at sets that are not visited faces are never read.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.2, eq. (73), pp.30–31 (PDF 30–31)

import Mathlib
import Definitions.Def_HDXConc_linkWeight

namespace ROLDescent

/-- **Common-metric subspace hierarchy.** Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1.2, eq. (73), p.30–31
(PDF 30–31): "Fix a finite-dimensional Hilbert space K. At every visited face choose a linear
subspace I_τ ⊆ K, with its inherited metric. The structural requirements are I_τi ⊆ I_τ,
Σ_{i∈N_τ} I_τi = I_τ (τ ∈ T_int). The sum denotes linear span, not a direct sum".

**Formalization Note** `I : Finset V → Submodule ℂ K`; the internal faces T_int are the faces with
`τ.card + 2 ≤ d`, and the linear span of the children is the supremum `⨆` in the submodule
lattice. Values of `I` at sets that are not visited faces are never read. -/
def IsSubspaceHierarchy {V : Type*} [Fintype V] [DecidableEq V] {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (X : Finset (Finset V)) (d : ℕ) (I : Finset V → Submodule ℂ K) : Prop :=
  ∀ τ ∈ X, τ.card + 2 ≤ d →
    (∀ i ∈ HDXConc.linkVerts X τ, I (insert i τ) ≤ I τ) ∧ (⨆ i ∈ HDXConc.linkVerts X τ, I (insert i τ)) = I τ

end ROLDescent


