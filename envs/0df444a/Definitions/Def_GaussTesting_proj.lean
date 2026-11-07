-- Prove2me | Definitions.Def_GaussTesting_proj
-- name    : GaussTesting_proj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:14.337433+00:00
-- url     : https://prove2.me/theorems/0e2e35f6-0ac9-49ce-a138-329a8e507065
-- title:
--   Orthogonal projector onto a closed subspace
-- statement:
--   For a closed subspace $K$ of $\ell^2(\alpha)$, $\Pi_K$ is the orthogonal projector onto $K$. Every orthogonal projector on a Hilbert space is the projector onto its closed range, so throughout the mission projective tests $\Pi_{\mathrm{test}}$ are specified by their accepting subspaces.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Remark 1.3, p.5; Definition 3.1, p.21

import Definitions.Def_GaussTesting_Ell2

namespace GaussTesting

/-- The orthogonal projector `Π_K` onto a closed subspace `K` of `ℓ²(α)`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Remark 1.3, p.5 (testers as orthogonal projectors `Π_test`), Definition 3.1,
p.21.

**Formalization Note.** Every orthogonal projector on a Hilbert space is the projector onto its
(closed) range, so projectors are given by closed subspaces throughout this mission. -/
noncomputable def proj {α : Type*} (K : ClosedSubmodule ℂ (Ell2 α)) : Ell2 α →L[ℂ] Ell2 α :=
  (K : Submodule ℂ (Ell2 α)).starProjection

end GaussTesting


