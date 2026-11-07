-- Prove2me | Definitions.Def_GaussTesting_topIrrep
-- name    : GaussTesting_topIrrep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:59.632093+00:00
-- url     : https://prove2.me/theorems/08088e8b-780f-4a31-a803-05ef4d3e78f2
-- title:
--   The top irrep $V_k=\overline{\mathrm{Span}}\{|\phi\rangle^{\otimes k}:\phi\in G_b\}$ and $\Pi_{\mathrm{test},G_b}$
-- statement:
--   For the $n$-mode bosonic Fock space $\mathcal H$ and $k\ge1$, let
--
--   $$
--   V_k=\overline{\mathrm{Span}}\{|\phi\rangle^{\otimes k}:\ |\phi\rangle \text{ bosonic Gaussian}\}\subseteq\mathcal H^{\otimes k}.
--   $$
--
--   By (6.11) this is the "top" irrep $V^{J(n)}_{(k/2,\dots,k/2)}$ of the Jacobi group in $\mathcal H^{\otimes k}$. The bosonic Gaussian test $\Pi_{\mathrm{test},G_b}$ is the projector onto $V_3$.
--
--   **Formalization Note** The irrep is encoded by its spanning set (6.11), since Mathlib has no representation of the Jacobi group on $\ell^2(\mathbb N^n)^{\otimes k}$; the irreducibility content is not used by Theorem 6.1. "Span" is the closed span.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §6.1 and Lemma 6.4, eq. (6.11), p.56

import Definitions.Def_GaussTesting_Gb
import Definitions.Def_GaussTesting_tpow

namespace GaussTesting

/-- The "top" irrep of `ℋ^{⊗k}` for bosonic Gaussian states, `Span{|ϕ⟩^{⊗k} : |ϕ⟩ bosonic Gaussian}`
(closed span); for `k = 3` its projector is the bosonic Gaussian test `Π_test,G_b`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), §6.1, p.56 ("Our tester will be based on projecting on to the top irrep for
`k = 3`, and we denote this projector as `Π_test,G_b`"), Lemma 6.4, eq. (6.11), p.56
(`V^{J(n)}_{(k/2,…,k/2)} ≅ Span{|ϕ⟩^{⊗k} | |ϕ⟩ is bosonic Gaussian}`).

**Formalization Note.** The irrep of the Jacobi group `J(n)` is encoded by its spanning set (6.11),
since Mathlib has no representation of `J(n)` on `ℓ²(ℕⁿ)^{⊗k}`; the irreducibility content of (6.11) is
not used in the proof of Theorem 6.1. "Span" is the closed span (an irrep subspace is closed; the
algebraic span is not closed in infinite dimension). -/
noncomputable def topIrrep (n k : ℕ) : ClosedSubmodule ℂ (Ell2 (Fin k → Fin n → ℕ)) :=
  (Submodule.span ℂ (tpow k '' Gb n)).closure

end GaussTesting


