-- Prove2me | Definitions.Def_BoundEntGauss_realPartSpan
-- name    : BoundEntGauss_realPartSpan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:51.855578+00:00
-- url     : https://prove2.me/theorems/a0b1a673-e518-42d0-8d51-404924b396c7
-- title:
--   The real parts $\Re\mathfrak e\,\mathcal N$ of a complex subspace
-- statement:
--   For a complex subspace $\mathcal N\subseteq\mathbb C^{k}$, $\Re\mathfrak e\,\mathcal N$ denotes the real subspace of $\mathbb R^{k}$ consisting of all real parts $\operatorname{Re}\Phi=(\operatorname{Re}\Phi_i)_i$ of vectors $\Phi\in\mathcal N$.
--
--   In Proposition 3 the criterion for minimal ppt is that $\Re\mathfrak e\,\mathcal N$ and $\Re\mathfrak e\,\tilde{\mathcal N}$ together span the phase space.
--
--   **Formalization Note** Defined as the real span of the set of real parts; that set is already a real subspace, so the span adds nothing.
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section II, p. 2

import Mathlib

namespace BoundEntGauss

/-- **The real parts `ℜe N` of a complex subspace.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section II, p. 2 ("we denote by ℜe N the subspace of X consisting of all real parts of
vectors in N").

For a complex subspace `N ⊆ ℂ^κ`, `ℜe N` is the real subspace of `ℝ^κ` of the real parts
`(Re Φ_i)_i` of the vectors `Φ ∈ N`.

**Formalization Note.** The set of real parts of a complex subspace is already a real subspace;
the definition takes its real span, which therefore adds nothing. -/
def realPartSpan {κ : Type} (N : Submodule ℂ (κ → ℂ)) : Submodule ℝ (κ → ℝ) :=
  Submodule.span ℝ {x | ∃ v ∈ N, x = fun i => (v i).re}

end BoundEntGauss


