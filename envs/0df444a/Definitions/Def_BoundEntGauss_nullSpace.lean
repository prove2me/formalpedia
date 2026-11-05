-- Prove2me | Definitions.Def_BoundEntGauss_nullSpace
-- name    : BoundEntGauss_nullSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:59.760846+00:00
-- url     : https://prove2.me/theorems/28853a62-ff8b-4e2e-8c2c-d2e4dc857c1c
-- title:
--   The null space $\mathcal N$ of $\gamma+i\sigma$
-- statement:
--   For real square matrices $\gamma$ and $\sigma$ indexed by a finite set, the **null space** of $\gamma+i\sigma$ is the complex subspace
--
--   $$
--   \mathcal N=\{\Phi\in\mathbb C^{2f}\;:\;(\gamma+i\sigma)\Phi=0\}
--   $$
--
--   of the complexification of phase space. With $\sigma$ the symplectic matrix this is the paper's $\mathcal N$; with $\tilde\sigma$ in place of $\sigma$ it is $\tilde{\mathcal N}$ (Proposition 3).
--
--   **Formalization Note** The kernel of the complexified matrix, via the published `complexKernel`.
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section II, p. 2, and Proposition 3, p. 3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify complexKernel)

namespace BoundEntGauss

/-- **The null space of `γ + iσ`.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section II, p. 2 (`N = {Φ | (γ + iσ)Φ = 0}`) and Proposition 3, p. 3.

For real matrices `γ`, `σ` on a finite coordinate set, `nullSpace γ σ` is the complex
subspace `{Φ ∈ ℂ^κ | (γ + iσ)Φ = 0}` of the complexification of the phase space. With
`σ` the symplectic matrix it is `N`; with `σ̃` it is `Ñ`.

**Formalization Note.** The kernel is the published `Dependency50.P10.complexKernel` of the
entrywise complexified matrix `γ + iσ`. -/
noncomputable def nullSpace {κ : Type} [Fintype κ] (Γ σ : Matrix κ κ ℝ) : Submodule ℂ (κ → ℂ) :=
  complexKernel (complexify Γ + Complex.I • complexify σ)

end BoundEntGauss


