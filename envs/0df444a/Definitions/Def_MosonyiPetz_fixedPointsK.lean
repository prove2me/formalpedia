-- Prove2me | Definitions.Def_MosonyiPetz_fixedPointsK
-- name    : MosonyiPetz_fixedPointsK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:56.314352+00:00
-- url     : https://prove2.me/theorems/c0cb465a-21ad-40d1-aa0b-458bfdf9f3e0
-- title:
--   The fixed-point set $\mathcal D_{\mathcal K}$ of $\gamma_{\mathcal K}$
-- statement:
--   $$\mathcal D_{\mathcal K}=\{X\in\mathcal B(\mathcal K):\ \gamma_{\mathcal K}(X)=X\}.$$
--
--   The paper calls it the fixed point algebra of $\gamma_{\mathcal K}=\alpha\circ T^*$. It lies in the multiplicative domain of $T^*$ (Lemma 1), is invariant under the modular group of $T(D_1)$ (p.9) and contains $T(D_1)^{it}T(D_2)^{-it}$ (p.9); these facts produce the subalgebra of Theorem 1.
--
--   **Formalization Note** Defined as a plain set.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §4, p.8

import Mathlib
import Definitions.Def_MosonyiPetz_gammaK

open scoped Matrix

namespace MosonyiPetz

/-- **The fixed-point set D_K of γ_K.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §4, p.8: "that of γK := α◦T∗ be DK".

`fixedPointsK T D₁ = {A | gammaK T D₁ A = A}`.

**Formalization Note.** This is the plain set of fixed points; that it is an algebra is a claim of
the paper (Lemma 1), not part of the definition. -/
noncomputable def fixedPointsK {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K]
    [DecidableEq K] (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (D₁ : Matrix H H ℂ) : Set (Matrix K K ℂ) :=
  {A | gammaK T D₁ A = A}

end MosonyiPetz


