-- Prove2me | Definitions.Def_MosonyiPetz_fixedPointsH
-- name    : MosonyiPetz_fixedPointsH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:55.533478+00:00
-- url     : https://prove2.me/theorems/31e6ed6e-3ffa-46d1-9a4a-d603040f2cbf
-- title:
--   The fixed-point set $\mathcal D_{\mathcal H}$ of $\gamma_{\mathcal H}$
-- statement:
--   $$\mathcal D_{\mathcal H}=\{A\in\mathcal B(\mathcal H):\ \gamma_{\mathcal H}(A)=A\}.$$
--
--   The paper calls it the fixed point algebra of $\gamma_{\mathcal H}=T^*\circ\alpha$; that it is an algebra, and isomorphic to $\mathcal D_{\mathcal K}$ through $T^*$, is part of Lemma 1.
--
--   **Formalization Note** Defined as a plain set; the algebra structure is a theorem, not part of the definition.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §4, p.8

import Mathlib
import Definitions.Def_MosonyiPetz_gammaH

open scoped Matrix

namespace MosonyiPetz

/-- **The fixed-point set D_H of γ_H.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §4, p.8: "Let the fixed point algebra of γH := T∗◦α be DH".

`fixedPointsH T D₁ = {A | gammaH T D₁ A = A}`.

**Formalization Note.** This is the plain set of fixed points; that it is an algebra is a claim of
the paper (Lemma 1), not part of the definition. -/
noncomputable def fixedPointsH {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K]
    [DecidableEq K] (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (D₁ : Matrix H H ℂ) : Set (Matrix H H ℂ) :=
  {A | gammaH T D₁ A = A}

end MosonyiPetz


