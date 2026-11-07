-- Prove2me | Definitions.Def_ContractionLemma_Splitting_betaTerm
-- name    : ContractionLemma_Splitting_betaTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:02:30.329603+00:00
-- url     : https://prove2.me/theorems/4d5f9e23-5527-4199-bab9-e53d77bf38fa
-- title:
--   The $\beta$-term
-- statement:
--   For an exponent vector $\beta$, the **$\beta$-term** is the part of $F(t+\alpha z_j)$ in which each mode $\xi$ is used exactly $\beta_\xi$ times:
--
--   $$
--   \sum_{Y,X}A(Y)\,B(X)\Big[\prod_x\chi_{Y_x}\Big(\omega_x+\sum_\xi c_{x,\xi}\xi\Big)\Big]_\beta\ \prod_\xi\xi(X)^{\beta_\xi}.
--   $$
--
--   In the bracket the modes are formal variables, and in the last product they are evaluated at the column bits.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), App. A.5.3, p.68 and proof of Lemma A.12.2, p.90

import Mathlib
import Definitions.Def_ContractionLemma_BipNet
import Definitions.Def_ContractionLemma_BipNet_Phi
import Definitions.Def_ContractionLemma_Packing
import Definitions.Def_ContractionLemma_NodeField
import Definitions.Def_ContractionLemma_Splitting_modeSet

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

namespace Splitting

variable {U W E : Type*} {f : ℤ[X]} {a : ℕ}

/-- **The β-term** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript, sha256
049caea1…), App. A.5.3, p.68, and proof of Lemma A.12.2, p.90 (PDF p.93):
`∑_{Y,X} A(Y) B(X) [∏_x χ_{Y_x}(ω_x + ∑_ξ c_{x,ξ} ξ)]_β ∏_ξ ξ(X)^{β_ξ}`, where the modes are
formal variables in the bracket and `[·]_β` is the coefficient of `∏_ξ ξ^{β_ξ}`. -/
noncomputable def betaTerm [Fintype U] [Fintype W] [Fintype E] [DecidableEq E]
    (G : BipNet U W E (NodeField f)) (pk : Packing U W E a) (t : ℤ) (i : ℕ) (z : NodeField f)
    (p' : ℕ) (β : Mode G pk i p' → ℕ) : NodeField f :=
  ∑ Y : E → Bool, ∑ X : E → Bool, G.rowProd Y * G.colProd X *
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm β) (∏ e, wireFactor G pk t i z p' e Y X) *
    ∏ ξ, modeVal G pk i p' ξ X ^ β ξ

end Splitting

end ContractionLemma


