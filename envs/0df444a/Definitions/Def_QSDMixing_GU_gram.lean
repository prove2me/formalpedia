-- Prove2me | Definitions.Def_QSDMixing_GU_gram
-- name    : QSDMixing_GU_gram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:52:41.808214+00:00
-- url     : https://prove2.me/theorems/06df6900-37b5-415c-bf09-1ea7c3276e07
-- title:
--   The Gram matrix $X$ on $G/H$
-- statement:
--   The Gram matrix of the coset states is the $n\times n$ matrix, $n=|G/H|$, with entries
--
--   $$
--   X_{xH,yH}=\langle\psi_{xH}|\psi_{yH}\rangle=\langle\psi|U(x^{-1}y)|\psi\rangle.
--   $$
--
--   It is positive semidefinite with unit diagonal, and it lies in the Hecke algebra.
--
--   **Formalization Note** The inner product is conjugate-linear in its first slot, as in the bra-ket notation.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, p.17

import Mathlib
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_stabilizer

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- The Gram matrix `X_{xH,yH} = ⟨ψ_x, ψ_y⟩ = ⟨ψ| U(x⁻¹ y) |ψ⟩` on `G ⧸ H`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, p.17.

**Formalization Note.** Mathlib's inner product is conjugate-linear in the first slot, as in
`⟨ψ_x|ψ_y⟩`. -/
noncomputable def gram {G ι : Type} [Group G] (U : G →* unitary (Ell2 ι →L[ℂ] Ell2 ι)) (ψ : Ell2 ι) :
    Matrix (G ⧸ stabilizer U ψ) (G ⧸ stabilizer U ψ) ℂ :=
  Matrix.of fun x y =>
    inner ℂ ((U x.out : Ell2 ι →L[ℂ] Ell2 ι) ψ) ((U y.out : Ell2 ι →L[ℂ] Ell2 ι) ψ)

end QSDMixing.GU


