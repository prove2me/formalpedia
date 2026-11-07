-- Prove2me | Definitions.Def_QSDMixing_GU_gramPow
-- name    : QSDMixing_GU_gramPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:55:55.977023+00:00
-- url     : https://prove2.me/theorems/ebae99a7-9be5-45ee-a2b3-8522e17bdf78
-- title:
--   The $t$-copy Gram matrix $X_t=X^{\circ t}$
-- statement:
--   The $t$-copy Gram matrix is the entrywise $t$-th power of the Gram matrix:
--
--   $$
--   (X_t)_{x,y}=(X_{x,y})^t.
--   $$
--
--   It satisfies $X_t=n\,\Phi_X^t(\tau_n)$, and it is the Gram matrix of the $t$-copy vectors $\psi_x^{\otimes t}$.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, p.17

import Mathlib
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_stabilizer
import Definitions.Def_QSDMixing_GU_gram

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- The `t`-copy Gram matrix `X_t = X^{∘t}`, the entrywise `t`-th power of the Gram matrix.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, p.17: "the `t`-copy Gram matrix", `X_t = |G| Φ_X^t(τ)`. -/
noncomputable def gramPow {G ι : Type} [Group G] (U : G →* unitary (Ell2 ι →L[ℂ] Ell2 ι)) (ψ : Ell2 ι)
    (t : ℕ) : Matrix (G ⧸ stabilizer U ψ) (G ⧸ stabilizer U ψ) ℂ :=
  Matrix.of fun x y => gram U ψ x y ^ t

end QSDMixing.GU


