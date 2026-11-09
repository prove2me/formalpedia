-- Prove2me | Definitions.Def_LindbladStructLearn_Eell
-- name    : LindbladStructLearn_Eell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:53:43.535356+00:00
-- url     : https://prove2.me/theorems/5e7325c3-d8bf-4e17-9f34-1c0693863986
-- title:
--   Degree-$\ell$ term $E^{(\ell)}_{\overline P}(x)$
-- statement:
--   For an integer $\ell \ge 0$,
--
--   $$E^{(\ell)}_{\overline P}(x) = \mathbb E_{R\sim\mathcal P_{S_{\overline P}}}\big[\overline{\mathrm{tr}}\big(\chi_{P_1,P_2}(R)^\dagger\,\mathcal L_x^\ell(R)\big)\big],$$
--
--   the $\ell$-th Taylor coefficient (up to $t^\ell/\ell!$) of the local Fourier coefficient of $e^{\mathcal L_x t}$; by (4.6) it equals $\mathbb E_R[\overline{\mathrm{tr}}(\mathcal L_x^{\dagger\ell}(P_2RP_1)\,R)]$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (4.4), p.24

import Mathlib
import Definitions.Def_LindbladStructLearn_lindbladSuper
import Definitions.Def_LindbladStructLearn_pauliAvg
import Definitions.Def_LindbladStructLearn_chi
import Definitions.Def_LindbladStructLearn_ntr
import Definitions.Def_LindbladStructLearn_pairSupport

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The degree-`ℓ` term of the series (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (4.4), p.24):
`E^(ℓ)_P̄(x) = E_(R∼𝒫_(S_P̄)) [tr̄(χ_(P₁,P₂)(R)† · L_x^ℓ(R))]` (equal to `E_R[tr̄(L_x^(†ℓ)(P₂RP₁) R)]`,
Eq. (4.6)).

**Formalization Note** `L_x^ℓ` is the `ℓ`-th power of the superoperator matrix (composition). -/
def Eell {n : ℕ} (ℓ : ℕ) (x : Pauli n × Pauli n → ℂ) (P : Pauli n × Pauli n) : ℂ :=
  pauliAvg (pairSupport P) fun R =>
    ntr ((chi P.1 P.2 (pauliMatrix R))ᴴ * applySuper (lindbladSuper x ^ ℓ) (pauliMatrix R))

end LindbladStructLearn


