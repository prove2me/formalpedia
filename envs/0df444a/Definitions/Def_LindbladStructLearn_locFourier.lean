-- Prove2me | Definitions.Def_LindbladStructLearn_locFourier
-- name    : LindbladStructLearn_locFourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:37.511714+00:00
-- url     : https://prove2.me/theorems/326584be-346a-4c62-b9b7-91247077a724
-- title:
--   Local Fourier coefficients $\widehat\Phi_{\mathrm{loc}}(P_1,P_2)$
-- statement:
--   For a superoperator $\Phi$ on $n$ qubits and a pair $\overline P = (P_1,P_2)$,
--
--   $$\widehat\Phi_{\mathrm{loc}}(P_1,P_2) = \mathbb E_{R\sim\mathcal P_{S_{\overline P}}}\big[\overline{\mathrm{tr}}\big(\chi_{P_1,P_2}(R)^\dagger\,\Phi(R)\big)\big],$$
--
--   the Fourier inversion formula with the random Pauli $R$ restricted to the support of the pair. These are the quantities the learning algorithm estimates from experiments.
--
--   **Formalization Note** $\Phi$ is any superoperator, given by its matrix in matrix units (the reused `LindbladTolerant.Testing.Super`).
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2.1, Eq. (2.22), p.16

import Mathlib
import Definitions.Def_LindbladStructLearn_pairSupport
import Definitions.Def_LindbladStructLearn_pauliAvg
import Definitions.Def_LindbladStructLearn_chi
import Definitions.Def_LindbladStructLearn_ntr

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Local Fourier coefficients (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2.1, Eq. (2.22), p.16):
`Φ̂_loc(P₁,P₂) = E_(R∼𝒫_(S_P̄)) [tr̄(χ_(P₁,P₂)(R)† · Φ(R))]`.

**Formalization Note** `Φ` is any superoperator, given by its matrix in matrix units (the reused
`LindbladTolerant.Testing.Super`); `tr̄` is the normalized trace `ntr`. -/
def locFourier {n : ℕ} (Φ : Super (Qubits n) (Qubits n)) (P : Pauli n × Pauli n) : ℂ :=
  pauliAvg (pairSupport P) fun R =>
    ntr ((chi P.1 P.2 (pauliMatrix R))ᴴ * applySuper Φ (pauliMatrix R))

end LindbladStructLearn


