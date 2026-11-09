-- Prove2me | Definitions.Def_LindbladStructLearn_lindbladAdj
-- name    : LindbladStructLearn_lindbladAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:50:26.640675+00:00
-- url     : https://prove2.me/theorems/a57bef62-adb6-4999-bb79-401b85df9bb2
-- title:
--   Adjoint $\mathcal L_\lambda^\dagger$ of a parameterized Lindbladian
-- statement:
--   The adjoint of $\mathcal L_\lambda$ with respect to the pairing $\overline{\mathrm{tr}}(X\,\mathcal L(Y)) = \overline{\mathrm{tr}}(\mathcal L^\dagger(X)\,Y)$:
--
--   $$\mathcal L_\lambda^\dagger(O) = \sum_{P_1\ne I,\,P_2} \lambda_{P_1,P_2}\Big(P_2 O P_1 - \tfrac12\{P_2P_1, O\}\Big).$$
--
--   The pairing is bilinear, so the coefficients are not conjugated. Powers $\mathcal L_\lambda^{\dagger\ell}$ drive the cluster-expansion bounds of Section 4.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 2.3, Eq. (2.6), p.14; Eq. (4.59), p.29

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The adjoint of a parameterized Lindbladian (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 2.3, Eq. (2.6), p.14, and
Eq. (4.59), p.29): `L_λ†(O) = Σ_(P₁ ≠ I, P₂) λ_(P₁,P₂) (P₂ O P₁ − ½{P₂P₁, O})`, the map with
`tr̄(X L_λ(Y)) = tr̄(L_λ†(X) Y)`.

**Formalization Note** The explicit formula of Eq. (2.6)/(4.59) (the trace pairing is bilinear, so
`λ` is not conjugated). Entries with `P₁ = I` do not enter. -/
def lindbladAdj {n : ℕ} (x : Pauli n × Pauli n → ℂ) : Super (Qubits n) (Qubits n) :=
  ∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0),
    x P • (leftRight (pauliMatrix P.2) (pauliMatrix P.1) -
      (1 / 2 : ℂ) • (leftRight (pauliMatrix P.2 * pauliMatrix P.1) 1 +
        leftRight 1 (pauliMatrix P.2 * pauliMatrix P.1)))

end LindbladStructLearn


