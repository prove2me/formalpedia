-- Prove2me | Definitions.Def_LindbladStructLearn_lindbladSuper
-- name    : LindbladStructLearn_lindbladSuper
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:07.931512+00:00
-- url     : https://prove2.me/theorems/de0ef9e7-70d5-4ceb-8de5-57f675f41988
-- title:
--   Parameterized Lindbladian $\mathcal L_\lambda$
-- statement:
--   For a coefficient vector $\lambda$ indexed by pairs of $n$-qubit Paulis,
--
--   $$\mathcal L_\lambda(\rho) = \sum_{P_1 \ne I,\,P_2} \lambda_{P_1,P_2}\Big(P_1\rho P_2 - \tfrac12\{P_2P_1, \rho\}\Big).$$
--
--   With $\lambda_{P,I} = \alpha_P$ and $\lambda_{P_1,P_2} = D_{P_1,P_2}$ ($P_2 \ne I$) this is the Lindbladian (2.4) with coherent part $\tfrac12\sum_P \alpha_P[P,\rho]$ and dissipative matrix $D$. For a general $\lambda$ it is the paper's "superoperator" $\mathcal L_\lambda$, which need not be a physical Lindbladian.
--
--   **Formalization Note** $\lambda$ is a function on all pairs; the entries with $P_1 = I$ do not enter $\mathcal L_\lambda$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.1, Eq. (2.5) and Definition 2.2, pp.13–14

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The parameterized Lindbladian (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.1, Eq. (2.5) and Definition 2.2, pp.13–14):
`L_λ(ρ) = Σ_(P₁ ≠ I, P₂) λ_(P₁,P₂) (P₁ ρ P₂ − ½{P₂P₁, ρ})`, as a superoperator matrix.

**Formalization Note** A coefficient vector is a function on all pairs of `n`-qubit Paulis; the
entries with `P₁ = I` do not enter `L_λ` (the paper indexes `λ` by pairs with `P₁ ≠ I` only).
`λ_(P,I) = α_P` and `λ_(P₁,P₂) = D_(P₁,P₂)` recover Equation (2.4). No condition on `λ`: for general
`λ` this is the paper's "superoperator", not necessarily a physical Lindbladian. -/
def lindbladSuper {n : ℕ} (x : Pauli n × Pauli n → ℂ) : Super (Qubits n) (Qubits n) :=
  ∑ P ∈ Finset.univ.filter (fun P : Pauli n × Pauli n => P.1 ≠ 0),
    x P • (leftRight (pauliMatrix P.1) (pauliMatrix P.2) -
      (1 / 2 : ℂ) • (leftRight (pauliMatrix P.2 * pauliMatrix P.1) 1 +
        leftRight 1 (pauliMatrix P.2 * pauliMatrix P.1)))

end LindbladStructLearn


