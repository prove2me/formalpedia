-- Prove2me | Definitions.Def_QuantumHMMR_IsAcceptanceMatrix
-- name    : QuantumHMMR_IsAcceptanceMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:25.171491+00:00
-- url     : https://prove2.me/theorems/0de8c5e4-5a8e-4aa5-ae25-2a274be0a539
-- title:
--   Acceptance matrix $\Lambda_A$ of Lemma 4.1
-- statement:
--   Let $M^{(t)}_\nu = \mathbb E_{U \sim \nu}[U^{\otimes t} \otimes \bar U^{\otimes t}]$ be the order-$t$ moment operator of an ensemble $\nu$ (Eq. (3)), a $d^{2t} \times d^{2t}$ matrix with $d = 2^n$. A matrix $\Lambda$ of the same size is an **acceptance matrix** for a $t$-query algorithm $A$ and measurement $(M_A, I - M_A)$ when, for every unitary ensemble $\nu$,
--   $$
--   \mathop{\mathbb E}_{U \sim \nu} \mathrm{Tr}\big[M_A |A^U_t\rangle\langle A^U_t|\big] = \mathrm{Tr}\big[\Lambda^\dagger M^{(t)}_\nu\big].
--   $$
--   Lemma 4.1 asserts that such a $\Lambda$ exists, with trace norm at most $d^{2t}$.
--
--   **Formalization Note** A unitary ensemble is a probability measure on $n$-qubit matrices almost surely supported on unitaries. The moment operator is the published `balancedUnitaryMoment`, indexed by pairs of $t$-tuples of basis labels.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Lemma 4.1, Eq. (11), p.12

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_acceptProb

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped Matrix

namespace QuantumHMMR

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- `Λ` is an acceptance matrix for the algorithm `alg` and the measurement `(M, I - M)`: the
first clause of Eq. (11) of Lemma 4.1 (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), p.12) holds for every unitary ensemble,
`E_{U∼ν} Tr[M |A^U_t⟩⟨A^U_t|] = Tr[Λ† M^{(t)}_ν]`.

Here `Λ` is a `d^{2t} × d^{2t}` matrix (`d = 2^n`) on the index set of `U^{⊗t} ⊗ Ū^{⊗t}`, and
`M^{(t)}_ν = E_{U∼ν}[U^{⊗t} ⊗ Ū^{⊗t}]` is the moment operator of Eq. (3).

**Formalization Note** A unitary ensemble is a probability measure on `n`-qubit matrices that is
almost surely supported on unitaries. The moment operator is the published
`balancedUnitaryMoment`, indexed by pairs `(x, x')` of `t`-tuples of basis labels. The left side is
a real number, cast to `ℂ`. -/
def IsAcceptanceMatrix {n t : ℕ} (alg : AdaptiveAlg n t)
    (M : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ)
    (Λ : Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
      ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ) : Prop :=
  ∀ ν : Measure (QMat n), IsProbabilityMeasure ν →
    (∀ᵐ U ∂ν, U ∈ Matrix.unitaryGroup (Qubits n) ℂ) →
    ((∫ U, acceptProb alg M U ∂ν : ℝ) : ℂ) = (Λᴴ * balancedUnitaryMoment ν t).trace

end QuantumHMMR


