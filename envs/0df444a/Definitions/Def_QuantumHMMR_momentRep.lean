-- Prove2me | Definitions.Def_QuantumHMMR_momentRep
-- name    : QuantumHMMR_momentRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:02.302691+00:00
-- url     : https://prove2.me/theorems/37cfd448-4c72-4c63-b35e-24333ff969ed
-- title:
--   The operator $U^{\otimes t} \otimes \bar U^{\otimes t}$
-- statement:
--   For an $n$-qubit matrix $U$ and $t \in \mathbb N$, the operator $U^{\otimes t} \otimes \bar U^{\otimes t}$ acts on $(\mathbb C^{2^n})^{\otimes 2t}$; its average over $U \sim \nu$ is the moment operator
--   $$
--   M^{(t)}_\nu = \mathop{\mathbb E}_{U \sim \nu}\big[U^{\otimes t} \otimes \bar U^{\otimes t}\big]. \tag{3}
--   $$
--   A vector $v$ is invariant under a group of unitaries when $(U^{\otimes t} \otimes \bar U^{\otimes t})v = v$ for every $U$ in the group; this defines the Clifford- and Haar-invariant subspaces of Lemma 4.2.
--
--   **Formalization Note** Same index set and entries as the integrand of the published `balancedUnitaryMoment`.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 3, Eq. (3), p.10; Lemma 4.2, p.13

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45
open scoped ComplexConjugate

namespace QuantumHMMR

/-- The operator `U^{⊗t} ⊗ Ū^{⊗t}` whose average is the moment operator of Eq. (3)
(Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), p.10): `M^{(t)}_ν = E_{U∼ν}[U^{⊗t} ⊗ Ū^{⊗t}]`. A vector `v` is invariant under a set of
unitaries `S` when `(U^{⊗t} ⊗ Ū^{⊗t}) v = v` for every `U ∈ S`.

**Formalization Note** Same index set and entries as the integrand of the published
`balancedUnitaryMoment`: rows and columns are pairs `(x, x')` of `t`-tuples of basis labels, and the
`((x, x'), (y, y'))` entry is `∏_j U_{x_j y_j} · conj(∏_j U_{x'_j y'_j})`. -/
noncomputable def momentRep {n : ℕ} (t : ℕ) (U : QMat n) :
    Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
      ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ :=
  Matrix.of fun x y => qubitTensorPower t U x.1 y.1 * conj (qubitTensorPower t U x.2 y.2)

end QuantumHMMR


