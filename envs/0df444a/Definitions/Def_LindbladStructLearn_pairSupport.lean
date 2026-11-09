-- Prove2me | Definitions.Def_LindbladStructLearn_pairSupport
-- name    : LindbladStructLearn_pairSupport
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:00.507279+00:00
-- url     : https://prove2.me/theorems/7cc8aa39-c140-469a-b4c1-b8229c969cdd
-- title:
--   Support $S_{\overline P}$ of a pair of Paulis
-- statement:
--   For a pair $\overline P = (P_1, P_2)$ of $n$-qubit Paulis, $S_{\overline P} = \mathrm{supp}(P_1) \cup \mathrm{supp}(P_2)$, where $\mathrm{supp}(P)$ is the set of qubits on which $P$ is not the identity. Its size is $s_{\overline P} = |S_{\overline P}|$.
--
--   **Formalization Note** Qubits are indexed by $\{0, \dots, n-1\}$ instead of the paper's $[n] = \{1,\dots,n\}$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, p.13

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Support of a pair of Paulis (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2, p.13): `S_P̄ = supp(P₁) ∪ supp(P₂)`; its
cardinality is `s_P̄`.

**Formalization Note** Qubit indices are `Fin n` (0-based); the paper's `[n] = {1,…,n}`. -/
def pairSupport {n : ℕ} (P : Pauli n × Pauli n) : Finset (Fin n) :=
  support P.1 ∪ support P.2

end LindbladStructLearn


