-- Prove2me | Definitions.Def_LindbladStructLearn_paulisOn
-- name    : LindbladStructLearn_paulisOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:52.463992+00:00
-- url     : https://prove2.me/theorems/5991ecea-26c8-41db-88f4-5625955f0e8d
-- title:
--   The Paulis $\mathcal P_S$ supported in a set $S$
-- statement:
--   For $S \subseteq [n]$, $\mathcal P_S$ is the set of the $4^{|S|}$ $n$-qubit Paulis that are the identity outside $S$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2, p.15

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The Paulis supported in a set (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), §2.2, p.15): `𝒫_S`, the `4^|S|` Paulis that are the
identity off `S`. -/
def paulisOn {n : ℕ} (S : Finset (Fin n)) : Finset (Pauli n) :=
  Finset.univ.filter fun R => support R ⊆ S

end LindbladStructLearn


