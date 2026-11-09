-- Prove2me | Definitions.Def_LindbladStructLearn_boolChar
-- name    : LindbladStructLearn_boolChar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:55.088552+00:00
-- url     : https://prove2.me/theorems/e78199d9-94db-481f-bfba-74cfc090d3c2
-- title:
--   Boolean character $\chi_S(v) = \prod_{i\in S} v_i$
-- statement:
--   For $S \subseteq [n]$ and $v \in \{\pm1\}^n$, $\chi_S(v) = \prod_{i\in S} v_i$, the standard Boolean Fourier character.
--
--   **Formalization Note** $v_i = -1$ is encoded as `true`.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (2.24), p.16

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The Boolean Fourier character (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (2.24), p.16): `χ_S(v) = Π_(i ∈ S) v_i`
(`v_i = −1` for `true`). -/
def boolChar {n : ℕ} (S : Finset (Fin n)) (v : Qubits n) : ℂ :=
  ∏ i ∈ S, if v i then (-1 : ℂ) else 1

end LindbladStructLearn


