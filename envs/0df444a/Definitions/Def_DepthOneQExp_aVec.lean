-- Prove2me | Definitions.Def_DepthOneQExp_aVec
-- name    : DepthOneQExp_aVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:08.31993+00:00
-- url     : https://prove2.me/theorems/c7a7cb40-cdee-4399-8ae6-d113f27ed2b1
-- title:
--   The vectors $|a_1\rangle,\dots,|a_5\rangle$
-- statement:
--   On two copies of an $n$-qubit register, the five vectors of the proof of Theorem 2.13 (p.13) are
--   $$
--   |a_1\rangle=\sum_i|i\rangle|i\rangle,\quad |a_2\rangle=|+^n\rangle|+^n\rangle,\quad |a_3\rangle=|0^n\rangle|0^n\rangle,\quad |a_4\rangle=|0^n\rangle|+^n\rangle,\quad |a_5\rangle=|+^n\rangle|0^n\rangle .
--   $$
--   Their span is the range of the second-moment operator of the CNOT group (Eq. (2.43)). `aVec n k` is $|a_{k+1}\rangle$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eq. (2.40) and the line before Eq. (2.43), p.13

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_maxEnt
import Definitions.Def_DepthOneQExp_plusVec
import Definitions.Def_DepthOneQExp_zeroVec

namespace DepthOneQExp

/-- The five vectors `|a_1⟩, …, |a_5⟩` on two copies of an `n`-qubit register used in the proof of
Theorem 2.13 (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group
and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Eq. (2.40) and the line
before Eq. (2.43), p.13): `|a_1⟩ = Σ_i |i⟩|i⟩`, `|a_2⟩ = |+ⁿ⟩|+ⁿ⟩`, `|a_3⟩ = |0ⁿ⟩|0ⁿ⟩`,
`|a_4⟩ = |0ⁿ⟩|+ⁿ⟩`, `|a_5⟩ = |+ⁿ⟩|0ⁿ⟩`. `aVec n k` is `|a_{k+1}⟩`; the amplitude of `|x⟩|y⟩` in
`|u⟩|v⟩` is `u(x) v(y)`. -/
noncomputable def aVec (n : ℕ) : Fin 5 → MITMSynthesis.Q n × MITMSynthesis.Q n → ℂ :=
  ![maxEnt n, fun p => plusVec n p.1 * plusVec n p.2, fun p => zeroVec n p.1 * zeroVec n p.2,
    fun p => zeroVec n p.1 * plusVec n p.2, fun p => plusVec n p.1 * zeroVec n p.2]

end DepthOneQExp


