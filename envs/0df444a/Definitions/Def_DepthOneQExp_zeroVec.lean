-- Prove2me | Definitions.Def_DepthOneQExp_zeroVec
-- name    : DepthOneQExp_zeroVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:36.414193+00:00
-- url     : https://prove2.me/theorems/3e26fc33-7a6c-46d0-9708-cbb2f15f3795
-- title:
--   The state $|0^n\rangle$
-- statement:
--   The all-zero computational basis state $|0^n\rangle$ of an $n$-qubit register. It appears in the commutant of the CNOT group (Lemma 2.15) and in the vectors $|a_3\rangle,|a_4\rangle,|a_5\rangle$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Lemma 2.15, p.12

import Mathlib
import Definitions.Def_MITMSynthesis_Gate

namespace DepthOneQExp

/-- The basis state `|0ⁿ⟩` of an `n`-qubit register (Anshu–Balasubramanian–Haferkamp–Harrow–Tan,
*Depth-1 expanders on the unitary group and applications*, arXiv:2609.01605, held version sha256
3c3f8513…aebfd87, Lemma 2.15, p.12): amplitude `1` on the all-zero string and `0` elsewhere. -/
def zeroVec (n : ℕ) : MITMSynthesis.Q n → ℂ :=
  fun x => if x = 0 then 1 else 0

end DepthOneQExp


