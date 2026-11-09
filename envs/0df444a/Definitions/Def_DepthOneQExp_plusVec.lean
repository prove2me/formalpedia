-- Prove2me | Definitions.Def_DepthOneQExp_plusVec
-- name    : DepthOneQExp_plusVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:25.858187+00:00
-- url     : https://prove2.me/theorems/ed766381-b104-45a1-9423-377d4eb564f3
-- title:
--   The state $|+^n\rangle$
-- statement:
--   The uniform superposition on an $n$-qubit register,
--   $$
--   |+^n\rangle = \frac1{\sqrt N}\sum_{x\in\{0,1\}^n}|x\rangle,\qquad N=2^n .
--   $$
--   It appears in the commutant of the CNOT group (Lemma 2.15) and in the vectors $|a_2\rangle,|a_4\rangle,|a_5\rangle$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Lemma 2.15, p.12

import Mathlib
import Definitions.Def_MITMSynthesis_Gate

namespace DepthOneQExp

/-- The state `|+ⁿ⟩ = 2^{−n/2} Σ_x |x⟩` of an `n`-qubit register (Anshu–Balasubramanian–Haferkamp–
Harrow–Tan, *Depth-1 expanders on the unitary group and applications*, arXiv:2609.01605, held
version sha256 3c3f8513…aebfd87, Lemma 2.15, p.12): every amplitude equals `1/√N`, `N = 2ⁿ`. -/
noncomputable def plusVec (n : ℕ) : MITMSynthesis.Q n → ℂ :=
  fun _ => ((Real.sqrt (2 ^ n))⁻¹ : ℝ)

end DepthOneQExp


