-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_RealSuccess
-- name    : AgnosticTNS_Supplement_RealSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:31:25.589956+00:00
-- url     : https://prove2.me/theorems/c9a0aa92-d254-4526-855c-d23fae8fc240
-- title:
--   Success of a realisable learner: trace-norm error at most $\epsilon$
-- statement:
--   In the realisable setting the input is a pure state $|\psi\rangle$ and the learner must output a classical description of a pure state $|\hat\psi\rangle$ with
--   $$
--   \big\| |\psi\rangle\langle\psi| - |\hat\psi\rangle\langle\hat\psi| \big\|_1 \le \epsilon .
--   $$
--   The output need not belong to the reference class.
--
--   **Formalization Note** The output string decodes with the mission's fixed decoder to a tree tensor network (any number of nodes) with Gaussian-rational entries and nonzero state, and $|\hat\psi\rangle$ is that state divided by its norm.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 4, Eq. (4.1), p.28

import Mathlib
import Definitions.Def_AgnosticTNS_decodeTTN
import Definitions.Def_AgnosticTNS_TTN_state
import Definitions.Def_WildeQIT_traceNorm
open Matrix

namespace AgnosticTNS.Supplement

/-- **Success of a realisable learner**, Eq. (4.1), p.28 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
the output string `s` describes a pure state `|ψ̂⟩` with `‖|ψ⟩⟨ψ| − |ψ̂⟩⟨ψ̂|‖₁ ≤ ε`. The output need not
belong to the reference class.

**Formalization Note** `s` decodes with the fixed decoder `decodeTTN` to a TTN `D` (any number of
nodes, any tree) with Gaussian-rational entries and nonzero state, and `|ψ̂⟩` is its normalised state
`D.state / ‖D.state‖` (exact normalisation is not representable with rational entries). -/
noncomputable def RealSuccess {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (ε : ℝ)
    (s : QAlgorithms.Complexity.Str) : Prop :=
  ∃ (m : ℕ) (D : TTN m n d), decodeTTN n d s = some ⟨m, D⟩ ∧ D.state ≠ 0 ∧
    WildeQIT.traceNorm (vecMulVec ψ (star ψ) -
      ((∑ x, ‖D.state x‖ ^ 2 : ℝ) : ℂ)⁻¹ • vecMulVec D.state (star D.state)) ≤ ε

end AgnosticTNS.Supplement


