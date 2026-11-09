-- Prove2me | Definitions.Def_QStateSearch_cqDist
-- name    : QStateSearch_cqDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:44.958037+00:00
-- url     : https://prove2.me/theorems/8c40867b-26b1-4047-872e-f66c945f237d
-- title:
--   Trace distance of the final classical–quantum states
-- statement:
--   For two oracle schedules $O,O'$ and a prover $P$, let $a_h,b_h$ be the final branch vectors of $V$. The trace distance of the two final classical–quantum states is
--   $$
--   D(\Omega,\Omega')=\sum_h\tfrac12\,\big\||a_h\rangle\langle a_h|-|b_h\rangle\langle b_h|\big\|_1 ,
--   $$
--   because the states are block diagonal over the public transcript and the trace norm of a block-diagonal operator is the sum over its blocks. Here $D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$.
--
--   **Formalization Note** $\|\cdot\|_1$ is the published `WildeQIT.traceDist` (which has no factor $\tfrac12$); the factor is written explicitly.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2, p.8; Section 4, p.13

import Mathlib
import Definitions.Def_QStateSearch_Verifier
import Definitions.Def_QStateSearch_transcripts
import Definitions.Def_QStateSearch_branch
import Definitions.Def_WildeQIT_traceDist
open Matrix

namespace QStateSearch

/-- The trace distance `D(Ω, Ω')` between the final classical–quantum states (verifier state and
public transcript) of `V` with prover `P` under the oracle schedules `O` and `O'`:
`∑_h ½ ‖|a_h⟩⟨a_h| − |b_h⟩⟨b_h|‖₁` over the complete transcripts `h`, where `a_h`, `b_h` are the
final branch vectors.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2, p.8 ("D(ρ, σ) = ½‖ρ − σ‖₁ denote trace distance") and Section 4, p.13
("E_Ψ[D(Ω^Ψ_{t−1}, Ω^Ψ_t)]").

**Formalization Note.** The final state `Ω = ∑_h |a_h⟩⟨a_h| ⊗ |h⟩⟨h|` is block diagonal over the
public transcript, and the trace norm of a block-diagonal operator is the sum of the trace norms
of its blocks. `WildeQIT.traceDist M N = ‖M − N‖₁` has no factor `½`; it is written here. -/
noncomputable def cqDist {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (V : Verifier D W) (P : Prover)
    (O O' : ℕ → Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  ∑ h ∈ transcripts V.steps [],
    (1 / 2 : ℝ) * WildeQIT.traceDist
      (vecMulVec (branch O P V.steps V.init [] 0 h) (star (branch O P V.steps V.init [] 0 h)))
      (vecMulVec (branch O' P V.steps V.init [] 0 h) (star (branch O' P V.steps V.init [] 0 h)))

end QStateSearch


