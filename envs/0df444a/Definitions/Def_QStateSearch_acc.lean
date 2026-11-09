-- Prove2me | Definitions.Def_QStateSearch_acc
-- name    : QStateSearch_acc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:17.188373+00:00
-- url     : https://prove2.me/theorems/5c8cef71-a6a7-48d1-97a1-bc341352ee34
-- title:
--   Acceptance probability under an oracle schedule
-- statement:
--   The acceptance probability of the verifier $V$ with prover $P$ when slot $s$ uses the oracle $O_s$ is
--   $$
--   \mathrm{acc}(V,O,P)=\sum_{h}\langle\phi_h|A|\phi_h\rangle ,
--   $$
--   the sum over the complete transcripts $h$ of the final branch vectors $\phi_h$ weighted by the accept effect $A$. Schedules that vary from slot to slot are the hybrids of the proof of Theorem 4.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.2, p.9; Section 4, p.13

import Mathlib
import Definitions.Def_QStateSearch_Verifier
import Definitions.Def_QStateSearch_transcripts
import Definitions.Def_QStateSearch_branch
open Matrix

namespace QStateSearch

/-- The acceptance probability of the verifier `V` interacting with the deterministic prover
`P` when query slot `s` uses the oracle `O s`:
`∑_h ⟨φ_h, A φ_h⟩` over the complete transcripts `h`, with `φ_h` the final branch vector and
`A` the accept effect.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.2, p.9 ("let Acc_W(V, P) be the verifier's acceptance probability when
interacting with P"); the schedule form is the hybrid of Section 4, p.13. -/
noncomputable def acc {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (V : Verifier D W) (O : ℕ → Matrix (Fin D) (Fin D) ℂ) (P : Prover) : ℝ :=
  ∑ h ∈ transcripts V.steps [],
    (star (branch O P V.steps V.init [] 0 h) ⬝ᵥ (V.accept *ᵥ branch O P V.steps V.init [] 0 h)).re

end QStateSearch


