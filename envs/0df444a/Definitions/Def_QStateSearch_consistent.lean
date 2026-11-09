-- Prove2me | Definitions.Def_QStateSearch_consistent
-- name    : QStateSearch_consistent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:03.708876+00:00
-- url     : https://prove2.me/theorems/8365d5bc-0e94-4472-a0d1-a3d372388696
-- title:
--   Consistency of a prover with a transcript
-- statement:
--   A deterministic prover $P$ is **consistent** with a transcript $h$ of a step list if $P$ sends every prover message recorded in $h$: at each prover-message step of length $b$, the reply $P(h',b)$ after the preceding part $h'$ of $h$ is the reply recorded in $h$. Verifier messages impose no condition. For a family $\psi\mapsto P_\psi$, the **compatible set** of $h$ is
--   $$
--   C(h)=\{\psi : P_\psi\text{ is consistent with }h\}.
--   $$
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 3, p.11

import Mathlib
import Definitions.Def_QStateSearch_Step
import Definitions.Def_QStateSearch_Prover

namespace QStateSearch

/-- `consistent P steps hp hr`: reading the transcript entries `hr` against the step list
`steps` (after the already-read prefix `hp`), the prover `P` sends every prover message recorded
there: at each prover-message step of length `b`, `P hp b` is the recorded reply. Verifier
messages impose no condition. A full transcript `h` is checked as `consistent P steps [] h`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 3, p.11: "For a possible transcript h, define its compatible set
C(h) = {ψ ∈ CP^{D−1} : P_ψ sends every prover message recorded in h}."

**Formalization Note.** The compatible set of a prover family `P : ℂ^D → Prover` is
`{ψ | consistent (P ψ) V.steps [] h}`. The function is `Bool`-valued so that it can be used in
`if … then … else`. Entries beyond the end of the step list impose no condition (such
transcripts never occur). -/
def consistent {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (P : Prover) : List (Step D W) → List ℕ → List ℕ → Bool
  | _, _, [] => true
  | [], _, _ :: _ => true
  | .unitary _ :: rest, hp, hr => consistent P rest hp hr
  | .query :: rest, hp, hr => consistent P rest hp hr
  | .vmsg _ _ :: rest, hp, x :: hr => consistent P rest (hp ++ [x]) hr
  | .pmsg b _ :: rest, hp, x :: hr =>
      decide ((P hp b).val = x) && consistent P rest (hp ++ [x]) hr

end QStateSearch


