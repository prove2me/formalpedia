-- Prove2me | Definitions.Def_QStateSearch_branch
-- name    : QStateSearch_branch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:49.640531+00:00
-- url     : https://prove2.me/theorems/fb3534e6-920d-4563-8521-25c8563de144
-- title:
--   Final branch vectors of a run
-- statement:
--   Fix an oracle schedule $(O_s)_{s\ge0}$ (query slot $s$ uses $O_s$) and a deterministic prover $P$. Running the step list from the vector $\phi$ produces, for each complete transcript $h$, an unnormalized final vector $\phi_h$: a unitary step applies $U$; a query applies the controlled call of $O_s$ and moves to slot $s+1$; a verifier message branches over its outcomes $a$, multiplying by $K_a$ and recording $a$; a prover message applies $U_{P(h',b)}$ after the current transcript $h'$ and records the reply. Transcripts the run does not produce get the vector $0$.
--
--   With private measurements deferred, $\|\phi_h\|^2$ is the probability of transcript $h$, and the final classical–quantum state is $\sum_h|\phi_h\rangle\langle\phi_h|\otimes|h\rangle\langle h|$.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.2, pp.8–10; Section 4, p.13

import Mathlib
import Definitions.Def_QStateSearch_ctrlQuery
import Definitions.Def_QStateSearch_Step
import Definitions.Def_QStateSearch_Prover
open Matrix

namespace QStateSearch

/-- The run of a step list against a deterministic prover `P` and an oracle schedule `O`
(query slot `s` uses the oracle `O s`). `branch O P steps φ h s h'` is the final unnormalized
verifier vector on the branch whose complete public transcript is `h'`, when the run starts
in the vector `φ`, after transcript `h`, at query slot `s`; it is `0` for transcripts the run
does not produce.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.2, pp.8–10, and Section 4, p.13 ("For t = 0, …, q, let Ω^ψ_t be the final state
of the verifier and public transcript when the first t calls use I and the remaining calls
use R_ψ").

**Formalization Note.** Private measurements are deferred, so each branch is a pure
unnormalized vector whose squared norm is the probability of its transcript. A unitary step
applies `U`; a query applies `controlled-O_s` and moves to slot `s + 1`; a verifier message
sums over its outcomes `a`, each multiplied by `K a` and recorded; a prover message applies
`U (P h b)` and records the reply. -/
noncomputable def branch {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (O : ℕ → Matrix (Fin D) (Fin D) ℂ) (P : Prover) :
    List (Step D W) → (Reg D W → ℂ) → List ℕ → ℕ → List ℕ → Reg D W → ℂ
  | [], φ, h, _ => fun h' => if h' = h then φ else 0
  | .unitary U :: rest, φ, h, s => branch O P rest ((U : Matrix (Reg D W) (Reg D W) ℂ) *ᵥ φ) h s
  | .query :: rest, φ, h, s => branch O P rest (ctrlQuery (O s) *ᵥ φ) h (s + 1)
  | .vmsg m K :: rest, φ, h, s => fun h' =>
      ∑ a : Fin m, branch O P rest (K a *ᵥ φ) (h ++ [a.val]) s h'
  | .pmsg b U :: rest, φ, h, s =>
      branch O P rest ((U (P h b) : Matrix (Reg D W) (Reg D W) ℂ) *ᵥ φ) (h ++ [(P h b).val]) s

end QStateSearch


