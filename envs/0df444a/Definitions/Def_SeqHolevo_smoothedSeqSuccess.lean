-- Prove2me | Definitions.Def_SeqHolevo_smoothedSeqSuccess
-- name    : SeqHolevo_smoothedSeqSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:58:51.885636+00:00
-- url     : https://prove2.me/theorems/878ee907-2e2f-4d1c-92c9-8ba68aa89689
-- title:
--   Smoothed success term of (11)
-- statement:
--   For a code $|\Phi_1\rangle,\dots,|\Phi_M\rangle$ and a projector $\Pi$, the smoothed success term of message $m$ is
--
--   $$\operatorname{Tr}\{\varphi_m\hat\Pi_{m-1}\cdots\hat\Pi_1\,\Pi\varphi_m\Pi\,\hat\Pi_1\cdots\hat\Pi_{m-1}\varphi_m\}=\big|\langle\Phi_m|\hat\Pi_{m-1}\cdots\hat\Pi_1\Pi|\Phi_m\rangle\big|^2,$$
--
--   the success probability of the sequential decoder when the received state between the tests is replaced by its projection $\Pi\varphi_m\Pi$.
--
--   **Formalization Note** Lean computes the right-hand side; messages are 0-based.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, eq. (11), p.7

import Mathlib
import Definitions.Def_SeqHolevo_seqRemainder
import Definitions.Def_SeqHolevo_arrApply

open QAlgorithms.Papers.Independent.Intakenext100.P76 (coefficientInner)

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, p.7 (PDF page), (11): the smoothed success term
`Tr{φ_{xⁿ(m)} Π̂_{m−1} ⋯ Π̂_1 Π φ_{xⁿ(m)} Π Π̂_1 ⋯ Π̂_{m−1} φ_{xⁿ(m)}}`, in which the received
state `φ_{xⁿ(m)}` between the tests is replaced by its projection `Π φ_{xⁿ(m)} Π`.

Here it is `|⟨Φ_m | Π̂_{m−1} ⋯ Π̂_1 Π | Φ_m⟩|²`.

**Formalization Note.** For a unit vector `Φ_m` and a self-adjoint `Π`,
`Π φ Π = |ΠΦ_m⟩⟨ΠΦ_m|` and `Tr{φ A |ΠΦ_m⟩⟨ΠΦ_m| A† φ} = |⟨Φ_m|A Π Φ_m⟩|²`, which is this
expression with `A = Π̂_{m−1} ⋯ Π̂_1` (computed by `seqRemainder` started at `ΠΦ_m`). 0-based
messages. -/
noncomputable def smoothedSeqSuccess {J : Type} {M : ℕ} (Φ : Fin M → J → ℂ)
    (P : Matrix J J ℂ) (m : Fin M) : ℝ :=
  Complex.normSq (coefficientInner (Φ m) (seqRemainder Φ (arrApply P (Φ m)) (m : ℕ)))

end SeqHolevo


