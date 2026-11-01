-- Prove2me | Definitions.Def_SeqHolevo_seqSuccessProb
-- name    : SeqHolevo_seqSuccessProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:58:36.751987+00:00
-- url     : https://prove2.me/theorems/7994f552-2de6-4ebe-9848-04740e5079f1
-- title:
--   Success probability of the sequential decoder for message $m$
-- statement:
--   If the $m$-th codeword $|\Phi_m\rangle$ is sent, the sequential decoder answers $m$ exactly when tests $1,\dots,m-1$ say "no" and test $m$ says "yes". Its success probability is
--
--   $$\operatorname{Tr}\{\varphi_m\hat\Pi_{m-1}\cdots\hat\Pi_1\varphi_m\hat\Pi_1\cdots\hat\Pi_{m-1}\varphi_m\}=\big|\langle\Phi_m|\hat\Pi_{m-1}\cdots\hat\Pi_1|\Phi_m\rangle\big|^2,\qquad \varphi_m=|\Phi_m\rangle\langle\Phi_m| .$$
--
--   The decoder is fixed by the code: it is not chosen or optimized.
--
--   **Formalization Note** Lean computes the right-hand side (equal to the printed trace because $\varphi_m$ is a rank-one projector); messages are 0-based.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, p.6

import Mathlib
import Definitions.Def_SeqHolevo_seqRemainder

open QAlgorithms.Papers.Independent.Intakenext100.P76 (coefficientInner)

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, p.6 (PDF page): "if Alice transmits the m-th codeword, then the
probability for Bob to decode correctly with this sequential decoding strategy is
`Tr{φ_{xⁿ(m)} Π̂_{m−1} ⋯ Π̂_1 φ_{xⁿ(m)} Π̂_1 ⋯ Π̂_{m−1} φ_{xⁿ(m)}}`". The decoder tests codewords
`1, 2, …` in order with `{φ_{xⁿ(i)}, Π̂_i}` and stops at the first "yes" (§II, pp.2–3).

Here it is `|⟨Φ_m | Π̂_{m−1} ⋯ Π̂_1 | Φ_m⟩|²`, computed with `seqRemainder`.

**Formalization Note.** Because `φ = |Φ_m⟩⟨Φ_m|` is a rank-one projector of a unit vector,
`Tr{φ A φ A† φ} = |⟨Φ_m|A|Φ_m⟩|²` for `A = Π̂_{m−1} ⋯ Π̂_1`, so this is the printed trace. Lean's
message `m : Fin M` is 0-based: it is preceded by the tests of codewords `0, …, m−1`. The
decoder is fixed by the code, not chosen. -/
noncomputable def seqSuccessProb {J : Type} {M : ℕ} (Φ : Fin M → J → ℂ) (m : Fin M) : ℝ :=
  Complex.normSq (coefficientInner (Φ m) (seqRemainder Φ (Φ m) (m : ℕ)))

end SeqHolevo


