-- Prove2me | Definitions.Def_SeqHolevo_seqError
-- name    : SeqHolevo_seqError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:59:33.195905+00:00
-- url     : https://prove2.me/theorems/27b390ce-57d3-4562-9ead-63b011a1881e
-- title:
--   Error probability of the sequential decoder for message $m$
-- statement:
--   The probability that the sequential decoder errs when the $m$-th codeword is sent:
--
--   $$1-\operatorname{Tr}\{\varphi_m\hat\Pi_{m-1}\cdots\hat\Pi_1\varphi_m\hat\Pi_1\cdots\hat\Pi_{m-1}\varphi_m\}.$$
--
--   **Formalization Note** Messages are 0-based.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, p.6

import Mathlib
import Definitions.Def_SeqHolevo_seqSuccessProb

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, p.6 (PDF page): "the probability that Bob makes an error when decoding
the m-th codeword is just `1 − Tr{φ_{xⁿ(m)} Π̂_{m−1} ⋯ Π̂_1 φ_{xⁿ(m)} Π̂_1 ⋯ Π̂_{m−1} φ_{xⁿ(m)}}`".

**Formalization Note.** `1 − seqSuccessProb Φ m`; 0-based messages (see `seqSuccessProb`). -/
noncomputable def seqError {J : Type} {M : ℕ} (Φ : Fin M → J → ℂ) (m : Fin M) : ℝ :=
  1 - seqSuccessProb Φ m

end SeqHolevo


