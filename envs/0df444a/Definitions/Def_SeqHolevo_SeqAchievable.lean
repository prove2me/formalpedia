-- Prove2me | Definitions.Def_SeqHolevo_SeqAchievable
-- name    : SeqHolevo_SeqAchievable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:00:57.354151+00:00
-- url     : https://prove2.me/theorems/b5a6a8ee-fde9-426c-b4dc-4b3b8f8616e7
-- title:
--   Rate achievable with the sequential decoder
-- statement:
--   A rate $R$ (bits per channel use) is **achievable with sequential decoding** for the pure-state channel $x\mapsto|\varphi_x\rangle$ if for every $\varepsilon>0$ there is $N$ such that for every blocklength $n\ge N$ there are $M\ge2^{nR}$ codewords $x^n(1),\dots,x^n(M)\in X^n$ for which the sequential decoder of these codewords (tested in order) errs with probability at most $\varepsilon$ on **every** message.
--
--   **Formalization Note** This is the standard notion (maximal error) of the paper's reference [4]; the paper's proof reaches maximal error by expurgation. $2^{nR}$ is a real power, not rounded.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Theorem 1, p.2

import Mathlib
import Definitions.Def_SeqHolevo_seqError
import Definitions.Def_SeqHolevo_codeVecs

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Theorem 1, p.2 (PDF page): "the rate `R` bits per channel use is achievable for
communication over this channel by having the receiver employ a sequential decoding strategy".

For every `ε > 0` there is `N` such that for every blocklength `n ≥ N` there are `M ≥ 2^{nR}`
codewords `C 0, …, C (M−1) ∈ Xⁿ` for which the sequential decoder of these codewords, tested in
index order, errs with probability at most `ε` on **every** message.

**Formalization Note.** Reading R1 of the mission: the standard notion of achievability (the
paper's ref. [4]) with the maximal error criterion, which the paper's proof reaches by
expurgation. The decoder is not chosen: it is the sequential decoder (`seqError`) of the code's
own codeword vectors. `2^{nR}` is a real power (no rounding); `M ≥ 1` follows from it. Rates are
in bits. -/
def SeqAchievable {X : Type*} {I : Type} (W : X → I → ℂ) (R : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ M : ℕ, (2 : ℝ) ^ ((n : ℝ) * R) ≤ M ∧
    ∃ C : Fin M → Fin n → X, ∀ m, seqError (codeVecs W n C) m ≤ ε

end SeqHolevo


