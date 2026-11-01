-- Prove2me | Definitions.Def_SeqHolevo_codeAvgError
-- name    : SeqHolevo_codeAvgError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:01:09.286891+00:00
-- url     : https://prove2.me/theorems/611cc2ea-765b-4b9d-9cef-a2107f440118
-- title:
--   Average error of the sequential decoder of a code
-- statement:
--   For a fixed codebook with $|\mathcal M|=M\ge1$ messages, the error probability of the sequential decoder averaged over a uniformly random message:
--
--   $$\frac1M\sum_{m=1}^M\Big(1-\operatorname{Tr}\{\varphi_{x^n(m)}\hat\Pi_{m-1}\cdots\hat\Pi_1\varphi_{x^n(m)}\hat\Pi_1\cdots\hat\Pi_{m-1}\varphi_{x^n(m)}\}\Big).$$
--
--   Its expectation over the random codebook is the quantity (8) bounded in Appendix B.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, eq. (8), p.6

import Mathlib
import Definitions.Def_SeqHolevo_seqError
import Definitions.Def_SeqHolevo_codeVecs

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, p.6 (PDF page), (8): for a fixed codebook `C`, the error probability of the
sequential decoder averaged over a uniformly random message `M`,
`(1/|𝓜|) Σ_m (1 − Tr{φ_{xⁿ(m)} Π̂_{m−1} ⋯ Π̂_1 φ_{xⁿ(m)} Π̂_1 ⋯ Π̂_{m−1} φ_{xⁿ(m)}})`. Its expectation
over the random codebook is (8).

**Formalization Note.** Uniform weights `1/M`; the mission uses it with `M ≥ 1`. 0-based
messages. -/
noncomputable def codeAvgError {X : Type*} {I : Type} (W : X → I → ℂ) (n : ℕ) {M : ℕ}
    (C : Fin M → Fin n → X) : ℝ :=
  (∑ m, seqError (codeVecs W n C) m) / M

end SeqHolevo


