-- Prove2me | Definitions.Def_FuchsThesis_Coding_minLength
-- name    : FuchsThesis_Coding_minLength
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:37.897818+00:00
-- url     : https://prove2.me/theorems/6eaec26b-8b3c-4178-9285-6fe43a495c18
-- title:
--   Minimal average codeword length $\bar l_{\min}$ of a binary instantaneous code
-- statement:
--   Let messages $x_1,\dots,x_n$ occur with probabilities $p(x_1),\dots,p(x_n)$. The **minimal average codeword length** for a binary instantaneous coding of these messages is
--
--   $$
--   \bar l_{\min} = \inf\Big\{ \sum_i p(x_i)\, l(x_i) \;:\; c \text{ a binary instantaneous code for } x_1,\dots,x_n \Big\},
--   $$
--
--   where $l(x_i)$ is the length of the codeword $c(x_i)$. It is the least expected number of binary questions with which the outcome of sampling $p$ can be discerned.
--
--   **Formalization Note** The source writes "minimal"; the definition takes the infimum (`sInf` in $\mathbb R$) over the set of expected lengths of all instantaneous codes. That set is never empty (the code $x_k \mapsto 1\cdots10$ with $k$ ones is instantaneous) and, for nonnegative $p$, it is bounded below by $0$, so the infimum is a genuine one; both facts are proved in the mission's sanity file. (The infimum is in fact attained, by a Huffman code.)
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Theorem 2.8, p.39 (PDF p.48); eq. (2.133), p.37

import Mathlib
import Definitions.Def_FuchsThesis_Coding_IsInstantaneous
import Definitions.Def_FuchsThesis_Coding_expLength

namespace FuchsThesis.Coding

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Theorem 2.8, p.39 (PDF p.48): the minimal average codeword length
`l̄_min` for a binary instantaneous coding of messages occurring with probabilities `p`, i.e. the
least value of `l̄ = ∑ᵢ p(xᵢ) l(xᵢ)` (2.133) over all binary instantaneous codes.

**Formalization Note.** The minimum is written as the infimum (`sInf` in `ℝ`) of the set of
expected lengths of all instantaneous codes `c : ι → List Bool`. For a finite message type this set
is nonempty (e.g. the code `xₖ ↦ 1…10` with `k` ones) and, for nonnegative `p`, bounded below by
`0`, so `sInf` is the genuine infimum; both facts are proved in
`Solutions/verification/FuchsThesis_Coding_sanity.lean`. -/
noncomputable def minLength {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  sInf {l : ℝ | ∃ c : ι → List Bool, IsInstantaneous c ∧ l = expLength p c}

end FuchsThesis.Coding


