-- Prove2me | Definitions.Def_FuchsThesis_Coding_expLength
-- name    : FuchsThesis_Coding_expLength
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:20:55.574506+00:00
-- url     : https://prove2.me/theorems/4007a133-bcc3-4f20-ba84-2f7e5d54ae5e
-- title:
--   Expected codeword length $\bar l = \sum_i p(x_i)\, l(x_i)$
-- statement:
--   Let messages $x_1,\dots,x_n$ occur with probabilities $p(x_1),\dots,p(x_n)$ and let $c$ be a binary code, with $l(x_i)$ the number of binary digits in the codeword of $x_i$. The **expected (average) codeword length** of $c$ is
--
--   $$
--   \bar l = \sum_i p(x_i)\, l(x_i).
--   $$
--
--   In the language of questioning schemes it is the expected number of yes/no questions needed to identify the outcome. For the four-outcome example of the source, $p = (\tfrac1{20}, \tfrac15, \tfrac14, \tfrac12)$, the four schemes of Figure 2.1 have $\bar l = 2.70,\ 2.00,\ 2.55,\ 1.75$.
--
--   **Formalization Note** Defined for any real weights on a finite type of messages; lengths are natural numbers cast to reals. The theorems assume the weights form a probability distribution.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (2.133), p.37 (PDF p.46)

import Mathlib

namespace FuchsThesis.Coding

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (2.133), p.37 (PDF p.46): the expected (average) codeword length
`l̄ = ∑ᵢ p(xᵢ) l(xᵢ)` of a code `c` for messages occurring with probabilities `p`, where `l(xᵢ)`
"is the number of digits in the code word for `xᵢ`".

**Formalization Note.** Defined for any real weights `p` on a finite type of messages; the
theorems assume `p` is a probability distribution. Lengths are natural numbers cast to `ℝ`. -/
noncomputable def expLength {ι : Type*} [Fintype ι] (p : ι → ℝ) (c : ι → List Bool) : ℝ :=
  ∑ x, p x * ((c x).length : ℝ)

end FuchsThesis.Coding


