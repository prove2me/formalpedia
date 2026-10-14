-- Prove2me | Definitions.Def_Zeta5_SourceGrowth
-- name    : Zeta5_SourceGrowth
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T14:44:35.845175+00:00
-- url     : https://prove2.me/theorems/6a82a0c2-f8a7-43fc-8e05-f071c8685aa5
-- title:
--   Zeta5: the weighted prime sum `psum` and the tail profile `F`
-- statement:
--   The weighted prime sum $\operatorname{psum} f a b K = \sum_{K/b < p \le K/a} p\,f(K/p)\log p$ (written as a sum over integers with the weight $c(k) = \log k$ for primes, $0$ otherwise) over which all growth estimates of the normaliser of the $\zeta(5)$ construction are stated, and the tail profile $F(x) = 4\lambda + 2\lambda\{x\} - 12\lambda\{\alpha x\}$ with $\lambda = 37/40$, $\alpha = 3/40$ and $\{\cdot\}$ the fractional part (source `Apery/Growth/TailPrime.lean`, formula (5.13)). `F` is the density whose weighted prime sum over $K/400 < p \le K/20$ produces the tail contribution $-0.05346\,K^2$ of Proposition 5.2. **Formalization Note** Nothing is proved in this module; the two definitions are reproduced verbatim from the source in the `Apery` namespace.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/PrimeSumStep.lean#L17-L19 and Apery/Growth/TailPrime.lean#L224-L227

import Mathlib
import Definitions.Def_Zeta5_SourcePrimeSum

/-!
# The weighted prime sum and the tail profile (source `Apery/PrimeSumStep.lean`,
# `Apery/Growth/TailPrime.lean`)

`psum f a b K = ∑_{K/b < p ≤ K/a} p f(K/p) log p` is the weighted prime sum over which the
growth estimates of the source project `mo271/Zeta5` are stated; `Ftail` is the profile

$$F(x) = 4\lambda + 2\lambda\{x\} - 12\lambda\{\alpha x\}, \qquad \lambda = 37/40,\
\alpha = 3/40,$$

of the tail range `K/400 < p ≤ K/20` (`Apery/Growth/TailPrime.lean`). Nothing is proved in
this module; the definitions are reproduced verbatim from the source.
-/

open Finset

namespace Apery

/-- `∑_{K/b < p ≤ K/a} p f(K/p) log p`, written as a sum over integers `k` with the weight
`cPrime`. -/
noncomputable def psum (f : ℝ → ℝ) (a b K : ℝ) : ℝ :=
  ∑ k ∈ Ioc ⌊K / b⌋₊ ⌊K / a⌋₊, (k : ℝ) * cPrime k * f (K / k)

/-- `F(x) = 4λ + 2λ{x} - 12λ{αx}`. -/
noncomputable def Ftail (x : ℝ) : ℝ :=
  4 * (37 / 40) + 2 * (37 / 40) * Int.fract x - 12 * (37 / 40) * Int.fract (3 / 40 * x)

end Apery


