-- Prove2me | Definitions.Def_FastFourierTransform_opCount
-- name    : FastFourierTransform_opCount
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T18:10:44.172987+00:00
-- url     : https://prove2.me/theorems/367a9b8c-987f-4ed8-b3ed-bb06dee03acf
-- title:
--   Arithmetic cost model of the radix-2 butterfly recursion
-- statement:
--   The **arithmetic cost model** of the radix-2 Cooley–Tukey recursion on $n=2^p$ points, as two natural-number recursions. A transform of $2^{p+1}$ points makes two recursive calls on $2^p$ points and then merges them with $2^p$ butterflies; each butterfly performs one twiddle-factor multiplication and two complex additions. Hence
--
--   $$M(0)=0,\quad M(p+1)=2M(p)+2^{p},\qquad A(0)=0,\quad A(p+1)=2A(p)+2^{p+1},$$
--
--   with $M$ counting complex multiplications and $A$ complex additions. Both are ordinary recursions on natural numbers and refer to no complex arithmetic themselves; they are the model against which the $\tfrac n2\log_2 n$ and $n\log_2 n$ counts are stated.
-- source:
--   Fast Fourier transform, Wikipedia (snapshot supplied by the mission captain's user), https://en.wikipedia.org/wiki/Fast_Fourier_transform, section 'Definition' (radix-2 Cooley–Tukey: '(n/2)log_2 n complex multiplications and n log_2 n complex additions')

import Mathlib

namespace FastFourierTransform

/-- Number of complex multiplications performed by the radix-2 Cooley–Tukey butterfly
recursion on `2 ^ p` sample points: two recursive calls on half-size inputs, plus one
twiddle-factor multiplication for each of the `2 ^ p` butterflies of the merge stage. -/
def fftMulCount : ℕ → ℕ
  | 0 => 0
  | (p + 1) => 2 * fftMulCount p + 2 ^ p

/-- Number of complex additions performed by the radix-2 Cooley–Tukey butterfly recursion
on `2 ^ p` sample points: two recursive calls on half-size inputs, plus two additions for
each of the `2 ^ p` butterflies of the merge stage. -/
def fftAddCount : ℕ → ℕ
  | 0 => 0
  | (p + 1) => 2 * fftAddCount p + 2 ^ (p + 1)

end FastFourierTransform


