-- Prove2me | Definitions.Def_PLCMarkets_Rationality_EncodingSize
-- name    : PLCMarkets_Rationality_EncodingSize
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:57:45.167205+00:00
-- url     : https://prove2.me/theorems/06c9bcba-eb01-4c37-bac9-59bf8ac59398
-- title:
--   Bit size of a rational number and encoding size of a Fisher market
-- statement:
--   The **bit size** of a rational number $q=a/b$ in lowest terms ($b>0$) is the number of binary digits of $|a|$ plus that of $b$:
--   $$\operatorname{bits}(q)=\lceil\log_2(|a|+1)\rceil+\lceil\log_2(b+1)\rceil .$$
--
--   The **encoding size** of a piecewise-linear concave utility with bounded segments $(c_1,a_1),\dots,(c_m,a_m)$ and last slope $c_\infty$ is
--   $$m+\sum_{k=1}^m\bigl(\operatorname{bits}(c_k)+\operatorname{bits}(a_k)\bigr)+\operatorname{bits}(c_\infty),$$
--   and the **encoding size** of a Fisher market with $n$ buyers, $g$ goods, budgets $e(i)$ and utilities $f^i_j$ is
--   $$\|M\|=n+g+\sum_{i}\operatorname{bits}(e(i))+\sum_{i,j}\bigl(\text{encoding size of } f^i_j\bigr).$$
--
--   These sizes make precise the phrase "can be written using polynomially many bits" of Theorem 4.1: every rational parameter of the market and every segment counts.
--
--   **Formalization Note.** The binary length of a natural number is `Nat.size`. Any encoding size polynomially equivalent to this one yields the same notion of "polynomially many bits".
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, https://doi.org/10.1145/1970392.1970394, p. 10:9, THEOREM 4.1 ("polynomially many bits"); data of §2, pp. 10:6-10:7

import Mathlib
import Definitions.Def_PLCMarkets_Rationality_FisherMarket

namespace PLCMarkets.Rationality

/-- The number of bits of a rational number written as a reduced fraction: the binary length of
the absolute value of its numerator plus that of its denominator. -/
def bitSize (q : ℚ) : ℕ :=
  Nat.size q.num.natAbs + Nat.size q.den

/-- The encoding size of a piecewise-linear concave function: one unit per segment, plus the bits
of every slope and every amount, plus the bits of the slope of the last, unbounded piece. -/
def PLConcave.encodingSize (f : PLConcave) : ℕ :=
  f.segs.length + (f.segs.map (fun s => bitSize s.1 + bitSize s.2)).sum + bitSize f.tail

/-- The encoding size of a Fisher market: the numbers of buyers and goods, the bits of every
budget, and the encoding size of every utility function `f^i_j`. -/
def FisherMarket.encodingSize {n g : ℕ} (M : FisherMarket n g) : ℕ :=
  n + g + ∑ i, bitSize (M.budget i) + ∑ i, ∑ j, (M.util i j).encodingSize

end PLCMarkets.Rationality


