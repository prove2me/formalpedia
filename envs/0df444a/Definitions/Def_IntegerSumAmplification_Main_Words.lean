-- Prove2me | Definitions.Def_IntegerSumAmplification_Main_Words
-- name    : IntegerSumAmplification_Main_Words
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:02:05.793774+00:00
-- url     : https://prove2.me/theorems/86cacdee-0f31-4f25-aa90-962821ceb208
-- title:
--   Binary words, range widths and block encodings
-- statement:
--   An input of length $n$ is a Boolean word indexed by $0,\ldots,n-1$. A range of cardinality $r$ uses $\lceil\log_2 r\rceil$ bits, represented by the integer ceiling logarithm (zero bits when $r=1$). The value of a word $x$ is $\sum_i 2^i\mathbf 1\{x_i=1\}$, and encoding takes the corresponding low-order bits. Packing concatenates $k$ words of length $n$ in coordinate order; unpacking is its inverse. Joining concatenates two words. The integer sum of $k$ labels in $\{0,\ldots,m-1\}$ has range cardinality $k(m-1)+1$.
--
--   These conventions fix wire positions and word widths; they do not reduce a sum modulo $m$ or map invalid output codes to zero. The zero-width word has value zero. The computational results use positive ranges; the raw width helper is total also at zero.
-- source:
--   Farhan Ali and Weiqiang Yuan, Optimal Black-Box Hardness Amplification for Integer Sums, held manuscript dated November 3, 2026 (STOC 2027 submission; acceptance not asserted); citation_basis: published. §3, printed p. 8 / PDF p. 11; §6.2, printed pp. 17–19 / PDF pp. 20–22. PDF SHA256 181fd8ae5069b0c062ebccc0aa72d5a78ec0c836e6d8f6f99dd60464c0b746d7.

import Mathlib

namespace IntegerSumAmplification.Main

abbrev Bits (n : ℕ) := Fin n → Bool

def wordWidth (r : ℕ) : ℕ := Nat.clog 2 r

def decode {w : ℕ} (x : Bits w) : ℕ :=
  ∑ i : Fin w, if x i then 2 ^ i.val else 0

def encode (w a : ℕ) : Bits w := fun i => a.testBit i.val

def pack {k n : ℕ} (x : Fin k → Bits n) : Bits (k * n) :=
  fun i => x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

def unpack {k n : ℕ} (x : Bits (k * n)) : Fin k → Bits n :=
  fun i j => x (finProdFinEquiv (i, j))

def joinBits {a b : ℕ} (x : Bits a) (y : Bits b) : Bits (a + b) :=
  Fin.addCases x y

def sumRange (k m : ℕ) : ℕ := k * (m - 1) + 1

end IntegerSumAmplification.Main


