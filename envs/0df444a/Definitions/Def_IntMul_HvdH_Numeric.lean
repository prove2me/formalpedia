-- Prove2me | Definitions.Def_IntMul_HvdH_Numeric
-- name    : IntMul_HvdH_Numeric
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-11T21:47:05.480631+00:00
-- url     : https://prove2.me/theorems/17eb637a-06bb-4c5a-a8dc-fb4843d9cf84
-- title:
--   Integer approximations of $\pi$ and $\log 2$ (Harvey–van der Hoeven §2.8)
-- statement:
--   Computable integer approximations used to obtain $\pi$ and $\log 2$ to $n$ bits.
--
--   * `atanInv x N K` $=\sum_{k<K}(-1)^k\lfloor 2^N/((2k+1)x^{2k+1})\rfloor$ approximates $2^N\arctan(1/x)$.
--   * `atanhInv x N K` $=\sum_{k<K}\lfloor 2^N/((2k+1)x^{2k+1})\rfloor$ approximates $2^N\operatorname{artanh}(1/x)$.
--   * `piApprox M` $=16\,$`atanInv 5 M M`$-4\,$`atanInv 239 M M` (Machin's formula) approximates $2^M\pi$.
--   * `log2Approx M` $=2\,$`atanhInv 3 M M` approximates $2^M\log 2$.
--   * `piBits n` and `log2Bits n` round `piApprox (2n+9)` and `log2Approx (2n+9)` to the nearest multiple of $2^{n+9}$ and divide, giving integers $u$ with $u/2^n\approx\pi$ resp. $\log 2$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.8 (computing pi and log 2 to p bits)

import Mathlib

/-! Integer approximations of π and log 2 (Harvey–van der Hoeven §2.8 / Lemma 2.12–2.13 style). -/

namespace IntMul.HvdH

open Finset

/-- Integer approximation of `2^N arctan(1/x)` from `K` series terms, each rounded down. -/
def atanInv (x N K : ℕ) : ℤ :=
  ∑ k ∈ range K, (-1) ^ k * ((2 ^ N / ((2 * k + 1) * x ^ (2 * k + 1)) : ℕ) : ℤ)

/-- Integer approximation of `2^N artanh(1/x)` from `K` series terms, each rounded down. -/
def atanhInv (x N K : ℕ) : ℤ :=
  ∑ k ∈ range K, ((2 ^ N / ((2 * k + 1) * x ^ (2 * k + 1)) : ℕ) : ℤ)

/-- Machin: integer approximation of `2^M π`. -/
def piApprox (M : ℕ) : ℤ := 16 * atanInv 5 M M - 4 * atanInv 239 M M

/-- `n`-bit approximation of `π`: `|piBits n / 2^n - π| ≤ 2^{-n}`. -/
def piBits (n : ℕ) : ℤ := (piApprox (2 * n + 9) + 2 ^ (n + 8)) / 2 ^ (n + 9)

/-- Integer approximation of `2^M log 2` (`log 2 = 2 artanh(1/3)`). -/
def log2Approx (M : ℕ) : ℤ := 2 * atanhInv 3 M M

/-- `n`-bit approximation of `log 2`: `|log2Bits n / 2^n - log 2| ≤ 2^{-n}`. -/
def log2Bits (n : ℕ) : ℤ := (log2Approx (2 * n + 9) + 2 ^ (n + 8)) / 2 ^ (n + 9)

end IntMul.HvdH


