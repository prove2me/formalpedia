-- Prove2me | Definitions.Def_LowRankMisspec_RankOne_Rounding
-- name    : LowRankMisspec_RankOne_Rounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:15:44.759415+00:00
-- url     : https://prove2.me/theorems/72bff493-916a-463d-b570-f9a9121f10ef
-- title:
--   Largest-remainder rounding of a probability row to denominator $2^b$ (§E.2)
-- statement:
--   To round a row $p\in\Delta([\sigma])$ to denominator $2^b$: floor each $2^b p[a]$ and allocate the remaining $R=2^b-\sum_a\lfloor 2^b p[a]\rfloor$ integer units, one each, to the symbols with the largest fractional remainders $\{2^b p[a]\}$. `IsLRRounding b p n` says that $n$ arises this way for some tie-break: there is a set $S$ of $R$ symbols whose remainders are at least those of every symbol outside $S$, and $n[a]=\lfloor 2^b p[a]\rfloor+\mathbf 1[a\in S]$. The rounded row is $n/2^b$ (`dyadicRow b n`).
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 39 (PDF 40), Appendix E.2

import Mathlib
import Definitions.Def_LowRankMisspec_RankOne_Laws

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace LowRankMisspec.RankOne

/-!
# Largest-remainder rounding of a row to denominator `2^b` (§E.2)

Hasrati, Risteski, *Understanding Model Misspecification in Low-Rank Distributions: Tolerant
Testing and Agnostic Learning*, STOC 2027 submission (manuscript sha256 235f2a4f…), Appendix E.2,
p. 39 (PDF 40).

"To round a row `p`, floor each `2^b p[b]` and allocate the remaining integer units to the largest
fractional remainders." `IsLRRounding b p n` says that the integer vector `n` arises this way for
some tie-break: with `R = 2^b − Σ_a ⌊2^b p[a]⌋` remaining units, there is a set `S` of `R` symbols
whose fractional remainders `frac(2^b p[a])` are at least those of every symbol outside `S`, and
`n[a] = ⌊2^b p[a]⌋ + 1[a ∈ S]`. The rounded row is `dyadicRow b n = n / 2^b`.
-/

/-- `n` is a largest-remainder rounding of the row `p` to denominator `2^b` (ties broken
arbitrarily). -/
def IsLRRounding {σ : ℕ} (b : ℕ) (p : Fin σ → ℝ) (n : Fin σ → ℕ) : Prop :=
  ∃ S : Finset (Fin σ),
    S.card = 2 ^ b - ∑ a, ⌊(2 : ℝ) ^ b * p a⌋₊ ∧
    (∀ a ∈ S, ∀ a' ∉ S, Int.fract ((2 : ℝ) ^ b * p a') ≤ Int.fract ((2 : ℝ) ^ b * p a)) ∧
    ∀ a, n a = ⌊(2 : ℝ) ^ b * p a⌋₊ + if a ∈ S then 1 else 0

/-- The dyadic row `n / 2^b`. -/
def dyadicRow {σ : ℕ} (b : ℕ) (n : Fin σ → ℕ) : Fin σ → ℝ :=
  fun a => (n a : ℝ) / 2 ^ b

end LowRankMisspec.RankOne


