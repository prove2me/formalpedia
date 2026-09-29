-- Prove2me | Definitions.Def_Rudin_ch03_series
-- name    : Rudin_ch03_series
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T18:59:16.199773+00:00
-- url     : https://prove2.me/theorems/dc9f5b4d-9aab-4486-b0bc-d209e3b78c32
-- title:
--   Partial sums and convergence of a series
-- statement:
--   Rudin's notion of a convergent series: $\sum a_n$ converges to $s$ when the partial sums $s_n = a_0 + \dots + a_{n-1}$ converge to $s$ (Definition 3.21), and converges absolutely when $\sum \|a_n\|$ converges (Section 3.45). This is deliberately *not* Mathlib's `Summable`/`HasSum`, which express unconditional summability and are equivalent to absolute convergence for real and complex terms; the distinction between conditional and absolute convergence is the subject of the chapter, so the partial-sum formulation is needed.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, pp. 58, 71, Definitions 3.21 and Section 3.45

import Mathlib

/-!
# Rudin, Chapter 3 — series and their partial sums

Definitions transcribed from Walter Rudin, *Principles of Mathematical Analysis*, 3rd edition,
Chapter 3 (Definitions 3.21 and 3.23, Section 3.45).

Convergence of a *sequence* is Mathlib's `Filter.Tendsto … atTop (nhds …)` and is reused.
Convergence of a *series* is not: Rudin's $\sum a_n$ converges when the sequence of partial
sums $s_n = a_0 + \dots + a_{n-1}$ converges, which for real or complex terms is strictly weaker
than Mathlib's `Summable`/`HasSum` (those express unconditional summability, equivalent to
absolute convergence in this setting).  Since Chapter 3 is largely about the difference between
conditional and absolute convergence — its capstone is the Riemann rearrangement theorem — the
partial-sum notions are introduced explicitly here.
-/

namespace Rudin

/-- The `n`-th partial sum `a 0 + a 1 + ⋯ + a (n-1)` of the series `∑ aₙ`. -/
def partialSum {M : Type*} [AddCommMonoid M] (a : ℕ → M) (n : ℕ) : M :=
  ∑ i ∈ Finset.range n, a i

/-- Rudin, Definition 3.21: the series `∑ aₙ` **converges to** `s` if its partial sums converge
to `s`. -/
def SeriesConvergesTo {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (a : ℕ → M) (s : M) :
    Prop :=
  Filter.Tendsto (partialSum a) Filter.atTop (nhds s)

/-- Rudin, Definition 3.21: the series `∑ aₙ` **converges** if its partial sums converge. -/
def SeriesConverges {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (a : ℕ → M) : Prop :=
  ∃ s, SeriesConvergesTo a s

/-- Rudin, Definition 3.45: the series `∑ aₙ` **converges absolutely** if `∑ ‖aₙ‖` converges. -/
def SeriesConvergesAbsolutely {E : Type*} [NormedAddCommGroup E] (a : ℕ → E) : Prop :=
  SeriesConverges fun n => ‖a n‖

end Rudin


