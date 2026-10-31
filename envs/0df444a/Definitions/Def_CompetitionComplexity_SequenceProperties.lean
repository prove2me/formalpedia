-- Prove2me | Definitions.Def_CompetitionComplexity_SequenceProperties
-- name    : CompetitionComplexity_SequenceProperties
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:41.428038+00:00
-- url     : https://prove2.me/theorems/2f1a1901-69e5-4658-9a9d-1c6c5e3a2a0d
-- title:
--   Increments $\partial S_n=S_{n+1}-S_n$ and properties (a)–(c) of a sequence
-- statement:
--   Given a real sequence $(S_n)_{n\in\mathbb N}$ (indices start at $0$), its **increment sequence** is
--   $$
--   \partial S_n=S_{n+1}-S_n\qquad(n\ge0).
--   $$
--   The paper considers three properties:
--
--   1. **(a)** $(S_n)$ is strictly increasing;
--   2. **(b)** $(\partial S_n)$ is non-increasing;
--   3. **(c)** the ratio sequence $(\partial S_{n+1}/\partial S_n)$ is non-decreasing.
--
--   Under (a) every increment is positive, so the ratios in (c) are well defined; under (b)–(c) they lie in $(0,1]$ and converge. Lemma 1 shows that $(A_n(F))$ has these properties, and Lemma 3 shows that every sequence with $S_0=0$, (a)–(c) and $\partial S_n\to0$ arises as $(A_n(G))$ for some distribution $G$.
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, §3, p.7 (∂S_n and properties (a)–(c))

import Mathlib

namespace CompetitionComplexity

/-- **The increment sequence `∂Sₙ = Sₙ₊₁ − Sₙ`.**
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), §3, p.7: "we denote by
(∂Sn)n∈N the sequence such that ∂Sn = Sn+1 − Sn for every non-negative integer n."

**Formalization Note.** Indices are 0-based as in the paper (`ℕ` includes `0`). -/
def dS (S : ℕ → ℝ) (n : ℕ) : ℝ := S (n + 1) - S n

/-- **Property (a)**, §3, p.7: "The sequence (Sn)n∈N is strictly increasing." -/
def PropA (S : ℕ → ℝ) : Prop := StrictMono S

/-- **Property (b)**, §3, p.7: "The sequence (∂Sn)n∈N is non-increasing." -/
def PropB (S : ℕ → ℝ) : Prop := Antitone (dS S)

/-- **Property (c)**, §3, p.7: "The sequence (∂Sn+1/∂Sn)n∈N is non-decreasing."

**Formalization Note.** The ratio uses real division; under property (a) every `∂Sₙ` is
positive, so no division by zero occurs where (c) is used together with (a). -/
def PropC (S : ℕ → ℝ) : Prop := Monotone (fun n => dS S (n + 1) / dS S n)

end CompetitionComplexity


