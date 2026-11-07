-- Prove2me | Definitions.Def_DynBrooks_Patterns
-- name    : DynBrooks_Patterns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:10.564367+00:00
-- url     : https://prove2.me/theorems/f96151b5-7999-45fb-950a-c38887297908
-- title:
--   §5.2 — the collision-pattern sum $W_m$
-- statement:
--   For $\Delta\ge3$ let
--
--   $$\alpha=\frac{\Delta}{\Delta-2},\qquad u_k=\frac{2^k}{(\Delta-1)^{\lfloor k/2\rfloor}}.$$
--
--   A **pattern** of length $m$ is a binary string; a one stands for a collision and a zero for an arrival without one. A pattern is admissible if between consecutive ones there are at least three zeros. Its **weight** is the product of $\alpha$ for every one and $u_k$ for every maximal zero run of length $k$; the initial and final zero runs may be empty ($u_0=1$). $W_m$ is the sum of the weights of all admissible patterns of length $m$; the empty pattern has weight $W_0=1$.
--
--   For example, $000100010$ has weight $u_3\alpha u_3\alpha u_1$.
--
--   **Formalization Note** A pattern is a list of booleans, and its zero runs are obtained by splitting at the ones (`List.splitOn`).
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), §5.2, p.59 (PDF 61)

import Mathlib

namespace DynBrooks

/-! # The collision-pattern sum `W_m`

Mishra, Mukherjee, *Fully Dynamic Brooks Coloring* (STOC 2027 submission, sha256 6542a9f1…), §5.2,
p.59 (PDF 61): `α = ∆/(∆ − 2)`, `u_k = 2^k / (∆ − 1)^{⌊k/2⌋}`. A collision is a one and an arrival
without a collision is a zero; between consecutive ones there are at least three zeros. A pattern's
weight multiplies `α` per one and `u_k` per maximal zero run of length `k`, where the initial and final
zero runs may be empty, and `W_m` sums these weights over all such patterns of length `m`.

**Formalization Note.** A pattern is a `List Bool` (`true` = one). `List.splitOn true` returns its
zero runs: the first, the ones between consecutive ones, and the last, the outer ones possibly empty;
the empty pattern has the single run `[]`, of weight `u_0 = 1`. Check: `000100010` has runs of lengths
`3, 3, 1` and weight `u₃ α u₃ α u₁`. -/

/-- `α = ∆/(∆ − 2)`. -/
noncomputable def alpha (Δ : ℕ) : ℝ := (Δ : ℝ) / ((Δ : ℝ) - 2)

/-- `u_k = 2^k / (∆ − 1)^{⌊k/2⌋}`. -/
noncomputable def uRun (Δ k : ℕ) : ℝ := (2 : ℝ) ^ k / ((Δ : ℝ) - 1) ^ (k / 2)

/-- The zero runs of a pattern. -/
def zeroRuns (p : List Bool) : List (List Bool) := p.splitOn true

/-- The weight of a pattern: `α` per one and `u_k` per zero run of length `k`. -/
noncomputable def patternWeight (Δ : ℕ) (p : List Bool) : ℝ :=
  alpha Δ ^ p.count true * ((zeroRuns p).map fun r => uRun Δ r.length).prod

/-- Between consecutive ones there are at least three zeros: every zero run other than the first and
the last has length at least `3`. -/
def IsSpaced (p : List Bool) : Prop :=
  ∀ r ∈ (zeroRuns p).tail.dropLast, 3 ≤ r.length

instance (p : List Bool) : Decidable (IsSpaced p) := by unfold IsSpaced; infer_instance

/-- All binary patterns of length `m`. -/
def allPatterns : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (allPatterns m).flatMap fun l => [false :: l, true :: l]

/-- `W_m`: the sum of the weights over all spaced binary patterns of length `m`. -/
noncomputable def W (Δ m : ℕ) : ℝ :=
  (((allPatterns m).filter IsSpaced).map (patternWeight Δ)).sum

end DynBrooks


