-- Prove2me | Definitions.Def_KSATWindow_CoverTime
-- name    : KSATWindow_CoverTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:03.857739+00:00
-- url     : https://prove2.me/theorems/ad9cf7ea-056c-4af2-a8b9-d24293943b43
-- title:
--   Cover times of i.i.d. random subsets: $T$, the last uncovered set $\mathcal T$, and $c(A)$
-- statement:
--   Let $X$ be a finite set and $Y_1,Y_2,\dots$ independent copies of a random subset of $X$ with law $\nu$. This module defines:
--
--   1. the law of the sequence $Y_1,Y_2,\dots$;
--   2. for $A\subseteq X$, the first time $m$ with $A\subseteq Y_1\cup\dots\cup Y_m$ (infinite if there is none), and the cover time $T$ of $X$;
--   3. the last uncovered set $\mathcal T=X\setminus\bigcup_{i<T}Y_i$;
--   4. $c(A)$, the expected time to cover $A$ using a fresh independent sequence with the same law.
--
--   These are the objects of Aldous's covering inequality (Theorem 4.1 of the paper).
--
--   **Formalization Note** A random subset is its membership indicator $X\to\{0,1\}$; its law is an arbitrary probability measure. Hitting times take values in $\mathbb N\cup\{\infty\}$ and expected cover times in $[0,\infty]$, so they are never junk values.
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), Theorem 4.1, p.8 (Aldous [5], Theorem 1(b))

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace KSATWindow

/-!
# Cover times of i.i.d. random subsets of a finite set

G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), Theorem 4.1, p.8 (Aldous [5],
Theorem 1(b)).

`X` is a finite set and `Y₁, Y₂, …` are independent copies of a random subset of `X`.

**Formalization Note.**
* A random subset of `X` is its membership indicator `X → Bool`, with the product σ-algebra
  (discrete, since `X` is finite). Its law `ν` is an arbitrary probability measure on `X → Bool`.
* The sequence is `ω : ℕ → X → Bool` with law `Measure.infinitePi (fun _ => ν)`; `ω i` is
  `Y_{i+1}`, so "`i < T`" in the paper's 1-based indexing is `i + 1 < T` here.
* Hitting times are in `ℕ∞` (`⊤` when the sets never cover), and expectations of them are
  `ℝ≥0∞`-valued lower integrals, so an expected cover time is never a junk value.
-/

variable {X : Type*}

/-- The law of the sequence `Y₁, Y₂, …` of independent copies of a random subset with law `ν`. -/
noncomputable def subsetStreamLaw [Fintype X] (ν : Measure (X → Bool)) [IsProbabilityMeasure ν] :
    Measure (ℕ → X → Bool) :=
  Measure.infinitePi fun _ : ℕ => ν

/-- The first time `m` such that `Y₁ ∪ ⋯ ∪ Y_m ⊇ A` (`⊤` if there is none). -/
noncomputable def coverTimeOf (A : Set X) (ω : ℕ → X → Bool) : ℕ∞ :=
  sInf ((fun m : ℕ => (m : ℕ∞)) '' {m | ∀ x ∈ A, ∃ i < m, ω i x = true})

/-- The cover time `T` of `X`: the first time the sets cover `X`. -/
noncomputable def coverTime (ω : ℕ → X → Bool) : ℕ∞ :=
  coverTimeOf Set.univ ω

/-- The last uncovered set `𝒯 = X \ ⋃_{i<T} Y_i` (1-based indices), i.e. the points missed by
`Y₁, …, Y_{T−1}`. Defined through `T.toNat`; `T = ⊤` is a null event under the hypotheses of
Theorem 4.1. -/
noncomputable def lastUncovered (ω : ℕ → X → Bool) : Set X :=
  {x | ∀ i : ℕ, i + 1 < (coverTime ω).toNat → ω i x = false}

/-- `c(A)`: the expected time to cover a deterministic `A ⊆ X` using a fresh independent sequence
with the same law. -/
noncomputable def coverMean [Fintype X] (ν : Measure (X → Bool)) [IsProbabilityMeasure ν]
    (A : Set X) : ℝ≥0∞ :=
  ∫⁻ ω, ((coverTimeOf A ω : ℕ∞) : ℝ≥0∞) ∂(subsetStreamLaw ν)

end KSATWindow


