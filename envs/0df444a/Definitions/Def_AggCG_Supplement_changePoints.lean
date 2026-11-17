-- Prove2me | Definitions.Def_AggCG_Supplement_changePoints
-- name    : AggCG_Supplement_changePoints
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:20:04.63169+00:00
-- url     : https://prove2.me/theorems/7e7303a6-0d6b-4bea-a64f-614d5a9c4e6a
-- title:
--   Change points of a parameterized output path
-- statement:
--   A parameter value is a **change point** of an output path $F:\mathbb R\to Y$ if $F$ is not constant on any open neighborhood of that value. The associated count is the cardinality of the change points in a specified parameter window.
--
--   The count takes values in $\mathbb N\cup\{\infty\}$, so an infinite transition set cannot silently become zero.
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem 3.3, p.4, PDF p.5; Theorem E.11, p.34, PDF p.35

import Mathlib

namespace AggCG.Supplement

/-- The parameter values at which a parameter-indexed output `F` **changes**: the points `t₀` such that
`F` is not constant on any open interval around `t₀` (Sharma, *Computational Complexity of Data-Driven
Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission
(manuscript sha256 f7ea0248…), Theorem 3.3, p.4, PDF p.5: "finite exponents α ∈ Θ at which the complete
power-mean linkage hierarchy changes"; Theorem E.11, p.34, PDF p.35: "changes in the optimal cut on
s ∈ (0, ∞)").

**Formalization Note** A change point is a point where `F` is not locally constant; an isolated value
produced by the tie rule at a single parameter counts as a change. The counting set is intersected with
the parameter window of each theorem, and is counted with `Set.encard` in `ℕ∞`, so an infinite set of
change points is not silently counted as `0`. -/
def changePoints {β : Type*} (F : ℝ → β) : Set ℝ :=
  {t₀ | ¬ ∃ ε > 0, ∀ t : ℝ, |t - t₀| < ε → F t = F t₀}

/-- The number of change points of `F` inside the window `Θ`, in `ℕ∞`. -/
noncomputable def changeCount {β : Type*} (F : ℝ → β) (Θ : Set ℝ) : ℕ∞ :=
  (changePoints F ∩ Θ).encard

end AggCG.Supplement


