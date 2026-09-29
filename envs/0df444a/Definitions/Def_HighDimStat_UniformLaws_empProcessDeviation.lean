-- Prove2me | Definitions.Def_HighDimStat_UniformLaws_empProcessDeviation
-- name    : HighDimStat_UniformLaws_empProcessDeviation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:27:16.233346+00:00
-- url     : https://prove2.me/theorems/afc6bbd8-c9b7-4674-8c12-ad18a61509bc
-- title:
--   The empirical process deviation ||Pn - P||_F (Eq. 4.7)
-- statement:
--   **Eq. (4.7).** The **empirical process deviation**
--
--   $$
--   \|\mathbb P_n-P\|_F \;:=\; \sup_{f\in F}\Big|\frac1n\sum_{i=1}^n f(X_i) - \mathbb E[f(X)]\Big|,
--   $$
--
--   measuring the absolute deviation between the sample average and the population average,
--   uniformly over a function class $F=\{f_j,j\in\iota\}$. This is the quantity Theorem 4.10
--   bounds.
--
--   **Formalization Note** $\mathbb E[f(X)]$ is realized via a fixed population variable $X_0$
--   sharing the samples' common law (rather than a separately axiomatized distribution object),
--   and the class $F$ is realized as the range of an index family $f:\iota\to D\to\mathbb R$
--   rather than a `Set (D → ℝ)`, following the standard representation of a (possibly infinite)
--   function class by an index type.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 100 (PDF p. 120), Eq. (4.7)

import Mathlib

open MeasureTheory

namespace HighDimStat.UniformLaws

/-- **Eq. (4.7)**, Wainwright, *High-Dimensional Statistics* (2019), p. 100. The empirical
process deviation `‖Pₙ-P‖_F := sup_{f∈F} |(1/n)∑ᵢf(Xᵢ) - E[f(X)]|`, for a function class
`F = {f_j, j∈ι}`, a sample `X₁,...,Xₙ`, and a population variable `X₀` with the shared law. -/
noncomputable def empProcessDeviation {D ι Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (f : ι → D → ℝ)
    (Xs : ℕ → Ω → D) (X0 : Ω → D) (Prob : Measure Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ⨆ j : ι, |(1 / (n : ℝ)) * ∑ i ∈ Finset.range n, f j (Xs i ω) - ∫ ω', f j (X0 ω') ∂Prob|

end HighDimStat.UniformLaws


