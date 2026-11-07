-- Prove2me | Definitions.Def_MatroidEquitability_dualVector
-- name    : MatroidEquitability_dualVector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:48.350842+00:00
-- url     : https://prove2.me/theorems/a18aca2c-a78f-4d23-aebb-75e3b1eee881
-- title:
--   The vector $y=\sum_{B,D}\lambda_{B,D}(\mathbf 1_B-\mathbf 1_D)$
-- statement:
--   For $\lambda$ on $\mathcal F^+\times\mathcal F^-$, this is the vector
--
--   $$
--   y:=\sum_{B\in\mathcal F^+,\,D\in\mathcal F^-}\lambda_{B,D}\,(\mathbf 1_B-\mathbf 1_D),
--   $$
--
--   where $\mathbf 1_A$ is the characteristic vector of $A$. Its sign pattern is what complementary slackness controls.
--
--   **Formalization Note** $\lambda$ is a function on all pairs of sets; only its values on $\mathcal F^+\times\mathcal F^-$ enter.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Proof of Theorem 2, p.9 (PDF p.11)

import Mathlib

namespace MatroidEquitability

/-- The vector `y := Σ_{B∈F⁺, D∈F⁻} λ_{B,D} (1_B − 1_D)` of the proof of Theorem 2 (printed p.9 = PDF
p.11 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** The characteristic vector `1_A` is `A.indicator 1`, and `λ` is a function on
all pairs of sets of which only the values on `F⁺ × F⁻` matter. -/
noncomputable def dualVector {α : Type*} (Fp Fm : Finset (Set α)) (lam : Set α → Set α → ℝ)
    (e : α) : ℝ :=
  ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D * (B.indicator (1 : α → ℝ) e - D.indicator (1 : α → ℝ) e)

end MatroidEquitability


