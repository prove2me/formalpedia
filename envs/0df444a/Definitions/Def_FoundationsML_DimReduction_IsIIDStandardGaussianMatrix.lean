-- Prove2me | Definitions.Def_FoundationsML_DimReduction_IsIIDStandardGaussianMatrix
-- name    : FoundationsML_DimReduction_IsIIDStandardGaussianMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:27:58.411984+00:00
-- url     : https://prove2.me/theorems/0dd1ebda-8c6e-41b5-9065-5ced362ee786
-- title:
--   Matrix with i.i.d. standard normal entries
-- statement:
--   **Lemma 15.3, p. 355, PDF p. 372.** A random matrix $A\in\mathbb R^{k\times N}$ whose
--   entries are sampled independently from the standard normal distribution $N(0,1)$: every
--   entry $A_{ij}$ has law $N(0,1)$, and the entries are jointly independent.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 355, Lemma 15.3 (PDF p. 372)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace FoundationsML.DimReduction

/-- A random matrix `A : Ω → Matrix (Fin k) (Fin N) ℝ` whose entries are sampled independently
from the standard normal distribution `N(0,1)` (Mohri, Rostamizadeh & Talwalkar, *Foundations
of Machine Learning*, 2nd ed., MIT Press 2018, Lemma 15.3, p. 355, PDF p. 372): every entry
`A_{ij}` has law `N(0,1)`, and the entries are (jointly) independent.

**Formalization Note.** Marginal law and independence are stated as two separate conjuncts,
following the book's own two-part phrasing ("entries... are sampled independently from the
standard normal distribution"); independence is expressed via `iIndepFun` over the product
index type `Fin k × Fin N`, matching the book's "for all `i, j`" scope exactly. -/
structure IsIIDStandardGaussianMatrix {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    {k N : ℕ} (A : Ω → Matrix (Fin k) (Fin N) ℝ) : Prop where
  isGaussian : ∀ i j, Measure.map (fun ω => A ω i j) Prob = gaussianReal 0 1
  indep : iIndepFun (fun (p : Fin k × Fin N) (ω : Ω) => A ω p.1 p.2) Prob

end FoundationsML.DimReduction


