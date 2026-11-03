-- Prove2me | Definitions.Def_levy_foundations_isPositiveDefinite
-- name    : levy_foundations_isPositiveDefinite
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T14:23:56.99897+00:00
-- url     : https://prove2.me/theorems/125cf680-a3f0-4af8-bedf-7b7e05314906
-- title:
--   Positive-definite complex functions on the real line
-- statement:
--   A complex-valued function φ on ℝ is positive definite if every finite Hermitian quadratic form formed from differences of sample points has a nonnegative real value (and vanishing imaginary part).
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/PositiveDefinite.lean#L39-L44. Positive-definiteness predicate. Independent Prove2Me statement, pending audit and remote compilation.

import Mathlib.Analysis.Matrix.PosDef

open ComplexConjugate Finset
open scoped ComplexOrder
namespace LevyFoundations
def isPositiveDefinite (φ : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j)
end LevyFoundations


