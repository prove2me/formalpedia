-- Prove2me | Definitions.Def_DerivativeChain_root_probability
-- name    : DerivativeChain_root_probability
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-17T18:37:17.57445+00:00
-- url     : https://prove2.me/theorems/eb1fc212-95c6-4d8f-9bc8-882e3790c072
-- title:
--   Normalized probability on actual polynomial roots
-- statement:
--   For a complex polynomial P, a complex point z, and an index w in the finite set of distinct roots of P, rootProbability is the Gauss--Lucas derivative-root weight at w divided by the sum of all those weights. Mathlib incorporates multiplicities and the shared-root case in derivRootWeight. No claim of normalization is made at degree zero; subsequent theorems assume positive degree. The probability, mean, and support properties are proved separately.
-- source:
--   Derivative-zero chains: public formalization reference, R02, DerivativeChain_root_probability. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false

noncomputable section
namespace DerivativeChain

/-- Normalized Gauss--Lucas weights, indexed only by actual roots of `P`. -/
def rootProbability (P : ℂ[X]) (z : ℂ) (w : P.roots.toFinset) : ℝ :=
  P.derivRootWeight z w / ∑ v ∈ P.roots.toFinset, P.derivRootWeight z v

end DerivativeChain


