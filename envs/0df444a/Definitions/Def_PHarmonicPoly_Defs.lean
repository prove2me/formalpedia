-- Prove2me | Definitions.Def_PHarmonicPoly_Defs
-- name    : PHarmonicPoly_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T14:01:03.214436+00:00
-- url     : https://prove2.me/theorems/b2d2e868-d156-4a62-9301-962155c3a008
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from na0b (na0b/pharmonicpoly-lean; see pinned Apache-2.0 LICENSE)'s pinned Affineness of p-harmonic polynomials in n-dimensional Euclidean space development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/Defs.lean

module
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
set_option autoImplicit false
@[expose] public section
@[expose] public section
section EpOp
noncomputable def EpOp {n : ℕ} (p : ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => ‖gradient u x‖ ^ 2 * Laplacian.laplacian u x
    + (p - 2) * iteratedFDeriv ℝ 2 u x ![gradient u x, gradient u x]
end EpOp
section TrigPolyLe
def TrigPolyLe (m : ℕ) (T : ℝ → ℝ) : Prop :=
  ∃ a b : ℕ → ℝ, ∀ t : ℝ,
    T t = ∑ k ∈ Finset.range (m + 1), (a k * Real.cos (k * t) + b k * Real.sin (k * t))
end TrigPolyLe


