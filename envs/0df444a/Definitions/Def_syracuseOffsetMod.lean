-- Prove2me | Definitions.Def_syracuseOffsetMod
-- name    : syracuseOffsetMod
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-09T07:54:57.97124+00:00
-- url     : https://prove2.me/theorems/864533ea-15c3-4810-a04c-d66a460333b7
-- title:
--   Positive geometric valuation vectors and the Syracuse affine offset
-- statement:
--   Let G_t be a vector of t independent positive geometric random variables, each with probability P(G_i=j)=2^{-j} for j=1,2,... (mean 2). For a finite valuation list a, define C([])=0 and C(a::b)=3^{length(b)}+2^a C(b). The Syracuse offset associated with a vector a of length t is
--
--   $$F_{t,k}(a)=C(a)\,2^{-\sum_i a_i}\quad\text{in }\mathbb{Z}/3^k\mathbb{Z}.$$
--
--   The inverse is taken in the residue ring, where powers of two are units. The package defines G_t, C, and F_{t,k}; it includes t=0 and k=0. These objects support comparisons between actual Syracuse iterates and geometric-offset distributions. No endpoint identity, mixing estimate, or convergence claim is asserted by these definitions.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, introduction equations (1.21) and (1.22), https://arxiv.org/html/1909.03562v7. Positive geometric coordinates are encoded by shifting Mathlib's zero-based geometric measure.

/-
  Reusable definitions for the positive-support geometric valuation model and
  the Syracuse affine offset modulo powers of three.

  This file intentionally contains definitions and essential probability
  instances only. Atom formulas, affine identities, and offset laws belong in
  separate theorem modules.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Geometric

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal unitInterval

noncomputable section

private def geomTwoParam : unitInterval :=
  ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

/-- The positive-support `Geom(2)` law, obtained by shifting Mathlib's law. -/
def positiveGeomTwo : Measure ℕ :=
  (geometricMeasure geomTwoParam).map Nat.succ

instance positiveGeomTwo_isProbabilityMeasure : IsProbabilityMeasure positiveGeomTwo :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- A finite independent vector of positive-support `Geom(2)` variables. -/
def positiveGeomTwoVector (t : ℕ) : Measure (Fin t → ℕ) :=
  Measure.pi (fun _ : Fin t => positiveGeomTwo)

instance positiveGeomTwoVector_isProbabilityMeasure (t : ℕ) :
    IsProbabilityMeasure (positiveGeomTwoVector t) := by
  rw [positiveGeomTwoVector]
  infer_instance

/-- The affine constant in the Syracuse valuation-prefix recurrence. -/
def syracuseAffineConstant : List ℕ → ℕ
  | [] => 0
  | a :: as => 3 ^ as.length + 2 ^ a * syracuseAffineConstant as

/-
  For a valuation vector `a`, this is the residue obtained by multiplying the
  affine constant by the inverse of its dyadic factor in `ZMod (3^k)`.
-/
def syracuseOffsetMod (t k : ℕ) (a : Fin t → ℕ) : ZMod (3 ^ k) :=
  (syracuseAffineConstant (List.ofFn a) : ZMod (3 ^ k)) *
    ((2 ^ (∑ i : Fin t, a i) : ℕ) : ZMod (3 ^ k))⁻¹


