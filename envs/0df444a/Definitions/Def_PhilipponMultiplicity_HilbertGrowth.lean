-- Prove2me | Definitions.Def_PhilipponMultiplicity_HilbertGrowth
-- name    : PhilipponMultiplicity_HilbertGrowth
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-27T07:33:35.871601+00:00
-- url     : https://prove2.me/theorems/c8cc16b1-8e18-4861-b48d-3d5b4d423f54
-- title:
--   Total-degree filtration of a multiprojective coordinate quotient
-- statement:
--   The degree-$n$ filtration is the image in $R/I$ of coordinate polynomials of total degree at most $n$. Its vector-space dimension is the cumulative Hilbert function. The finite set of multidegrees with coordinate sum at most $n$ indexes the graded pieces. These are actual subspaces and their dimensions; no growth or Krull-dimension formula is assumed.
-- source:
--   Auxiliary definitions for Philippon (1986), §3, printed pp. 362–364: https://www.numdam.org/articles/10.24033/bsmf.2060/ .

import Definitions.Def_PhilipponMultiplicity_SectionThree

/-! The actual filtration by total coordinate degree. No growth or dimension
comparison is included in these definitions. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K]

def degreeFiltration (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) (n : ℕ) :
    Submodule K (M.CoordinateRing ⧸ I) :=
  (MvPolynomial.restrictTotalDegree M.Variable K n).map (Ideal.Quotient.mkₐ K I).toLinearMap

def cumulativeHilbertFunction (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (n : ℕ) : ℕ := Module.finrank K (degreeFiltration M I n)

def multidegreesLe (M : MultiProjectiveSpace K) (n : ℕ) : Finset (M.FactorIndex → ℕ) := by
  classical
  exact (Finset.Iic (fun _ => n)).filter (fun d => ∑ i, d i ≤ n)

end PhilipponMultiplicity.Hilbert


