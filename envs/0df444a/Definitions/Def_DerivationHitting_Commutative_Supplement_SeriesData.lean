-- Prove2me | Definitions.Def_DerivationHitting_Commutative_Supplement_SeriesData
-- name    : DerivationHitting_Commutative_Supplement_SeriesData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:54:04.017605+00:00
-- url     : https://prove2.me/theorems/1a505de3-4ad6-49ec-99b5-12dde2c82746
-- title:
--   Formal iterated-integral series and its rational-linear extension
-- statement:
--   For a field F, formal coefficientwise integration with zero constant term sends a series h to the series with degree-k coefficient h_{k−1}/k for k>0 and coefficient 0 at k=0. For each letter numbered i=1,…,n, set
--
--   $$b_i(t)=\frac{i}{1+it}=\sum_{k\ge0}(-1)^ki^{k+1}t^k,\qquad I_\varnothing=1,\qquad I_{x_iw}=\int_0^t b_i(z)I_w(z)\,dz.$$
--
--   The map Ψ sums these word series F-linearly. A separate function extends it F(t)-linearly into F((t)), using the canonical embedding of rational functions and power series into Laurent series. The field-characteristic restriction is imposed by the theorems; over characteristic zero all positive integer divisors are nonzero. These are algebraic formal series, without analytic convergence assumptions. Ψ is not an algebra homomorphism to scalar series.
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026). Canonical submission artifact, not proceedings publication; no arXiv pin. Printed page = PDF page throughout 1–29. pp.16–17, §5.1; p.20, Lemma 5.11.

import Definitions.Def_DerivationHitting_Commutative_Supplement_NCABPData
open scoped RatFunc

namespace DerivationHitting.Commutative.Supplement
noncomputable section

/-- Zero-constant coefficientwise formal primitive. -/
def formalPrimitive {F : Type*} [Field F] (h : PowerSeries F) : PowerSeries F :=
  PowerSeries.mk fun k => if k = 0 then 0 else PowerSeries.coeff (k - 1) h / (k : F)

/-- The expansion of i/(1+it), where the source's i is i.val+1. -/
def plusKernelSeries {F : Type*} [Field F] {n : ℕ} (i : Fin n) : PowerSeries F :=
  PowerSeries.mk fun k => (-1 : F) ^ k * ((i.val + 1 : ℕ) : F) ^ (k + 1)

def wordPsi {F : Type*} [Field F] {n : ℕ} : List (Fin n) → PowerSeries F
  | [] => 1
  | i :: w => formalPrimitive (plusKernelSeries i * wordPsi w)

/-- The F-linear iterated-integral map; this is not scalar algebra substitution. -/
def psi {F : Type*} [Field F] {n : ℕ} (f : NCPoly F n) : PowerSeries F :=
  f.coeff.sum fun w c => c • wordPsi w.toList

/-- The F(t)-linear extension, using the canonical rational-to-Laurent embedding. -/
def rationalPsi {F : Type*} [Field F] {n : ℕ} (f : NCPoly (RatFunc F) n) : LaurentSeries F :=
  f.coeff.sum fun w c => algebraMap (RatFunc F) (LaurentSeries F) c *
    algebraMap (PowerSeries F) (LaurentSeries F) (wordPsi (F := F) w.toList)

end
end DerivationHitting.Commutative.Supplement


