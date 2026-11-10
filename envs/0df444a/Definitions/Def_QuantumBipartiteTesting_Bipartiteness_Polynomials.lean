-- Prove2me | Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Polynomials
-- name    : QuantumBipartiteTesting_Bipartiteness_Polynomials
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:10:55.395209+00:00
-- url     : https://prove2.me/theorems/d6e3b7fd-70ae-428a-b935-89f3f096209e
-- title:
--   The common denominator, explicit reciprocal, and uniform error notation
-- statement:
--   The bivariate common denominator and its multiplicity count are constructed explicitly:
--   $$D_q(M,\ell)=\prod_{a=1}^{2q}(M-(2a-1)\ell)^{\lfloor2q/a\rfloor},\qquad d_q=\sum_{a=1}^{2q}\lfloor2q/a\rfloor.$$
--   For each repeated affine factor, form $z_i=(M_0-M+(2a-1)\ell)/M_0$. Complete homogeneous polynomials are finite sums over all nonnegative multi-indices of a given total degree. The reciprocal polynomial is exactly
--   $$A_q=M_0^{-d_q}\sum_{j=0}^{4d_q+10}S_{q,j}.$$
--   Rational representability is a predicate asserting the existence of an actual denominator dividing $D_q$; it is a theorem conclusion, never circuit data. All rational identities are restricted away from their poles. The error is the difference of feasible and formal gaps. Uniform vanishing quantifies over all circuits and grid points before bounding that error by an arbitrary positive tolerance.
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), equations (4)–(5), (13), (16)–(20); Lemma 3.12, PDF = printed page 12,17–19. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_FormalMoments

namespace QuantumBipartiteTesting.Bipartiteness
open Finset MvPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Bivariate := MvPolynomial (Fin 2) ℝ

def Eval (P : Bivariate) (M l : ℝ) : ℝ := MvPolynomial.eval ![M,l] P

def Denominator (q : ℕ) : Bivariate :=
  ∏ a ∈ range (2*q), (X 0 - (C ((2*(a+1)-1 : ℕ) : ℝ) : Bivariate) * X 1) ^ (2*q/(a+1))

def DenominatorDegree (q : ℕ) : ℕ := ∑ a ∈ range (2*q), 2*q/(a+1)
def TruncationDegree (q : ℕ) : ℕ := 4 * DenominatorDegree q + 10

abbrev FactorIndex (q : ℕ) :=
  {i : Fin (2*q) × Fin (2*q) // i.2.val < 2*q/(i.1.val+1)}

def AffineFactor (N q : ℕ) (i : FactorIndex q) : Bivariate :=
  C ((Center N : ℝ)⁻¹) *
    (C (Center N : ℝ) - X 0 + (C ((2*(i.val.1.val+1)-1 : ℕ) : ℝ) : Bivariate) * X 1)

/-- Complete homogeneous polynomial, as a finite sum over all nonnegative multi-indices. -/
def Homogeneous {I : Type*} [Fintype I] (z : I → Bivariate) (j : ℕ) : Bivariate :=
  ∑ κ : I → Fin (j+1), if (∑ i, (κ i).val) = j then ∏ i, z i ^ (κ i).val else 0

def ReciprocalPolynomial (N q : ℕ) : Bivariate :=
  C ((Center N : ℝ) ^ DenominatorDegree q)⁻¹ *
    ∑ j ∈ range (TruncationDegree q + 1), Homogeneous (AffineFactor N q) j

/-- Explicit rational representability, including a denominator actually dividing D_q. -/
def RationalDegreeBound (q : ℕ) (Cdeg : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ numerator denominator : Bivariate,
    denominator ∣ Denominator q ∧
    (numerator.totalDegree : ℝ) ≤ Cdeg * DegreeScale q ∧
    ∀ M l : ℝ, l ≠ 0 → Eval (Denominator q) M l ≠ 0 →
      Eval denominator M l ≠ 0 ∧ f M l = Eval numerator M l / Eval denominator M l

def GapError {N k w q : ℕ} (E : Encoding (Fin N × Bool) k)
    (A : Algorithm (Address N 3) k w q)
    (out : (Address N 3 × Bits k) × Fin w → Bool) (M l : ℕ) : ℝ :=
  FeasibleGap E A out M l - FormalGap E A out M l

/-- Uniform convergence of the actual gap error, over every circuit and every grid point. -/
def UniformGapVanishing (c₀ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k w q : ℕ,
    (q : ℝ) ≤ c₀ * LowerBoundScale N →
    ∀ E : Encoding (Fin N × Bool) k, ∀ A : Algorithm (Address N 3) k w q,
    ∀ out : (Address N 3 × Bits k) × Fin w → Bool, ∀ M l : ℕ,
    Grid N M l → |GapError E A out M l| ≤ δ

end
end QuantumBipartiteTesting.Bipartiteness


