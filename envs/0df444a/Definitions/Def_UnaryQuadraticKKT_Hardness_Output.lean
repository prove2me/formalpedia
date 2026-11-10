-- Prove2me | Definitions.Def_UnaryQuadraticKKT_Hardness_Output
-- name    : UnaryQuadraticKKT_Hardness_Output
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:46:23.875295+00:00
-- url     : https://prove2.me/theorems/1af6cf0e-3b01-4a2e-b993-62eeb5aec1f7
-- title:
--   The integer output polynomial, coefficient collection and no-constant matrix conversion
-- statement:
--   Construct the integer multivariate polynomial $H$ by substituting $u_{r,j}=2v_{r,j}-1$ into every exact chain and summing over the computed dyadic terms. Enumerate the original coordinates first, then the auxiliary blocks and their coordinates in order. Let $d$ be the resulting list length and $h_0$ the collected constant coefficient. The output rational quadratic $P_{\rm out}$ uses the collected coefficients of $H-h_0$:
--   $$
--   Q_{ii}^{\rm out}=2[X_i^2]H,\qquad Q_{ij}^{\rm out}=[X_iX_j]H\ (i\ne j),\qquad c_i^{\rm out}=[X_i]H.
--   $$
--   Integer coefficients are embedded in the public rational representation. Coefficient mass is the sum of absolute values of all collected coefficients of $H$, including the constant. The binary data length convention is $N=n+\sum_t(1+\operatorname{bits}(|a_t|)+\operatorname{bits}(b_t))$, where each source coefficient is reduced to $a_t/b_t$ and the sum includes zero slots.
--
--   These are actual polynomial operations and coefficient extractions; neither semantic equality nor efficient computability is assumed. The goal separately asserts the equality with $H-h_0$, the quantitative bounds, and the polynomial-time construction with decoding of every target answer.
--
--   **Formalization Note** Only the computed scalar $h_0$ is omitted when returning to the no-constant convention of Equation (2). This preserves all derivatives. $N$ is a coefficient payload length; the public self-delimiting binary code and the unary output code also charge their delimiters.
-- source:
--   Argyrios Deligkas, Michail Fasoulakis, Stavros Ioannidis, STOC 2027 submission #1093 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1093.pdf, Section 4.2, Equation (6), p.6; Section 4.4, p.10; Section 4.5, pp.10–11. Canonical PDF SHA256 f4a6f774376cfc40e24acff39a11029782994f72d85350d10b69fc17030bd0a5

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Combined

set_option autoImplicit false
noncomputable section

namespace UnaryQuadraticKKT.Hardness
open Finset NetworkEquilibriumCLS.LinearNash

/-- Integer symbolic implementation of Eq. (6); f and h may be constants or shared variables. -/
def chainPolynomial {ι : Type*} [DecidableEq ι] (k : ℕ) (s : ℤ)
    (f h : MvPolynomial ι ℤ) (u : Fin (k + 2) → MvPolynomial ι ℤ) : MvPolynomial ι ℤ :=
  3 * ∑ i : Fin (k + 1),
    (2 * u ⟨i.val, by omega⟩ - u ⟨i.val + 1, by omega⟩) ^ 2 +
  9 * (u ⟨k + 1, by omega⟩) ^ 2 - 6 * f * u ⟨0, by omega⟩ +
  6 * MvPolynomial.C s * h * u ⟨k + 1, by omega⟩ + f ^ 2 + h ^ 2

def factorPolynomial {n : ℕ} (p : Quadratic n) (a : Option (Fin n)) :
    MvPolynomial (CombinedIndex p) ℤ := a.elim 1 (fun i => MvPolynomial.X (.inl i))

/-- Exact integer polynomial H; its constant is retained here. -/
def outputPolynomial {n : ℕ} (p : Quadratic n) : MvPolynomial (CombinedIndex p) ℤ :=
  ∑ r : TermIndex p,
    chainPolynomial (termAt p r).exponent (termAt p r).sign
      (factorPolynomial p (termAt p r).left) (factorPolynomial p (termAt p r).right)
      (fun j => 2 * MvPolynomial.X (.inr ⟨r, j⟩) - 1)

/-- Explicit enumeration: original coordinates, then each complete auxiliary block in order. -/
def coordinateOrder {n : ℕ} (p : Quadratic n) : List (CombinedIndex p) :=
  (List.finRange n).map Sum.inl ++
  (List.finRange (dyadicTerms p).length).flatMap fun r =>
    (List.finRange ((termAt p r).exponent + 2)).map fun j => Sum.inr ⟨r, j⟩

def outputDimension {n : ℕ} (p : Quadratic n) : ℕ := (coordinateOrder p).length

def coordinateAt {n : ℕ} (p : Quadratic n) (i : Fin (outputDimension p)) : CombinedIndex p :=
  (coordinateOrder p)[i]

/-- Return to the public matrix representation; the computed constant coefficient is omitted.
Q_ii is twice the square coefficient, whereas Q_ij is the coefficient of X_i X_j. -/
def outputQuadratic {n : ℕ} (p : Quadratic n) : Quadratic (outputDimension p) where
  Q i j := if i = j then
    2 * (((outputPolynomial p).coeff (Finsupp.single (coordinateAt p i) 2) : ℤ) : ℚ)
    else (((outputPolynomial p).coeff
      (Finsupp.single (coordinateAt p i) 1 + Finsupp.single (coordinateAt p j) 1) : ℤ) : ℚ)
  c i := (((outputPolynomial p).coeff (Finsupp.single (coordinateAt p i) 1) : ℤ) : ℚ)
  symmetric i j := by
    by_cases h : i = j
    · subst j; rfl
    · simp only [h, Ne.symm h, ↓reduceIte, add_comm]

def outputConstant {n : ℕ} (p : Quadratic n) : ℤ := (outputPolynomial p).coeff 0

/-- Absolute sum over collected coefficients, including the constant. -/
def outputCoefficientMass {n : ℕ} (p : Quadratic n) : ℕ :=
  ∑ a ∈ (outputPolynomial p).support, ((outputPolynomial p).coeff a).natAbs

/-- Binary length convention used for L ≤ 2N+1; all source coefficients and n are charged. -/
def binaryDataLength {n : ℕ} (p : Quadratic n) : ℕ := n +
  ((slots n).map fun t => 1 + (coefficient p t).num.natAbs.bits.length +
    (coefficient p t).den.bits.length).sum

end UnaryQuadraticKKT.Hardness


