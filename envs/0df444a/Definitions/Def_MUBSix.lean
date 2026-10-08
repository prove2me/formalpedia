-- Prove2me | Definitions.Def_MUBSix
-- name    : MUBSix
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:17.940713+00:00
-- url     : https://prove2.me/theorems/1708c215-7c85-42a5-99dd-1da3609b4c7d
-- statement:
--   This block sets up the sixth-order mutually unbiased bases problem in the namespace MUB6. Coordinates are Fin 6, CMatrix is the space of 6×6 complex matrices, and a charge is an integer-valued exponent vector on the coordinates. IsHadamard(H) means every entry of H has modulus 1 and H*H = 6·I, so H is a complex Hadamard matrix. The character of a complex vector x at charge a is the product over i of x_i raised to the integer power a_i; g(H,a) is (1/6) times the sum over columns k of the character of column k of H at charge a. The specific charge alpha is (1,1,1,-1,-1,-1), and permuteCharge(π,a) precomposes a charge with a permutation of coordinates. Equivalent(H,K) is full Hadamard equivalence: K arises from H by permuting rows and columns and multiplying row i by a unit-modulus complex phase u_i and column j by a unit-modulus phase v_j, so K_ij = u_i H_{r(i),c(j)} v_j. With omega = exp(2πi/3), taoExponent is a specific 6×6 natural-number matrix with entries 0, 1, 2 (2 standing for exponent -1 mod 3), whose first row and column are zero and whose remaining 5×5 block is a five-cycle pattern; tao is the complex matrix with entries omega raised to those exponents. Space is 6-dimensional complex Euclidean space and Basis is an orthonormal basis of it indexed by Fin 6. IsMUBFamily(B) for a family of n bases means that for any two distinct bases r≠s and any vectors i, j in them, the squared modulus of their inner product is exactly 1/6. Attainable(n) is the defined proposition that some family of n such bases exists; the block states no results about which n are attainable.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MUBSix.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MUBSix.lean; bytes 16..1674
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

abbrev Coord := Fin 6
abbrev CMatrix := Matrix Coord Coord ℂ
abbrev Charge := Coord → ℤ

def IsHadamard (H : CMatrix) : Prop :=
  (∀ i j, Complex.normSq (H i j) = 1) ∧
  H.conjTranspose * H = (6 : ℂ) • (1 : CMatrix)

def character (x : Coord → ℂ) (a : Charge) : ℂ := ∏ i, x i ^ a i

def g (H : CMatrix) (a : Charge) : ℂ :=
  (6 : ℂ)⁻¹ * ∑ k, character (fun i => H i k) a

def alpha : Charge := ![1, 1, 1, -1, -1, -1]

def permuteCharge (π : Equiv.Perm Coord) (a : Charge) : Charge := a ∘ π

/-- Full Hadamard equivalence, with arbitrary unit complex phases. -/
def Equivalent (H K : CMatrix) : Prop :=
  ∃ (r c : Equiv.Perm Coord) (u v : Coord → ℂ),
    (∀ i, Complex.normSq (u i) = 1) ∧ (∀ j, Complex.normSq (v j) = 1) ∧
    ∀ i j, K i j = u i * H (r i) (c j) * v j

def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- The five-cycle exponent matrix in equation (cubic-matrix).
The entries 2 represent the exponents -1 modulo three. -/
def taoExponent : Matrix Coord Coord ℕ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 1, 2, 2, 1;
     0, 1, 0, 1, 2, 2;
     0, 2, 1, 0, 1, 2;
     0, 2, 2, 1, 0, 1;
     0, 1, 2, 2, 1, 0]

def tao : CMatrix := fun i j => omega ^ taoExponent i j

abbrev Space := EuclideanSpace ℂ Coord
abbrev Basis := OrthonormalBasis Coord ℂ Space

def IsMUBFamily {n : ℕ} (B : Fin n → Basis) : Prop :=
  ∀ r s, r ≠ s → ∀ i j,
    Complex.normSq (inner ℂ (B r i) (B s j)) = (1 : ℝ) / 6

def Attainable (n : ℕ) : Prop := ∃ B : Fin n → Basis, IsMUBFamily B



end MUB6
end
end OAI


