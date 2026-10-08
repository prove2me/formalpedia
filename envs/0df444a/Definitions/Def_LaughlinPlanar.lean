-- Prove2me | Definitions.Def_LaughlinPlanar
-- name    : LaughlinPlanar
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:17.207544+00:00
-- url     : https://prove2.me/theorems/cbef58b2-14dd-4fbf-a135-1e81ab5081be
-- statement:
--   The block sets up a finite-dimensional fermionic model for a planar Laughlin-type problem. gammaStar is the explicit constant 4616733319001/10^14. For naturals p,x,y, pairLimitCoefficient(p,x,y) is zero unless x+y=p+1, in which case it equals (x−y)·√(p!/(2^p x! y!))/√2. In the Fock part, an orbital space is ℂ^(Q+1) indexed by Fin(Q+1), and the Fock space is its exterior algebra over ℂ. annihilate(i) is the contraction (interior product) of the exterior algebra against the ith coordinate functional, and the occupation basis is indexed by finite subsets A of the orbitals, namely the wedge monomials. OccupationBidegree(Q,n,w,x) says that x has nonzero coordinates only on subsets with exactly n elements whose indices sum to w. In the planar part, occupation sets for L are subsets of Fin(L+1). For a coefficient array c, pairMatrix(L,c) is the matrix whose (A,B) entry is the sum over i,j of c(i,j) times the A-coordinate of the result of annihilating orbital i and then j from basis state B. planarCoefficient(p,i,j) is pairLimitCoefficient(p,i,j)/√2, so it carries a second factor 1/√2, and planarPairMatrix(L,p) is the pair matrix of these coefficients. planarHamiltonian(L) is the sum over p=0,…,2L of P_p^† P_p, where P_p is planarPairMatrix(L,p). pairEnergy(L,P,x) is the sum over p≤2L and basis sets A of |(P_p x)_A|^2, and squareNorm(L,H,x) is the sum over A of |(Hx)_A|^2. A HomogeneousState for N consists of one Fock vector for each degree L, with the Lth vector supported on exactly N-element subsets whose indices sum to L. Its fullEnergy is the extended-real sum over L of the planar pair energy of its coordinates, and fullSquareNorm is the corresponding sum of squared norms under the planar Hamiltonian. These are definitions only, with no theorem asserted, and gammaStar is not used by the other constructions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LaughlinPlanar.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LaughlinPlanar.lean; bytes 16..2821
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Laughlin
open scoped BigOperators Matrix ENNReal

noncomputable def gammaStar : ℝ := 4616733319001 / 10^14

noncomputable def pairLimitCoefficient (p x y : ℕ) : ℝ :=
  if x+y = p+1 then
    ((x : ℝ)-(y : ℝ)) * Real.sqrt ((p.factorial : ℝ) /
      (((2 : ℕ) : ℝ)^p * (x.factorial : ℝ) * (y.factorial : ℝ))) / Real.sqrt (2 : ℕ)
  else 0

namespace Fock

abbrev Orbital (Q : ℕ) := Fin (Q+1) → ℂ
abbrev Space (Q : ℕ) := ExteriorAlgebra ℂ (Orbital Q)

noncomputable def annihilate {Q : ℕ} (i : Fin (Q+1)) : Module.End ℂ (Space Q) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i)

noncomputable def occupationBasis (Q : ℕ) :
    Module.Basis (Finset (Fin (Q+1))) ℂ (Space Q) :=
  (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra

def OccupationBidegree (Q n w : ℕ) (x : Space Q) : Prop :=
  ∀ A : Finset (Fin (Q+1)), (A.card ≠ n ∨ (∑ i ∈ A, i.val) ≠ w) →
    (occupationBasis Q).repr x A = 0

end Fock

namespace Planar
open Fock

abbrev Occupations (L : ℕ) := Finset (Fin (L+1))

noncomputable def pairMatrix (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ) :
    Matrix (Occupations L) (Occupations L) ℂ := fun A B =>
  ∑ i, ∑ j, c i j * (occupationBasis L).repr
    (annihilate j (annihilate i (occupationBasis L B))) A

noncomputable def planarCoefficient (p i j : ℕ) : ℂ :=
  ((pairLimitCoefficient p i j / Real.sqrt (2 : ℕ) : ℝ) : ℂ)

noncomputable def planarPairMatrix (L p : ℕ) : Matrix (Occupations L) (Occupations L) ℂ :=
  pairMatrix L (fun i j => planarCoefficient p i.val j.val)

noncomputable def planarHamiltonian (L : ℕ) : Matrix (Occupations L) (Occupations L) ℂ :=
  ∑ p ∈ Finset.range (2*L+1), (planarPairMatrix L p)ᴴ * planarPairMatrix L p

noncomputable def pairEnergy (L : ℕ)
    (P : ℕ → Matrix (Occupations L) (Occupations L) ℂ) (x : Occupations L → ℂ) : ℝ :=
  ∑ p ∈ Finset.range (2*L+1), ∑ A, ‖(P p *ᵥ x) A‖^2

noncomputable def squareNorm (L : ℕ) (H : Matrix (Occupations L) (Occupations L) ℂ)
    (x : Occupations L → ℂ) : ℝ := ∑ A, ‖(H *ᵥ x) A‖^2

/-- Occupation coefficients with fixed particle number in every homogeneous degree. -/
structure HomogeneousState (N : ℕ) where
  block : (L : ℕ) → Space L
  homogeneous : ∀ L, OccupationBidegree L N L (block L)

noncomputable def fullEnergy {N : ℕ} (ψ : HomogeneousState N) : ℝ≥0∞ :=
  ∑' L, ENNReal.ofReal (pairEnergy L (planarPairMatrix L)
    (fun A => (occupationBasis L).repr (ψ.block L) A))

noncomputable def fullSquareNorm {N : ℕ} (ψ : HomogeneousState N) : ℝ≥0∞ :=
  ∑' L, ENNReal.ofReal (squareNorm L (planarHamiltonian L)
    (fun A => (occupationBasis L).repr (ψ.block L) A))

end Planar



end Laughlin
end OAI


