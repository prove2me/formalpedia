-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Cokernels
-- name    : DetSupportRank_DeterminantSupport_Cokernels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:45.062435+00:00
-- url     : https://prove2.me/theorems/e1f18119-56ef-43f0-ba03-2cb8ad1fc4e7
-- title:
--   The fixed cokernel and its row-column initial replacement
-- statement:
--   Given source and target shifts $a,b$, a polynomial matrix $A$ homogeneous in degrees $a_j-b_i$, and a chosen $k$ with $\det A\mid D^k$, define
--   $$N=\operatorname{im}A,\quad M=P^b/N,\quad N^\sharp=\operatorname{in}(N),\quad M^\sharp=P^b/N^\sharp.$$
--   Every target basis vector has row shift $b_i$ and column shift zero. The same actual quotient has both row-column pieces and row-only pieces. Natural-exponent integer tests are embedded into the Laurent ring without changing signs or coefficients.
--
--   The construction contains no assertion about annihilation or K-polynomials. Lemmas 5.15–5.19 supply those properties for these fixed objects.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §§5.5–5.6, pp.21–23; §5.1, p.16, p. 21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_DeterminantFamily
import Definitions.Def_DetSupportRank_DeterminantSupport_TestIdeal
import Definitions.Def_DetSupportRank_DeterminantSupport_InitialModules
import Definitions.Def_DetSupportRank_DeterminantSupport_Regrading

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport

/-- Nonnegative source shifts embedded in the true integer degree group. -/
def integerShifts {N n : ℕ} (b : Fin N → Fin n → ℕ) : Fin N → Fin n → ℤ :=
  fun i j => (b i j : ℤ)

/-- The witness conditions on the very matrix used to form the cokernel. -/
def IsRelationWitness {K : Type*} [Field K] {n N : ℕ}
    (D : MvPolynomial (Fin n × Fin n) K) (a b : Fin N → Fin n → ℕ)
    (A : Matrix (Fin N) (Fin N) (MvPolynomial (Fin n × Fin n) K)) (k : ℕ) : Prop :=
  (∀ i j, Homogeneous rowWeight
    (fun t => (a j t : ℤ) - (b i t : ℤ)) (A i j)) ∧ A.det ∣ D ^ k

/-- M = P^b / im A, with its row grading, §5.5. -/
def rowCokernel {K : Type*} [Field K] {n N : ℕ}
    (b : Fin N → Fin n → ℕ)
    (A : Matrix (Fin N) (Fin N) (MvPolynomial (Fin n × Fin n) K)) :=
  quotientModuleData rowWeight (integerShifts b) (matrixImage A)

/-- The fixed initial module N♯, §5.6; each target basis vector has column shift zero. -/
def rowColumnInitial {K : Type*} [Field K] {n N : ℕ}
    (b : Fin N → Fin n → ℕ)
    (A : Matrix (Fin N) (Fin N) (MvPolynomial (Fin n × Fin n) K)) :=
  initialModule rowWeight columnWeight (integerShifts b) (fun _ _ => 0) (matrixImage A)

/-- The actual M♯ with both row and column pieces. -/
def bigradedCokernel {K : Type*} [Field K] {n N : ℕ}
    (b : Fin N → Fin n → ℕ)
    (A : Matrix (Fin N) (Fin N) (MvPolynomial (Fin n × Fin n) K)) :=
  quotientModuleData (pairDegrees rowWeight columnWeight)
    (fun i => Sum.elim (integerShifts b i) (fun _ => 0)) (rowColumnInitial b A)

/-- The same constructed quotient M♯ with only row pieces. -/
def rowInitialCokernel {K : Type*} [Field K] {n N : ℕ}
    (b : Fin N → Fin n → ℕ)
    (A : Matrix (Fin N) (Fin N) (MvPolynomial (Fin n × Fin n) K)) :=
  quotientModuleData rowWeight (integerShifts b) (rowColumnInitial b A)

/-- The natural-exponent integer test polynomial as a Laurent polynomial. -/
def naturalToLaurent {n : ℕ} (q : MvPolynomial (Fin n) ℤ) :
    AddMonoidAlgebra ℤ (Fin n → ℤ) :=
  (AddMonoidAlgebra.coeff q).sum fun e c =>
    AddMonoidAlgebra.single (fun i => (e i : ℤ)) c

end DetSupportRank.DeterminantSupport


