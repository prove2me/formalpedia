-- Prove2me | Definitions.Def_KadisonSimilarity
-- name    : KadisonSimilarity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:16.44466+00:00
-- url     : https://prove2.me/theorems/da5a5e72-811b-486b-b72a-0e9aa88da628
-- statement:
--   This block sets up the formal framework for Kadison's similarity problem and related commutator estimates for von Neumann algebras; everything is a definition or defined proposition, not an established theorem. For a C*-algebra A and a complex Hilbert space H, BoundedUnitalHom(A,H) is the type of continuous unital ℂ-algebra homomorphisms π from A to the bounded operators on H, and SimilarToStar(π) says there is an invertible bounded operator S with Sπ(a*)S⁻¹ = (Sπ(a)S⁻¹)* for every a, meaning π is similar to a *-homomorphism. The commutator of S and T in a normed ring is ST − TS. For n copies of H (an ℓ² direct sum), matrixOperator turns an n×n matrix of bounded operators into an operator on the n-fold sum, amplify(Y,n) is the diagonal operator Y⊕…⊕Y, and innerDerivation(Y) is the bounded map X ↦ YX − XY. For a von Neumann algebra P, scalarCommutatorNorm(P,Y) is the norm of this derivation restricted to P. CommutatorEstimate(P,C) says that for every bounded Y, every n, and every n×n matrix X with entries in P, ‖[amplify(Y,n), matrixOperator(X)]‖ ≤ C·scalarCommutatorNorm(P,Y)·‖matrixOperator(X)‖. UniformCommutatorEstimate(C) requires this for all von Neumann algebras on all Hilbert spaces in universe u, and UniversalCommutatorTheorem is the proposition that some constant C ≥ 0 works. SimilarityTheorem is the proposition that, for every C*-algebra A and Hilbert space K, every bounded unital homomorphism A → B(K) is similar to a *-homomorphism. For a von Neumann algebra M, a CommutantProjection is a self-adjoint idempotent in its commutant, offDiagonalSeminorm(M,T) is the supremum over these projections e of ‖(1−e)Te‖, and UniversalHyperreflexivity(C) says that for every von Neumann algebra M on every Hilbert space in universe u and every bounded T, the distance from T to M is at most 2C times offDiagonalSeminorm(M,T). Finally, explicit real constants are defined: rowConstant = 4√2, cyclicConstant = (1+4·rowConstant)², cornerConstant = 6π²(1+4·cyclicConstant), factorConstant = max(3·cornerConstant+2, 1+2·rowConstant, 2), and universalConstant = 3·factorConstant+2.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KadisonSimilarity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KadisonSimilarity.lean; bytes 16..3944
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace KadisonSimilarity

universe u v

section Homomorphisms

variable (A H : Type*) [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev BoundedUnitalHom :=
  {π : A →ₐ[ℂ] (H →L[ℂ] H) // Continuous π}

def SimilarToStar (π : BoundedUnitalHom A H) : Prop :=
  ∃ S : (H →L[ℂ] H)ˣ, ∀ a : A,
    (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
      star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H))

end Homomorphisms

section Commutators

variable {R : Type*} [NormedRing R]

def commutator (S T : R) : R := S * T - T * S

end Commutators

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section

attribute [-instance] NonUnitalCStarAlgebra.toNormedSpace


abbrev HilbertCopies (H : Type u) (n : ℕ) := PiLp 2 (fun _ : Fin n => H)

def matrixOperator {n : ℕ} (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    HilbertCopies H n →L[ℂ] HilbertCopies H n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ∑ j : Fin n, (X i j).comp (PiLp.proj 2 (fun _ : Fin n => H) j))

def amplify (Y : H →L[ℂ] H) (n : ℕ) :
    HilbertCopies H n →L[ℂ] HilbertCopies H n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => Y.comp (PiLp.proj 2 (fun _ : Fin n => H) i))

def innerDerivation (Y : H →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  ContinuousLinearMap.mul ℂ (H →L[ℂ] H) Y -
    (ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip Y

variable [CompleteSpace H]

def scalarCommutatorNorm (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) : ℝ := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  exact ‖(innerDerivation Y).comp P.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL‖

def CommutatorEstimate (P : VonNeumannAlgebra H) (C : ℝ) : Prop :=
  ∀ (Y : H →L[ℂ] H) (n : ℕ) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)),
    (∀ i j, X i j ∈ P) →
    ‖commutator (amplify Y n) (matrixOperator X)‖ ≤
      C * scalarCommutatorNorm P Y * ‖matrixOperator X‖

def UniformCommutatorEstimate (C : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (P : VonNeumannAlgebra K), CommutatorEstimate P C

def UniversalCommutatorTheorem : Prop := ∃ C : ℝ, 0 ≤ C ∧ UniformCommutatorEstimate.{u} C

def SimilarityTheorem : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (K : Type v) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (π : BoundedUnitalHom A K),
    SimilarToStar A K π

abbrev CommutantProjection (M : VonNeumannAlgebra H) :=
  {e : H →L[ℂ] H // e ∈ M.commutant ∧ star e = e ∧ e * e = e}

def offDiagonalSeminorm (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) : ℝ :=
  sSup (Set.range fun e : CommutantProjection M =>
    ‖(1 - (e : H →L[ℂ] H)) * T * (e : H →L[ℂ] H)‖)

def UniversalHyperreflexivity (C : ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra K) (T : K →L[ℂ] K),
    Metric.infDist T (M : Set (K →L[ℂ] K)) ≤ 2 * C * offDiagonalSeminorm M T

end


def rowConstant : ℝ := 4 * Real.sqrt 2
def cyclicConstant : ℝ := (1 + 4 * rowConstant) ^ 2
def cornerConstant : ℝ := 6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant)
def factorConstant : ℝ := max (max (3 * cornerConstant + 2) (1 + 2 * rowConstant)) 2
def universalConstant : ℝ := 3 * factorConstant + 2



end KadisonSimilarity
end
end OAI


