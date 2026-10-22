-- Prove2me | Definitions.Def_BraneBrauer_Orthogonal_Setting
-- name    : BraneBrauer_Orthogonal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T09:27:40.148059+00:00
-- url     : https://prove2.me/theorems/49a3a14b-bd23-4757-b9d9-a81a6505a0a6
-- title:
--   Mixed tensor space, Brauer image, partial transpose, and branching system
-- statement:
--   Let $V=\mathbb C^N$. The mixed tensor space $V^{\otimes m}\otimes\bar V^{\otimes n}$ has basis labels consisting of one $m$-tuple and one $n$-tuple of elements of $\{1,\ldots,N\}$. The subgroup $S_m\times S_n$ permutes the two blocks independently. A contraction $C_{i\bar j}$ joins the $i$th $V$ leg to the $j$th conjugate leg; these contractions and the subgroup generate the represented Brauer algebra $B_N(m,n)$.
--
--   The map $\Sigma$ transposes the conjugate tensor block. Given two matrices $Z_A,Z_B$, write
--   $$
--   f_X(Z_A,Z_B)=\operatorname{tr}_{m,n}\bigl(X(Z_A^{\otimes m}\otimes Z_B^{\otimes n})\bigr).
--   $$
--   The state inner product is the Gaussian expectation of $\overline{f_{X_2}}f_{X_1}$, using independent matrices with standard circular complex Gaussian entries. A branching system $Q^\gamma_{A,ij}$ consists of represented Brauer operators satisfying subgroup symmetry, the matrix-unit product (7.6), and $(Q^\gamma_{A,ij})^\dagger=Q^\gamma_{A,ji}$.
--
--   These definitions make the paper's diagrammatic operators and its quantum-mechanical inner product available to the individual theorem statements.
--
--   **Formalization Note** The Brauer algebra is its matrix image, $\Sigma$ is a concrete partial transpose, and the vacuum inner product is the Bargmann–Fock Gaussian realization. Irrep and multiplicity labels are abstract types with natural-number indices restricted by $i,j<M^\gamma_A$. The adjoint relation follows from (7.3) and is included explicitly. No completeness or positivity axiom is imposed.
-- source:
--   Kimura & Ramgoolam, Branes, Anti-Branes and Brauer Algebras in Gauge-Gravity duality, arXiv:0709.2158v2, pp. 6–12 and 27–28, (3.1)–(3.9), Figure 6, (7.3)–(7.8)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
import Definitions.Def_BraneBrauer_Orthogonal_ComplexGaussian

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Kronecker

namespace BraneBrauer.Orthogonal

/-- Basis labels for `V^{⊗m} ⊗ V̄^{⊗n}` with `V = ℂ^N`. -/
abbrev Idx (N m n : ℕ) := (Fin m → Fin N) × (Fin n → Fin N)

/-- Operators on the mixed tensor power. -/
abbrev Op (N m n : ℕ) := Matrix (Idx N m n) (Idx N m n) ℂ

/-- Entrywise measurable structure on complex matrices. -/
instance matrixMeasurableSpace (a b : Type*) : MeasurableSpace (Matrix a b ℂ) :=
  (inferInstance : MeasurableSpace (a → b → ℂ))

/-- The `Sₘ × Sₙ` action by tensor-factor permutations. -/
def permOp (N m n : ℕ) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Op N m n :=
  QAlgorithms.Schur.tensorPermutation N m σ ⊗ₖ
    QAlgorithms.Schur.tensorPermutation N n τ

/-- `C_{i j̄}`: contraction of primal leg `i` with dual leg `j`. -/
def contraction (N m n : ℕ) (i : Fin m) (j : Fin n) : Op N m n :=
  Matrix.of fun ⟨x, y⟩ ⟨x', y'⟩ =>
    if x i = y j ∧ x' i = y' j ∧
        (∀ k, k ≠ i → x k = x' k) ∧
        (∀ l, l ≠ j → y l = y' l) then 1 else 0

/-- The image of the walled Brauer algebra in the mixed tensor space. -/
def brauerAlgebra (N m n : ℕ) : Subalgebra ℂ (Op N m n) :=
  Algebra.adjoin ℂ
    ({X | ∃ (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)),
      X = permOp N m n σ τ} ∪
     {X | ∃ (i : Fin m) (j : Fin n), X = contraction N m n i j})

/-- `Σ`, reflection of the dual legs, as partial transpose. -/
def sigma {N m n : ℕ} (X : Op N m n) : Op N m n :=
  Matrix.of fun ⟨x, y⟩ ⟨x', y'⟩ => X (x, y') (x', y)

/-- The tensor of `m` copies of `Z_A` and `n` copies of `Z_B`. -/
def tensorPow (N m n : ℕ) (ZA ZB : Matrix (Fin N) (Fin N) ℂ) : Op N m n :=
  Matrix.of fun ⟨x, y⟩ ⟨x', y'⟩ =>
    (∏ k : Fin m, ZA (x k) (x' k)) *
      (∏ l : Fin n, ZB (y l) (y' l))

/-- The polynomial state associated with `X`. -/
def statePoly {N m n : ℕ} (X : Op N m n)
    (Z : Fin 2 → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  (X * tensorPow N m n (Z 0) (Z 1)).trace

/-- Two independent standard complex Gaussian matrices. -/
def matrixGaussian (N : ℕ) :
    Measure (Fin 2 → Matrix (Fin N) (Fin N) ℂ) :=
  Measure.pi (fun _ : Fin 2 =>
    Measure.pi (fun _ : Fin N =>
      Measure.pi (fun _ : Fin N => complexGaussian)))

/-- Bargmann–Fock inner product of polynomial states. -/
def innerProd (N m n : ℕ) (X₂ X₁ : Op N m n) : ℂ :=
  ∫ Z, star (statePoly X₂ Z) * statePoly X₁ Z ∂matrixGaussian N

/-- The matrix-unit, symmetry, membership, and adjoint properties of the
operators `Q^γ_{A,ij}` defined by (7.3). -/
structure IsBranchingSystem (N m n : ℕ) {Γ Λ : Type*}
    [DecidableEq Γ] [DecidableEq Λ]
    (M : Γ → Λ → ℕ) (Q : Γ → Λ → ℕ → ℕ → Op N m n) : Prop where
  mem : ∀ γ A i j, i < M γ A → j < M γ A →
    Q γ A i j ∈ brauerAlgebra N m n
  symm : ∀ γ A i j σ τ, i < M γ A → j < M γ A →
    permOp N m n σ τ * Q γ A i j * permOp N m n σ⁻¹ τ⁻¹ = Q γ A i j
  mul : ∀ γ₁ A i j γ₂ B k l,
    i < M γ₁ A → j < M γ₁ A → k < M γ₂ B → l < M γ₂ B →
    Q γ₁ A i j * Q γ₂ B k l =
      if γ₁ = γ₂ ∧ A = B ∧ j = k then Q γ₁ A i l else 0
  adj : ∀ γ A i j, i < M γ A → j < M γ A →
    (Q γ A i j)ᴴ = Q γ A j i

end BraneBrauer.Orthogonal


