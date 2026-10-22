-- Prove2me | Definitions.Def_EquivPosMaps_TwoPositive_Basic
-- name    : EquivPosMaps_TwoPositive_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:00.586064+00:00
-- url     : https://prove2.me/theorems/b66a1572-0bf3-4bc7-a52c-fc3699fb6ad8
-- title:
--   Definitions 1.1–1.3 and 1.5: map positivity, Choi and Bell matrices, and the family
-- statement:
--   The paper studies complex-linear maps between finite-dimensional matrix algebras. For such a map $\Psi$, positivity means that $X\geq0$ implies $\Psi(X)\geq0$. Its $k$-positivity means positivity of $\mathrm{id}_k\otimes\Psi$ on **all** positive semidefinite inputs. Copositivity and complete copositivity use composition with transposition on the source. Complete positivity uses the published all-$k$ predicate.
--
--   The Choi matrix and the paper's family are
--
--   $$
--   C_\Psi=\sum_{i,j}e_{ij}\otimes\Psi(e_{ij}),\qquad
--   \Phi_{\alpha,\beta,n}(A)=A^{\mathsf T}\otimes I_n+I_n\otimes A+\operatorname{Tr}(A)(\alpha I_{n^2}+\beta B_nB_n^*),
--   $$
--
--   where $B_n=\sum_i e_i\otimes e_i$ is unnormalized. The module also defines the first $k$ by $k$ block of $C_\Psi$, the two square-root boundary curves, and $S_\beta$ as the least real root of the cubic in Theorem 3.8. These are shared objects used by every mission statement.
--
--   **Formalization Note** Matrix indices are zero-based `Fin` values, the auxiliary tensor index is first, and the transpose in $\Phi$ acts on the first output factor. The root is a real `sInf` of a nonempty finite root set.
-- source:
--   Collins, Osaka & Sapra, On a family of a linear maps from Mn(C) to Mn2(C), arXiv:1802.07553v1, pp. 2–3, 4, 6, 8, 10, Definitions 1.1–1.3, 1.5 and displayed formulas

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
open scoped Matrix Kronecker ComplexOrder
noncomputable section

namespace EquivPosMaps.TwoPositive

/-- Definition 1.1, p. 2: positivity on every positive semidefinite input. -/
def IsPositiveMap {I J : Type*} [Fintype I] [Fintype J]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Prop :=
  ∀ X : Matrix I I ℂ, X.PosSemidef → (Φ X).PosSemidef

/-- Definition 1.1, p. 2: positivity of the identity ancilla tensored with the map. -/
def KPositive {I J : Type*} [Fintype I] [Fintype J] (k : ℕ)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Prop :=
  ∀ X : Matrix (Fin k × I) (Fin k × I) ℂ, X.PosSemidef →
    (QAlgorithms.idTensorSuperop Φ X).PosSemidef

/-- Notation 1.1, p. 2: transposition on the source algebra. -/
def transposeMap (I : Type*) [Fintype I] :
    Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ where
  toFun := Matrix.transpose
  map_add' := by intro A B; rfl
  map_smul' := by intro c A; rfl

/-- Definition 1.1, p. 2: positivity after transposition. -/
def IsCopositive {I J : Type*} [Fintype I] [Fintype J]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Prop :=
  IsPositiveMap (Φ.comp (transposeMap I))

/-- Definition 1.1, p. 2: k-positivity after transposition. -/
def KCopositive {I J : Type*} [Fintype I] [Fintype J] (k : ℕ)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Prop :=
  KPositive k (Φ.comp (transposeMap I))

/-- Definition 1.2, p. 2: complete copositivity. -/
def IsCompletelyCopositive {I J : Type*} [Fintype I] [Fintype J]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Prop :=
  QAlgorithms.Entanglement.IsCompletelyPositive (Φ.comp (transposeMap I))

example {I J : Type*} [Fintype I] [Fintype J]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) :
    QAlgorithms.Entanglement.IsCompletelyPositive Φ ↔ ∀ k, KPositive k Φ := Iff.rfl

/-- Definition 1.3, p. 2: the Choi matrix has entry Φ(eᵢⱼ) at ((i,a),(j,b)). -/
def choiMatrix {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Matrix (I × J) (I × J) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- Notation 1.1, p. 2: the unnormalized Bell projector BₙBₙᴴ. -/
def bellProj (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  Matrix.of fun p q => if p.1 = p.2 ∧ q.1 = q.2 then 1 else 0

/-- Definition 1.5, p. 3. The first Kronecker factor is transposed. -/
def phi (n : ℕ) (α β : ℝ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ where
  toFun A := A.transpose ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) +
    (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ A +
    A.trace • ((α : ℂ) • (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) +
      (β : ℂ) • bellProj n)
  map_add' := by
    intro A B
    ext p q
    simp [Matrix.trace_add, add_mul, mul_add]
    ring
  map_smul' := by
    intro c A
    ext p q
    simp [Matrix.trace_smul, mul_assoc]
    ring

/-- Proposition 2.2, p. 4: the first k by k block of the Choi matrix. -/
def blockMatrix {d₁ d₂ : ℕ} (k : ℕ) (hk : k ≤ d₁)
    (Φ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ) :
    Matrix (Fin k × Fin d₂) (Fin k × Fin d₂) ℂ :=
  Matrix.of fun p q =>
    Φ (Matrix.single (Fin.castLE hk p.1) (Fin.castLE hk q.1) 1) p.2 q.2

/-- Proposition 3.1, p. 6: the lower positivity boundary. -/
def lowP (n : ℕ) (β : ℝ) : ℝ :=
  (-(2 + (n : ℝ) * β) + Real.sqrt ((n : ℝ)^2 * β^2 - 4 * ((n : ℝ) - 2) * β + 4)) / 2

/-- Proposition 3.3, p. 8: the lower complete positivity boundary at n = 3. -/
def lowCP (β : ℝ) : ℝ :=
  (-(3 + 3 * β) + Real.sqrt (9 * β^2 - 10 * β + 17)) / 2

/-- Theorem 3.8, p. 10: the least real root of the displayed cubic. -/
def smallestRoot (β : ℝ) : ℝ :=
  sInf {x : ℝ | x^3 + (-2 - 3*β)*x^2 + (-2 + 4*β)*x + 2*β = 0}

end EquivPosMaps.TwoPositive


