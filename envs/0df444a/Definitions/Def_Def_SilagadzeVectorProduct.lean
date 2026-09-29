-- Prove2me | Definitions.Def_Def_SilagadzeVectorProduct
-- name    : Def_SilagadzeVectorProduct
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T20:03:33.074361+00:00
-- url     : https://prove2.me/theorems/12a19c4c-992b-4b6b-84b2-ea69edde0af6
-- title:
--   Vector products on inner product spaces, the ternary product $\{A,B,C\}$, and the octonionic product on $\mathbb R^7$
-- statement:
--   This file fixes the objects of Section 3 and eq. (17) of Silagadze's paper.
--
--   **Vector product.** Let $V$ be a real inner product space with inner product $A\cdot B = \langle A,B\rangle$ and norm $|A|$. A bilinear map $\times : V\times V\to V$ is called a *vector product* if, for all $A,B\in V$,
--
--   1. $(A\times B)\cdot A = 0$ and $(A\times B)\cdot B = 0$;
--   2. $A\times A = 0$;
--   3. $|A\times B| = |A|\,|B|$ whenever $A\cdot B = 0$.
--
--   These are exactly the "intuitively reasonable" requirements the paper imposes on a multi-dimensional vector product.
--
--   **Ternary product.** For a bilinear map $\times$ the paper's ternary product is
--
--   $$
--   \{A,B,C\} = A\times(B\times C) - B\,(A\cdot C) + C\,(A\cdot B),
--   $$
--
--   which vanishes identically exactly when the familiar identity $A\times(B\times C) = B(A\cdot C) - C(A\cdot B)$ (eq. (9)) holds.
--
--   **The seven-dimensional product (eq. (17)).** On $\mathbb R^7$ with orthonormal basis $e_1,\dots,e_7$ put $e_i\times e_j = \sum_k f_{ijk}\,e_k$, where $f_{ijk}$ is completely antisymmetric and its only nonzero independent components are
--
--   $$
--   f_{123}=f_{246}=f_{435}=f_{651}=f_{572}=f_{714}=f_{367}=1 .
--   $$
--
--   Extended bilinearly, $A\times B = \sum_{i,j,k} f_{ijk}A_iB_j\,e_k$.
--
--   These definitions are the common vocabulary of every theorem in the mission: the goal theorem constrains the dimension of any space carrying a vector product, and the octonionic product shows the constraint is attained in dimension $7$.
--
--   **Formalization Note.** `IsVectorProduct cross` is a `Prop`-valued structure on a bundled bilinear map `cross : V →ₗ[ℝ] V →ₗ[ℝ] V` (bilinearity is built into the type). `ternary cross A B C` is the ternary product. The paper's indices $1,\dots,7$ are shifted to `Fin 7` $=\{0,\dots,6\}$: `fanoTriples` lists the seven triples $(0,1,2),(1,3,5),(3,2,4),(5,4,0),(4,6,1),(6,0,3),(2,5,6)$; `structureConst i j k` is $1$ on cyclic rotations of a listed triple, $-1$ on rotations of a triple with its first two entries swapped, and $0$ otherwise; `octonionCross` is the resulting bilinear map on `EuclideanSpace ℝ (Fin 7)`.
-- source:
--   Z. K. Silagadze, Feynman's derivation of Maxwell equations and extra dimensions, arXiv:hep-ph/0106235v2 (29 Jan 2002), https://arxiv.org/abs/hep-ph/0106235, Section 3 (pp. 4-6) and Section 4, eq. (17) (p. 9)

import Mathlib

open scoped InnerProductSpace

namespace SilagadzeVectorProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A vector product on a real inner product space `V` in the sense of Silagadze
(hep-ph/0106235, §3): a bilinear map `cross` such that `A × B` is orthogonal to both
`A` and `B`, `A × A = 0`, and `|A × B| = |A| |B|` whenever `A` and `B` are orthogonal. -/
structure IsVectorProduct (cross : V →ₗ[ℝ] V →ₗ[ℝ] V) : Prop where
  inner_cross_left : ∀ A B : V, ⟪cross A B, A⟫_ℝ = 0
  inner_cross_right : ∀ A B : V, ⟪cross A B, B⟫_ℝ = 0
  cross_self : ∀ A : V, cross A A = 0
  norm_cross_of_inner_eq_zero : ∀ A B : V, ⟪A, B⟫_ℝ = 0 → ‖cross A B‖ = ‖A‖ * ‖B‖

/-- Silagadze's ternary product
`{A, B, C} = A × (B × C) - B (A · C) + C (A · B)`. -/
def ternary (cross : V →ₗ[ℝ] V →ₗ[ℝ] V) (A B C : V) : V :=
  cross A (cross B C) - ⟪A, C⟫_ℝ • B + ⟪A, B⟫_ℝ • C

/-- The seven positively oriented index triples
`123, 246, 435, 651, 572, 714, 367` of Silagadze's eq. (17), shifted to `0`-based indices
(the paper's basis vector `e_m` is `EuclideanSpace.single (m - 1) 1`). -/
def fanoTriples : List (Fin 7 × Fin 7 × Fin 7) :=
  [(0, 1, 2), (1, 3, 5), (3, 2, 4), (5, 4, 0), (4, 6, 1), (6, 0, 3), (2, 5, 6)]

/-- The completely antisymmetric structure constants `f_{ijk}` of eq. (17):
`f_{ijk} = 1` if `(i, j, k)` is a cyclic rotation of one of `fanoTriples`,
`f_{ijk} = -1` if `(j, i, k)` is, and `f_{ijk} = 0` otherwise. -/
def structureConst (i j k : Fin 7) : ℝ :=
  if fanoTriples.any (fun t => t = (i, j, k) ∨ t = (j, k, i) ∨ t = (k, i, j)) then 1
  else if fanoTriples.any (fun t => t = (j, i, k) ∨ t = (i, k, j) ∨ t = (k, j, i)) then -1
  else 0

/-- The seven-dimensional vector product of eq. (17):
`A × B = ∑_{i,j,k} f_{ijk} A_i B_j e_k` on `ℝ⁷`. -/
noncomputable def octonionCross :
    EuclideanSpace ℝ (Fin 7) →ₗ[ℝ] EuclideanSpace ℝ (Fin 7) →ₗ[ℝ] EuclideanSpace ℝ (Fin 7) :=
  LinearMap.mk₂ ℝ
    (fun A B => ∑ k : Fin 7,
      (∑ i : Fin 7, ∑ j : Fin 7, structureConst i j k * A i * B j) •
        EuclideanSpace.single k (1 : ℝ))
    (by
      intro A₁ A₂ B
      simp only [PiLp.add_apply, add_mul, mul_add, Finset.sum_add_distrib, add_smul])
    (by
      intro c A B
      simp only [PiLp.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine congrArg (· • _) (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
      ring)
    (by
      intro A B₁ B₂
      simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib, add_smul])
    (by
      intro c A B
      simp only [PiLp.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine congrArg (· • _) (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
      ring)

end SilagadzeVectorProduct


