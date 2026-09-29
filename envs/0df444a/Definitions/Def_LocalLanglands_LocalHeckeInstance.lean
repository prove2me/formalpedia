-- Prove2me | Definitions.Def_LocalLanglands_LocalHeckeInstance
-- name    : LocalLanglands_LocalHeckeInstance
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/6262deda-8199-5005-91de-056c6a966be8
-- title:
--   Integral subgroup GL2​(R)≤GL2​(K) and transpose involution
-- statement:
--   Two ingredients for the local pair at a finite place are set up. First, for a commutative ring $R$, a field $K$ and an $R$-algebra structure on $K$, [`LocalGL2.integralSubgroup R K`](../def/LocalLanglands_LocalHeckeInstance.html#L13) is defined as the range of the group homomorphism $\mathrm{GL}_2(R)\to\mathrm{GL}_2(K)$ obtained by applying `algebraMap R K` entrywise, i.e. `Matrix.GeneralLinearGroup.map (algebraMap R K)`; thus an element $x\in\mathrm{GL}_2(K)$ lies in it exactly when $x$ is the image of some $y\in\mathrm{GL}_2(R)$, as recorded by `mem_integralSubgroup_iff`. In the intended application $R$ is a discrete valuation ring with fraction field $K$, so this is the subgroup $\mathrm{GL}_2(\mathcal O)$ of $\mathrm{GL}_2(K)$.
--
--   Second, for a commutative ring $A$, [`LocalGL2.transposeGL`](../def/LocalLanglands_LocalHeckeInstance.html#L27) sends a unit $x$ of the ring of $2\times 2$ matrices over $A$ to the unit whose underlying matrix is the transpose of that of $x$ and whose inverse is the transpose of the inverse of $x$; its underlying matrix is the transpose of that of $x$. The accompanying lemmas state that this operation is an anti-homomorphism, $(xy)^{\top}=y^{\top}x^{\top}$, that it is involutive, and that it fixes the identity. Over an $R$-algebra $K$ as above it commutes with entrywise application of `algebraMap R K`, and consequently carries `integralSubgroup R K` into itself. A final lemma gives the compatibility of determinants with entrywise application of `algebraMap R K` for $2\times2$ matrices: $\det(M^{\mathrm{alg}})=\mathrm{algebraMap}(\det M)$.
--
--   **Relation to Mathlib.** The subgroup is defined as the range of Mathlib's `Matrix.GeneralLinearGroup.map`, and `transposeGL` packages Mathlib's `Matrix.transpose` as an operation on the general linear group of $2\times2$ matrices; `det_map_algebraMap` is the $2\times2$ case of the compatibility of determinants with ring homomorphisms.
--
--   **Where it is used.** These are the data of the local pair $(\mathrm{GL}_2(K),\mathrm{GL}_2(R))$ used, together with the Cartan decomposition for $2\times2$ matrices over a discrete valuation ring and the convolution algebra of bi-invariant functions of `HeckePair`, to obtain commutativity of the local spherical Hecke algebra by means of the transpose anti-involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalLanglands_LocalHeckeInstance.lean

import Mathlib
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_LocalLanglands_CartanDecomposition

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix

noncomputable section

namespace LocalGL2

def integralSubgroup (R K : Type*) [CommRing R] [Field K] [Algebra R K] :
    Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range

theorem mem_integralSubgroup_iff {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    {x : GL (Fin 2) K} :
    x ∈ integralSubgroup R K ↔
      ∃ y : GL (Fin 2) R, Matrix.GeneralLinearGroup.map (algebraMap R K) y = x :=
  Iff.rfl

section Transpose

variable {A : Type*} [CommRing A]

def transposeGL (x : GL (Fin 2) A) : GL (Fin 2) A where
  val := x.valᵀ
  inv := x.invᵀ
  val_inv := by rw [← Matrix.transpose_mul, x.inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, x.val_inv, Matrix.transpose_one]

@[simp] theorem transposeGL_val (x : GL (Fin 2) A) :
    (transposeGL x : Matrix (Fin 2) (Fin 2) A) = (x : Matrix (Fin 2) (Fin 2) A)ᵀ := rfl

theorem transposeGL_mul (x y : GL (Fin 2) A) :
    transposeGL (x * y) = transposeGL y * transposeGL x := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeGL_val, transposeGL_val, transposeGL_val, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeGL_involutive (x : GL (Fin 2) A) : transposeGL (transposeGL x) = x := by
  refine Units.ext ?_
  rw [transposeGL_val, transposeGL_val, Matrix.transpose_transpose]

@[simp] theorem transposeGL_one : transposeGL (1 : GL (Fin 2) A) = 1 := by
  refine Units.ext ?_
  rw [transposeGL_val, Units.val_one, Matrix.transpose_one]

end Transpose

section IntegralPreservation

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

theorem transposeGL_map_algebraMap (y : GL (Fin 2) R) :
    transposeGL (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y)
      = Matrix.GeneralLinearGroup.map (algebraMap R K) (transposeGL y) := by
  refine Units.ext ?_
  show ((Matrix.GeneralLinearGroup.map (algebraMap R K) y :
      Matrix (Fin 2) (Fin 2) K))ᵀ = _
  ext i j
  simp [Matrix.transpose_apply]

theorem transposeGL_mem_integralSubgroup {x : GL (Fin 2) K} (hx : x ∈ integralSubgroup R K) :
    transposeGL x ∈ integralSubgroup R K := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨transposeGL y, (transposeGL_map_algebraMap y).symm⟩

theorem det_map_algebraMap (M : Matrix (Fin 2) (Fin 2) R) :
    (M.map (algebraMap R K)).det = algebraMap R K M.det := by
  simp [Matrix.det_fin_two]

end IntegralPreservation

end LocalGL2

end


