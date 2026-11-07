-- Prove2me | Definitions.Def_QSDMixing_GU_hecke
-- name    : QSDMixing_GU_hecke
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:51:51.447746+00:00
-- url     : https://prove2.me/theorems/575c00a5-87db-40d2-8261-857c36edc40f
-- title:
--   The Hecke algebra $\mathcal A=\mathrm{End}_G(\mathbb C[G/H])$
-- statement:
--   The Hecke algebra is the unital $*$-subalgebra of $n\times n$ matrices on $G/H$ given by
--
--   $$
--   \mathcal A=\mathrm{End}_G(\mathbb C[G/H])=\{T:\ T_{gx,gy}=T_{x,y}\ \ \forall g\in G,\ x,y\in G/H\},
--   $$
--
--   where $G$ acts on $G/H$ by left multiplication. Equivalently, it is the span of the indicators of the $G$-orbits of pairs of cosets.
--
--   The Gram matrix lies in $\mathcal A$, so the Hadamard channel $\Phi_X$ preserves it.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (69), p.17

import Mathlib
import Definitions.Def_QSDMixing_GU_cosetFintype

set_option autoImplicit false

namespace QSDMixing.GU

/-- The Hecke algebra `A = End_G(ℂ[G/H])` as the `*`-subalgebra of `G`-invariant matrices on `G ⧸ H`:
`T_{gx, gy} = T_{x, y}` for all `g`, `x`, `y`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (69), p.17: "`T ∈ End_G(ℂ[G/H]) ⇔ T_{gxH,gyH} = T_{xH,yH} ∀ g, x, y ∈ G`".

**Formalization Note.** `g • x` is Mathlib's left action of `G` on `G ⧸ H`. -/
noncomputable def hecke {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    StarSubalgebra ℂ (Matrix (G ⧸ H) (G ⧸ H) ℂ) where
  carrier := {T | ∀ (g : G) (x y : G ⧸ H), T (g • x) (g • y) = T x y}
  mul_mem' := by
    intro S T hS hT g x y
    simp only [Matrix.mul_apply]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ ?_ |>.symm
    intro z
    exact (by rw [MulAction.toPerm_apply, hS g x z, hT g z y])
  add_mem' := by
    intro S T hS hT g x y
    simp only [Matrix.add_apply, hS g x y, hT g x y]
  algebraMap_mem' := by
    intro c g x y
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply, smul_left_cancel_iff]
  star_mem' := by
    intro T hT g x y
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, hT g y x]

end QSDMixing.GU


