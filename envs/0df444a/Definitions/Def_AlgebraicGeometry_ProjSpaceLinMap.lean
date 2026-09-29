-- Prove2me | Definitions.Def_AlgebraicGeometry_ProjSpaceLinMap
-- name    : AlgebraicGeometry_ProjSpaceLinMap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/51870fde-a7f1-5755-883d-19adcf7bf3bd
-- title:
--   Linear substitutions and the induced maps of projective space
-- statement:
--   Fix a commutative ring $R$ and $n \in \mathbb{N}$, and write $\mathcal{A}$ for the standard grading `MvPolynomial.homogeneousSubmodule (Fin (n+1)) R` of $R[x_0,\dots,x_n]$, so that `Proj 𝒜` is $\mathbb{P}^n_R$. For a square matrix $M$ indexed by `Fin (n+1)`, `linForm R n M i` is the linear form $\sum_j M_{ij} x_j$; it is identified with the $i$-th entry of the matrix–vector product $(M \mapsto C) \cdot (x_0,\dots,x_n)$ by `linForm_eq_mulVec`, and it is homogeneous of degree $1$, hence a member of $\mathcal{A}_1$ (`isHomogeneous_linForm`, `linForm_mem`). The substitution $x_i \mapsto \mathrm{linForm}\,M\,i$ is then packaged as `linSubst R n M`, a graded ring homomorphism $\mathcal{A} \to \mathcal{A}$ (notation `→+*ᵍ`) whose underlying ring map is the $R$-algebra evaluation `MvPolynomial.aeval` at these linear forms; gradedness is the statement that a polynomial in $\mathcal{A}_i$ is carried to $\mathcal{A}_i$, since substituting degree-one forms preserves degree. The computation rules `linSubst_apply`, `linSubst_X`, `linSubst_C` record its values, and `linSubst_linForm` gives the composition law in the form $\mathrm{linSubst}\,M\,(\mathrm{linForm}\,M'\,i) = \mathrm{linForm}\,(M'M)\,i$, with the product taken in that order.
--
--   `irrelevant_le_map_linSubst` asserts that if $M$ is a unit (in the matrix ring), then the irrelevant homogeneous ideal of $\mathcal{A}$ is contained in the `HomogeneousIdeal.map` of the irrelevant ideal along `linSubst R n M`; the proof uses a left inverse $M'$ of $M$ to exhibit each $x_j$ as the image of $\mathrm{linForm}\,M'\,j$, together with the containment of the irrelevant ideal in the ideal spanned by the variables. This is exactly the hypothesis required by Mathlib's `Proj.map`, and `linMap R n M hM` is defined to be that morphism $\mathbb{P}^n_R \to \mathbb{P}^n_R$, with `linMap_eq` recording the definition.
--
--   **Relation to Mathlib.** Mathlib supplies the grading `MvPolynomial.homogeneousSubmodule`, graded ring homomorphisms and the functoriality `Proj.map` of the `Proj` construction under a containment condition on irrelevant ideals; the linear substitutions and the resulting morphisms of $\mathbb{P}^n_R$ are the project's own.
--
--   **Where it is used.** These morphisms supply the action of invertible $(n+1) \times (n+1)$ matrices on projective space used elsewhere in the tree: a change of frame of the sections presenting a morphism to $\mathbb{P}^n_R$ changes that morphism by composition with `linMap`, which is how matrix actions on frames of polarised abelian schemes are expressed without altering the underlying scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ProjSpaceLinMap.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

section LinMap

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

def linForm (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) R :=
  ∑ j, C (M i j) * X j

theorem linForm_eq_mulVec (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    linForm R n M = Matrix.mulVec (M.map C) X := rfl

theorem isHomogeneous_linForm (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) :
    (linForm R n M i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (M i j) j

theorem linForm_mem (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) : linForm R n M i ∈ 𝒜 1 :=
  (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_linForm R n M i)

def linSubst (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : 𝒜 →+*ᵍ 𝒜 where
  __ := (MvPolynomial.aeval (linForm R n M)).toRingHom
  map_mem {i} {p} hp := by
    rw [mem_homogeneousSubmodule] at hp
    have h := hp.aeval (linForm R n M) (isHomogeneous_linForm R n M)
    rw [one_mul] at h
    exact (mem_homogeneousSubmodule i _).mpr h

theorem linSubst_apply (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (p : MvPolynomial (Fin (n + 1)) R) :
    linSubst R n M p = MvPolynomial.aeval (linForm R n M) p := rfl

@[simp] theorem linSubst_X (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) :
    linSubst R n M (X i) = linForm R n M i :=
  MvPolynomial.aeval_X _ i

@[simp] theorem linSubst_C (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (r : R) :
    linSubst R n M (C r) = C r :=
  MvPolynomial.aeval_C _ r

theorem linSubst_linForm (M M' : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) :
    linSubst R n M (linForm R n M' i) = linForm R n (M' * M) i := by
  simp only [linForm, map_sum, map_mul, linSubst_C, linSubst_X, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (mul_assoc _ _ _).symm

theorem irrelevant_le_map_linSubst (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hM : IsUnit M) :
    HomogeneousIdeal.irrelevant 𝒜 ≤ HomogeneousIdeal.map (linSubst R n M) (HomogeneousIdeal.irrelevant 𝒜) := by
  obtain ⟨M', hM'⟩ := hM.exists_left_inv
  intro a ha
  show a ∈ (HomogeneousIdeal.map (linSubst R n M) (HomogeneousIdeal.irrelevant _)).toIdeal
  rw [HomogeneousIdeal.toIdeal_map]
  refine (Ideal.span_le.mpr ?_) (irrelevant_le_span_X R n ha)
  rintro _ ⟨j, rfl⟩
  have hX : (X j : MvPolynomial (Fin (n + 1)) R) = (linSubst R n M).toRingHom (linForm R n M' j) := by
    change X j = linSubst R n M (linForm R n M' j)
    rw [linSubst_linForm, hM', linForm]
    simp only [Matrix.one_apply]
    rw [Fintype.sum_eq_single j (fun k hk => by rw [if_neg (Ne.symm hk), C_0, zero_mul])]
    rw [if_pos rfl, C_1, one_mul]
  rw [hX]
  exact Ideal.mem_map_of_mem _ ((HomogeneousIdeal.mem_irrelevant_iff _ _).mpr (by
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne _ (linForm_mem R n M' j) one_ne_zero]))

def linMap (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hM : IsUnit M) :
    Proj 𝒜 ⟶ Proj 𝒜 :=
  Proj.map (linSubst R n M) (irrelevant_le_map_linSubst R n M hM)

theorem linMap_eq (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hM : IsUnit M) :
    linMap R n M hM = Proj.map (linSubst R n M) (irrelevant_le_map_linSubst R n M hM) := rfl

end LinMap

end ProjSpace

end AlgebraicGeometry

end


