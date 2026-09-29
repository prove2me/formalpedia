-- Prove2me | Definitions.Def_HopfAlgebra_TorsorGrading
-- name    : HopfAlgebra_TorsorGrading
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/019fec29-287c-58ed-a67f-12c7a35c46ed
-- title:
--   Gradings of a bialgebra by a map to a group algebra
-- statement:
--   Fix an additive commutative group $\Lambda$ with decidable equality, a commutative ring $R$, a commutative ring $H$ carrying an $R$-bialgebra structure, and a bialgebra homomorphism $\pi \colon H \to R[\Lambda]$ into the group algebra of $\Lambda$ (written multiplicatively via `Multiplicative Λ`); dually, $\pi$ corresponds to a homomorphism from the diagonalisable group of characters $\Lambda$ to the group scheme attached to $H$. From this datum the module builds the associated $\Lambda$-grading.
--
--   `gradingCoaction` is the $R$-linear map $H \to R[\Lambda] \otimes_R H$ given by the comultiplication of $H$ followed by $\pi \otimes \mathrm{id}_H$. `gradingComponents` rewrites the target: the coefficient isomorphism $R[\Lambda] \cong (\Lambda \to_0 R)$ on the left tensor factor, followed by Mathlib's identification $(\Lambda \to_0 R) \otimes_R H \cong (\Lambda \to_0 H)$, turns the coaction into an $R$-linear map $H \to (\Lambda \to_0 H)$, the finitely supported family of homogeneous components of an element. `componentProj j` is the $j$-th component of this family, an $R$-linear endomorphism of $H$. `gradedPiece j` is the $R$-submodule of those $t \in H$ whose component family is the single function supported at $j$ with value $t$; equivalently the coaction sends $t$ to $[j] \otimes t$, so these are the elements of degree $j$. The submodule structure records closure under addition, zero and scalar multiplication.
--
--   `blockComponents` is the same composite written out in one step, and `blockComponents_eq` records that it agrees with `gradingComponents`. For an element $\varepsilon \in H$ (in applications an idempotent) and $j \in \Lambda$, `blockPiece ε j` is the $R$-submodule of $t \in H$ that are of degree $j$ and satisfy $t\varepsilon = t$; `mem_blockPiece_iff` restates this as membership in `gradedPiece Λ π j` together with $t\varepsilon = t$. The remaining declarations are unfolding lemmas for the definitions above. No decomposition of $H$ as a direct sum of the graded pieces is asserted here.
--
--   **Relation to Mathlib.** Built entirely from Mathlib's bialgebra and group-algebra API (`Bialgebra`, `Coalgebra.comul`, `BialgHom`, `MonoidAlgebra.coeffLinearEquiv`, `TensorProduct.finsuppScalarLeft`). Mathlib's graded-algebra notions are phrased as direct-sum decompositions indexed by a grading; the grading induced by a bialgebra map to a group algebra, its component projections and the block pieces cut out by an idempotent are the project's own definitions.
--
--   **Where it is used.** This vocabulary serves the statements about torsors under group schemes of multiplicative type in the $R = T$ part of the argument, where a homomorphism to a diagonalisable group splits a bialgebra into weight spaces and, after cutting by an idempotent, into block pieces from which units and Kummer-type generators are extracted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HopfAlgebra_TorsorGrading.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HopfAlgebra.TorsorGrading

open TensorProduct

section Grading

variable (Λ : Type) [AddCommGroup Λ] [DecidableEq Λ]
variable {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H]
variable (π : H →ₐc[R] MonoidAlgebra R (Multiplicative Λ))

def gradingCoaction : H →ₗ[R] MonoidAlgebra R (Multiplicative Λ) ⊗[R] H :=
  (LinearMap.rTensor H π.toLinearMap) ∘ₗ Coalgebra.comul

def gradingComponents : H →ₗ[R] (Multiplicative Λ →₀ H) :=
  (TensorProduct.finsuppScalarLeft R H (Multiplicative Λ)).toLinearMap ∘ₗ
    ((MonoidAlgebra.coeffLinearEquiv R).rTensor H).toLinearMap ∘ₗ gradingCoaction Λ π

def componentProj (j : Λ) : H →ₗ[R] H :=
  (Finsupp.lapply (Multiplicative.ofAdd j)) ∘ₗ gradingComponents Λ π

def gradedPiece (j : Λ) : Submodule R H where
  carrier := {t : H | gradingComponents Λ π t = Finsupp.single (Multiplicative.ofAdd j) t}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, ha, hb, ← Finsupp.single_add]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero, Finsupp.single_zero]
  smul_mem' := fun c a ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_smul, ha, Finsupp.smul_single]

omit [DecidableEq Λ] in
theorem gradingCoaction_apply (t : H) :
    gradingCoaction Λ π t = (LinearMap.rTensor H π.toLinearMap) ((Coalgebra.comul (R := R)) t) := rfl

theorem gradingComponents_apply (t : H) :
    gradingComponents Λ π t =
      (TensorProduct.finsuppScalarLeft R H (Multiplicative Λ))
        (((MonoidAlgebra.coeffLinearEquiv R).rTensor H) (gradingCoaction Λ π t)) := rfl

theorem componentProj_apply (j : Λ) (t : H) :
    componentProj Λ π j t = gradingComponents Λ π t (Multiplicative.ofAdd j) := rfl

theorem mem_gradedPiece_iff (j : Λ) (t : H) :
    t ∈ gradedPiece Λ π j ↔ gradingComponents Λ π t = Finsupp.single (Multiplicative.ofAdd j) t := Iff.rfl

def blockComponents : H →ₗ[R] (Multiplicative Λ →₀ H) :=
  (TensorProduct.finsuppScalarLeft R H (Multiplicative Λ)).toLinearMap ∘ₗ
    ((MonoidAlgebra.coeffLinearEquiv R).rTensor H).toLinearMap ∘ₗ
    (LinearMap.rTensor H π.toLinearMap) ∘ₗ Coalgebra.comul

def blockPiece (ε : H) (j : Λ) : Submodule R H where
  carrier := {t : H | blockComponents Λ π t = Finsupp.single (Multiplicative.ofAdd j) t ∧ t * ε = t}
  add_mem' := fun {x y} hx hy => by
    obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, by rw [add_mul, hx2, hy2]⟩
    rw [map_add, hx1, hy1, ← Finsupp.single_add]
  zero_mem' := by
    refine ⟨?_, by rw [zero_mul]⟩
    rw [map_zero, Finsupp.single_zero]
  smul_mem' := fun c x hx => by
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨?_, by rw [smul_mul_assoc, hx2]⟩
    rw [map_smul, hx1, Finsupp.smul_single]

theorem blockComponents_eq : blockComponents Λ π = gradingComponents Λ π := rfl

theorem mem_blockPiece_iff (ε : H) (j : Λ) (t : H) :
    t ∈ blockPiece Λ π ε j ↔ t ∈ gradedPiece Λ π j ∧ t * ε = t := Iff.rfl

end Grading

end HopfAlgebra.TorsorGrading

end


