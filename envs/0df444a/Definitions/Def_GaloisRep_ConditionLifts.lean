-- Prove2me | Definitions.Def_GaloisRep_ConditionLifts
-- name    : GaloisRep_ConditionLifts
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/8b1587fe-f083-5955-9524-575b1dc98b70
-- title:
--   Condition subfunctor of the framed lift functor
-- statement:
--   Fix a local ring $\mathcal{O}$ and a family of predicates $\mathcal{D}$ which, for every local ring $A$ carrying an $\mathcal{O}$-algebra structure, singles out certain elements of [`GaloisRepAdic A`](../def/GaloisRep_Adic.html#L16) — the structures consisting of a free finite $A$-module $V$ of rank $2$, a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ to $\operatorname{End}_A(V)$, and the adic continuity condition that for each $n$ there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every $\sigma$ fixing $L$ pointwise acts trivially on $V/\mathfrak{m}_A^n V$. Given in addition a point $\rho_0$ of the representation functor at the residue field, i.e. a continuous homomorphism $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(k)$, and an object $A$ of the category of local pro-Artinian $\mathcal{O}$-algebras, [`GaloisRep.conditionLifts`](../def/GaloisRep_ConditionLifts.html#L9) is the set of continuous homomorphisms $\rho' : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(A)$ such that: $\rho'$ belongs to `liftFunctor` at $A$, that is, the push-forward of $\rho'$ along the unique (terminal) morphism $A \to k$ is exactly $\rho_0$; and, for every morphism $f : A \to B$ in the category with $B$ Artinian, every $\rho_B \in$ [`GaloisRepAdic B`](../def/GaloisRep_Adic.html#L16) and every basis $b$ of the underlying module of $\rho_B$ indexed by $\mathrm{Fin}\,2$ whose associated matrices $\mathrm{toMatrix}\,b\,b\,(\rho_B(\sigma))$ agree for all $\sigma$ with the matrices of the push-forward of $\rho'$ along $f$, one has $\mathcal{D}(\rho_B)$. Thus the condition is imposed not on $\rho'$ directly but on every module-theoretic realisation, in a basis, of each Artinian push-forward of $\rho'$.
--
--   [`GaloisRep.conditionSubfunctor`](../def/GaloisRep_ConditionLifts.html#L22) assembles these sets into a subfunctor of the representation functor: stability under a morphism $g : A \to A'$ holds because the lift subfunctor is one, and because a test morphism $f$ out of $A'$ pulls back to $g$ followed by $f$ out of $A$. A simp lemma records that the object part of this subfunctor is the set just described.
--
--   **Relation to Mathlib.** Mathlib supplies `CategoryTheory.Subfunctor` and the linear-algebra and topological infrastructure; the category of local pro-Artinian $\mathcal{O}$-algebras, the functor of continuous rank-two representations, its lift subfunctor and the rank-two adic Galois representation structure used here are the project's own notions, and so is the mechanism of cutting out a subfunctor by a condition on Artinian push-forwards.
--
--   **Where it is used.** Subfunctors of this shape are the input to representability criteria for deformation problems with local conditions: once such a subfunctor is shown to be stable under conjugation, reflected by injections and compatible with limits, one obtains a universal deformation ring of type $\mathcal{D}$, which is the object compared with a Hecke algebra in the Taylor–Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_ConditionLifts.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_Deformations_TraceAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace GaloisRep

open Deformation CategoryTheory IsLocalRing

def conditionLifts (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      ProartinianCat.residueField)
    (A : ProartinianCat 𝒪) :
    Set ((repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj A) :=
  {ρ' | ρ' ∈ (liftFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 ρ₀).obj A ∧
    ∀ (B : ProartinianCat 𝒪) [IsArtinianRing B] (f : A ⟶ B) (ρB : GaloisRepAdic B)
      (b : Module.Basis (Fin 2) B ρB.V),
      (∀ σ, LinearMap.toMatrix b b (ρB.ρ σ) =
        ((mapRepn (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 f ρ' σ : GL (Fin 2) B) :
          Matrix (Fin 2) (Fin 2) B)) → 𝒟 ρB}

def conditionSubfunctor (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      ProartinianCat.residueField) :
    Subfunctor (repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪) where
  obj A := conditionLifts 𝒪 𝒟 ρ₀ A
  map {A A'} g := by
    rintro ρ' ⟨hlift, hD⟩
    refine ⟨(liftFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 ρ₀).map g hlift, ?_⟩
    intro B _ f ρB b hb
    refine hD B (g ≫ f) ρB b (fun σ => ?_)
    rw [hb σ]
    simp only [mapRepn, Functor.map_comp, types_comp_apply]

@[simp] lemma conditionSubfunctor_obj (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      ProartinianCat.residueField) (A : ProartinianCat 𝒪) :
    (conditionSubfunctor 𝒪 𝒟 ρ₀).obj A = conditionLifts 𝒪 𝒟 ρ₀ A := rfl

end GaloisRep


