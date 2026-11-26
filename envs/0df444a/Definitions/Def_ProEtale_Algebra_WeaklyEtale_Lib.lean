-- Prove2me | Definitions.Def_ProEtale_Algebra_WeaklyEtale_Lib
-- name    : ProEtale_Algebra_WeaklyEtale_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:36:47.755394+00:00
-- url     : https://prove2.me/theorems/29dd0767-bd18-41c4-b00a-ed3cc9655ba1
-- title:
--   Weakly étale algebras are formally unramified; tensor products over a quotient ring and universe lifts
-- statement:
--   This file continues the published file on weakly étale algebras. Here an $R$-algebra $S$ is weakly étale if $S$ is flat over $R$ and the multiplication map $S \otimes_R S \to S$ is flat.
--
--   Principal results:
--   1. **Change of base ring along a surjection.** If $R \to S$ is surjective and $M$, $N$ are $S$-modules (with compatible $R$-structure), the natural map is an $S$-linear isomorphism
--   $$M \otimes_R N \cong M \otimes_S N, \qquad m \otimes n \mapsto m \otimes n.$$
--   There is an analogous algebra isomorphism $A \otimes_R B \cong A \otimes_S B$, linear over any further base $T$ acting on $A$. Simp lemmas describe both maps on pure tensors.
--   2. **Universe lifting.** $\mathrm{ULift}(M \otimes_R N) \cong \mathrm{ULift}(M) \otimes_{\mathrm{ULift}(R)} \mathrm{ULift}(N)$, with simp lemmas on pure tensors.
--   3. If the multiplication map $S \otimes_R S \to S$ is flat, then $S$ is formally unramified over $R$. Consequently every weakly étale algebra is formally unramified, and a weakly étale algebra of finite presentation is étale. The ring-hom version also holds: a weakly étale ring map is formally unramified.
--
--   These facts are used to relate weakly étale and étale algebras in the finitely presented case.
--
--   **Formalization Note** The main declarations are `TensorProduct.congrRing`, `Algebra.TensorProduct.congrRing`, `TensorProduct.uliftEquiv`, `Algebra.FormallyUnramified.of_flat_lmul'` and `RingHom.WeaklyEtale.formallyUnramified`, with low-priority instances `WeaklyEtale R S → FormallyUnramified R S` and `[WeaklyEtale R S] [FinitePresentation R S] → Etale R S`. `Algebra.WeaklyEtale` is Mathlib's class, and `RingHom.WeaklyEtale` is defined in the published file. The universe-lift equivalence allows four independent universe levels for the lifted objects.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/WeaklyEtale.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Algebra_WeaklyEtale of the same module.

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Maps
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Mathlib_RingTheory_TensorProduct_Maps
import Definitions.Def_ProEtale_Algebra_WeaklyEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Weakly étale algebras

-/

universe u u₁ u₂ u₃ u₄ u₅

open TensorProduct


def TensorProduct.congrRing
    {R S : Type*} (M N : Type*) [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module S M] [Module S N]
    [Algebra R S] [IsScalarTower R S M] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) :
    M ⊗[R] N ≃ₗ[S] M ⊗[S] N :=
  letI f : M ⊗[R] N →ₗ[S] M ⊗[S] N :=
    { __ := lift ((TensorProduct.mk S M N).restrictScalars₁₂ R R)
      map_smul' s x := by obtain ⟨r, rfl⟩ := h s; simp }
  letI b : M →ₗ[S] N →ₗ[S] M ⊗[R] N := --TensorProduct.mk R M N
    { toFun m :=
        { __ := TensorProduct.mk R M N m
          map_smul' s x := by obtain ⟨r, rfl⟩ := h s; simp }
      map_add' _ _ := by ext; simp
      map_smul' s x := by ext; obtain ⟨r, rfl⟩ := h s; simp }
  .ofLinear f (lift b) (by ext; rfl) (by ext; rfl)

@[simp]
lemma TensorProduct.congrRing_tmul
    {R S M N : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module S M] [Module S N]
    [Algebra R S] [IsScalarTower R S M] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) (m : M) (n : N) :
    TensorProduct.congrRing M N h (m ⊗ₜ[R] n) = m ⊗ₜ[S] n :=
  rfl

@[simp]
lemma TensorProduct.congrRing_symm_tmul
    {R S M N : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module S M] [Module S N]
    [Algebra R S] [IsScalarTower R S M] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) (m : M) (n : N) :
    (TensorProduct.congrRing M N h).symm (m ⊗ₜ[S] n) = m ⊗ₜ[R] n :=
  rfl

def Algebra.TensorProduct.congrRing
    {R S : Type*} (T A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
    [Algebra R S] [IsScalarTower R S A] [IsScalarTower R S B] [Algebra T A]
    (h : Function.Surjective (algebraMap R S)) :
    A ⊗[R] B ≃ₐ[T] A ⊗[S] B where
  __ := _root_.TensorProduct.congrRing A B h
  map_mul' := LinearMap.map_mul_of_map_mul_tmul (by simp)
  commutes' _ := rfl

@[simp]
lemma Algebra.TensorProduct.congrRing_tmul
    {R S : Type*} (T A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
    [Algebra R S] [IsScalarTower R S A] [IsScalarTower R S B] [Algebra T A]
    (h : Function.Surjective (algebraMap R S)) (a : A) (b : B) :
    Algebra.TensorProduct.congrRing T A B h (a ⊗ₜ b) = a ⊗ₜ b :=
  rfl

@[simp]
lemma Algebra.TensorProduct.congrRing_symm_tmul
    {R S : Type*} (T A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
    [Algebra R S] [IsScalarTower R S A] [IsScalarTower R S B] [Algebra T A]
    (h : Function.Surjective (algebraMap R S)) (a : A) (b : B) :
    (Algebra.TensorProduct.congrRing T A B h).symm (a ⊗ₜ b) = a ⊗ₜ b :=
  rfl

def TensorProduct.uliftEquiv
    (R M N : Type*) [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] :
    ULift.{u₁} (M ⊗[R] N) ≃ₗ[R] ULift.{u₂} M ⊗[ULift.{u₃} R] ULift.{u₄} N :=
  ULift.moduleEquiv ≪≫ₗ
    TensorProduct.congr ULift.moduleEquiv.symm ULift.moduleEquiv.symm ≪≫ₗ
    ((TensorProduct.congrRing (R := R) _ _ (by exact ULift.up_surjective)).restrictScalars R)

@[simp]
lemma TensorProduct.down_uliftEquiv_symm_tmul
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (m : ULift M) (n : ULift N) :
    ((TensorProduct.uliftEquiv R M N).symm (m ⊗ₜ n)).down = m.down ⊗ₜ n.down :=
  rfl

@[simp]
lemma TensorProduct.uliftEquiv_tmul
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (m : M) (n : N) :
    TensorProduct.uliftEquiv R M N ⟨m ⊗ₜ n⟩ = ⟨m⟩ ⊗ₜ ⟨n⟩ :=
  rfl

open CategoryTheory Limits

-- `(S ⊗[R] S) (T ⊗[R] A) S (T ⊗[S] A)`


namespace Algebra


variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]


lemma FormallyUnramified.of_flat_lmul' (h : (TensorProduct.lmul' (S := S) R).Flat) :
    FormallyUnramified R S := by
  have hp : (KaehlerDifferential.ideal R S).Pure :=
    flat_lmul'_iff_kaehlerDifferential_ideal_pure.mp h
  rw [formallyUnramified_iff]
  exact (Ideal.cotangent_subsingleton_iff _).mpr (Ideal.isIdempotentElem_of_pure _)

namespace WeaklyEtale

instance (priority := low) inst_AlgebraWeaklyEtale_L218 [WeaklyEtale R S] : FormallyUnramified R S :=
  .of_flat_lmul' (flat_lmul' R S)

instance (priority := low) inst_AlgebraWeaklyEtale_L221 [WeaklyEtale R S] [FinitePresentation R S] : Etale R S :=
  .of_formallyUnramified_of_flat

end WeaklyEtale

end Algebra

namespace RingHom


variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)


/-- A weakly étale ring map is formally unramified. -/
lemma WeaklyEtale.formallyUnramified {f : R →+* S} (hf : f.WeaklyEtale) :
    f.FormallyUnramified := by
  algebraize [f]
  have : Algebra.WeaklyEtale R S := hf
  exact (inferInstance : Algebra.FormallyUnramified R S)


end RingHom


