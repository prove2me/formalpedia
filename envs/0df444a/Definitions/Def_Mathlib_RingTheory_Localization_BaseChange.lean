-- Prove2me | Definitions.Def_Mathlib_RingTheory_Localization_BaseChange
-- name    : Mathlib_RingTheory_Localization_BaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/7b8476cd-cc69-52a7-8074-7352f1babd36
-- title:
--   Base change along a localization: tensor identifications and extensionality
-- statement:
--   Working over a commutative semiring $R$ with a submonoid $S$ and a localization $A$ of $R$ at $S$, this module supplies computational lemmas and two refinements of the canonical identifications for tensor products of modules over $A$. For an $A$-module $M_1$ that is also an $R$-module compatibly (an `IsScalarTower R A M₁` assumption), `moduleLid_symm_apply` records that the inverse of the identification of $A \otimes_R M_1$ with $M_1$ sends $m$ to $1 \otimes_R m$; for a second such module $M_2$, `map_moduleTensorEquiv_tmul` and `map_moduleTensorEquiv_symm_tmul` record that the identification $M_1 \otimes_A M_2 \cong M_1 \otimes_R M_2$ (an isomorphism because $A$ is a localization of $R$) and its inverse send $m_1 \otimes m_2$ to $m_1 \otimes m_2$ in either direction.
--
--   `tensorProduct_ext` is an extensionality principle in the following situation: $S$ is a submonoid of a commutative semiring $A$, $B$ an $A$-algebra, $K$ a localization of $A$ at $S$, and $L$ a $B$-algebra which is simultaneously an $A$- and $K$-algebra with compatible scalars and which, as a $B$-module via the structure map $B \to L$, is the localization of $B$ at (the image of) $S$. Then two $K$-linear maps $L \otimes_K M \to P$ between $K$-modules that agree on all elements $(\mathrm{algebraMap}\,x) \otimes_K y$ with $x \in B$, $y \in M$ are equal, since every element of $L$ becomes the image of an element of $B$ after multiplication by a unit coming from $S$.
--
--   `leftModuleTensorEquiv` upgrades the identification $M_1 \otimes_A M_2 \cong M_1 \otimes_R M_2$ to an $M'$-linear equivalence, where $M'$ is a semiring acting on the left factor $M_1$ so as to commute with the $R$- and $A$-actions; the $M'$-action on either tensor product is the one through $M_1$. Finally, `leftModuleTensorEquiv_restrictScalars_eq` states that, when $M'$ is commutative and fits into algebra maps $A \to M' \to R$ with the corresponding towers, restricting this equivalence to $A$-linear maps returns the underlying identification of $A$-modules.
--
--   **Relation to Mathlib.** These are additions to the setting of Mathlib's `IsLocalization` base-change file: the simp lemmas compute Mathlib's `IsLocalization.moduleLid` and `IsLocalization.moduleTensorEquiv` on pure tensors, and [`IsLocalization.leftModuleTensorEquiv`](../def/Mathlib_RingTheory_Localization_BaseChange.html#L52) is the latter equivalence promoted to linearity over a semiring acting on the left tensor factor.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/RingTheory/Localization/BaseChange.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_Localization_BaseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

namespace IsLocalization

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
  (M₁ : Type*) [AddCommMonoid M₁] [Module R M₁] [Module A M₁] [IsScalarTower R A M₁]

@[simp]
lemma moduleLid_symm_apply (m : M₁) : (moduleLid S A M₁).symm m = 1 ⊗ₜ[R] m := rfl

variable (M₂ : Type*) [AddCommMonoid M₂] [Module R M₂] [Module A M₂] [IsScalarTower R A M₂]

@[simp]
lemma map_moduleTensorEquiv_tmul (m₁ : M₁) (m₂ : M₂) :
    moduleTensorEquiv S A M₁ M₂ (m₁ ⊗ₜ[A] m₂) = m₁ ⊗ₜ[R] m₂ := rfl

@[simp]
lemma map_moduleTensorEquiv_symm_tmul (m₁ : M₁) (m₂ : M₂) :
    (moduleTensorEquiv S A M₁ M₂).symm (m₁ ⊗ₜ[R] m₂) = m₁ ⊗ₜ[A] m₂ := rfl

end

section

open TensorProduct

variable {A : Type*} [CommSemiring A] (S : Submonoid A)
  (B : Type*) [CommSemiring B] [Algebra A B]
  (K : Type*) [CommSemiring K] [Algebra A K] [IsLocalization S K]
  (L : Type*) [CommSemiring L] [Algebra B L] [Algebra A L] [Algebra K L] [IsScalarTower A B L]
    [IsScalarTower A K L] [IsLocalizedModule (M := B) (M' := L) S (Algebra.linearMap B L)]
  (M : Type*) [AddCommMonoid M] [Module K M]
  (P : Type*) [AddCommMonoid P] [Module K P]

include S in
theorem tensorProduct_ext {g h : L ⊗[K] M →ₗ[K] P}
    (H : ∀ (x : B) (y : M), g ((algebraMap _ L x) ⊗ₜ[K] y) = h ((algebraMap _ L x) ⊗ₜ[K] y))
    : g = h := by
  apply TensorProduct.ext'
  intro l m
  obtain ⟨⟨x, s⟩, hl : (s : A) • l = algebraMap B L x⟩ :=
    IsLocalizedModule.surj (M:=B) (M':=L) S (Algebra.linearMap B L) l
  rw [← IsUnit.smul_left_cancel <| map_units K s]
  simpa [← map_smul, TensorProduct.smul_tmul', IsScalarTower.algebraMap_smul K, hl] using H x m

@[simps!]
noncomputable def leftModuleTensorEquiv {R : Type*} (M' : Type*)
    [Semiring M'] [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A]
    [IsLocalization S A] (M₁ : Type*) (M₂ : Type*) [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module M' M₁] [Module R M₁] [Module R M₂] [Module A M₁] [Module A M₂]
    [SMulCommClass A M' M₁] [SMulCommClass R M' M₁] [IsScalarTower R A M₁]
    [IsScalarTower R A M₂] :
    M₁ ⊗[A] M₂ ≃ₗ[M'] M₁ ⊗[R] M₂ where
  __ := IsLocalization.moduleTensorEquiv S A M₁ M₂
  map_smul' r x := by
    induction x with
    | zero => simp
    | tmul m₁ m₂ => simp [TensorProduct.smul_tmul']
    | add => simp_all

lemma leftModuleTensorEquiv_restrictScalars_eq {R M' : Type*} [CommSemiring M']
    [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A] [Algebra A M']
    [Algebra M' R] [IsLocalization S A] (M₁ : Type*) (M₂ : Type*) [AddCommMonoid M₁]
    [AddCommMonoid M₂] [Module M' M₁] [Module R M₁] [Module R M₂] [Module A M₁]
    [Module A M₂] [IsScalarTower A M' M₁] [IsScalarTower M' R M₁] [IsScalarTower R A M₁]
    [IsScalarTower R A M₂] :
    (IsLocalization.leftModuleTensorEquiv M' S A M₁ M₂).restrictScalars A =
      IsLocalization.moduleTensorEquiv S A M₁ M₂ := by
  rfl

end

end IsLocalization


