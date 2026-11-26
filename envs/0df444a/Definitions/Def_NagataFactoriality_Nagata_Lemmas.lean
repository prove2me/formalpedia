-- Prove2me | Definitions.Def_NagataFactoriality_Nagata_Lemmas
-- name    : NagataFactoriality_Nagata_Lemmas
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:57:43.6979+00:00
-- url     : https://prove2.me/theorems/0574e05d-3d5e-5a3f-83c8-65650f2390d6
-- title:
--   Lemmas
-- statement:
--   Definitions and structural lemmas for Lemmas, from Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz (Arthur742Ramos/NagataFactoriality; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Prime-generated Nagata factoriality theorem for Noetherian integral domains development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Theorems.Thm_NagataFactoriality_IsLocalization_map_eq_zero_iff
import Theorems.Thm_NagataFactoriality_Localization_den_mul_mk
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_den
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_mk
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_of
import Theorems.Thm_NagataFactoriality_Localization_mk_one
import Theorems.Thm_NagataFactoriality_Localization_of_add
import Theorems.Thm_NagataFactoriality_Localization_of_eq_zero_iff
import Theorems.Thm_NagataFactoriality_Localization_of_mul
import Theorems.Thm_NagataFactoriality_Localization_of_mul_mk
import Theorems.Thm_NagataFactoriality_Localization_of_neg
import Theorems.Thm_NagataFactoriality_Localization_of_one
import Theorems.Thm_NagataFactoriality_Localization_of_zero
import Theorems.Thm_NagataFactoriality_Submonoid_zero_notMem_of_prime_or_unit
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_mem_b89487295096
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c
attribute [local simp] NagataFactoriality.IsLocalization.map_eq_zero_iff
attribute [local simp] NagataFactoriality.Localization.den_mul_mk
attribute [local simp] NagataFactoriality.Localization.mk_mul_den
attribute [local simp] NagataFactoriality.Localization.mk_mul_mk
attribute [local simp] NagataFactoriality.Localization.mk_mul_of
attribute [local simp] NagataFactoriality.Localization.mk_one
attribute [local simp] NagataFactoriality.Localization.of_add
attribute [local simp] NagataFactoriality.Localization.of_eq_zero_iff
attribute [local simp] NagataFactoriality.Localization.of_mul
attribute [local simp] NagataFactoriality.Localization.of_mul_mk
attribute [local simp] NagataFactoriality.Localization.of_neg
attribute [local simp] NagataFactoriality.Localization.of_one
attribute [local simp] NagataFactoriality.Localization.of_zero
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil
attribute [local simp] P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_mem_b89487295096
attribute [local simp] P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
attribute [local simp] P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
attribute [local simp] P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c


set_option autoImplicit false
namespace NagataFactoriality
def Avoids {α : Type*} [CommRing α] [IsDomain α] (S : Submonoid α) (p : α) : Prop :=
  ∀ s : α, s ∈ S → ¬ p ∣ s
def PrimeGenerated {α : Type*} [CommRing α] (S : Submonoid α) : Prop :=
  ∀ s : α, s ∈ S → ∃ f : Multiset α, (∀ q ∈ f, q ∈ S ∧ Prime q) ∧ f.prod = s
def submonoidZeroNotMemFact {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) : Fact ((0 : α) ∉ S) :=
  ⟨Submonoid.zero_notMem_of_prime_or_unit hS⟩
theorem multiset_prod_ne_zero_of_prime_factors {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) : f.prod ≠ 0 := by
  revert hf
  refine Multiset.induction_on f ?_ ?_
  · intro _
    exact one_ne_zero
  · intro q qs ih hqs
    have hq : Prime q := hqs q (by simp)
    have htail : ∀ r ∈ qs, Prime r := by
      intro r hr
      exact hqs r (by simp [hr])
    simpa using mul_ne_zero hq.ne_zero (ih htail)
theorem zero_notMem_of_primeGenerated {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : PrimeGenerated S) : (0 : α) ∉ S := by
  intro hs
  rcases hS 0 hs with ⟨f, hf, hprod⟩
  exact (multiset_prod_ne_zero_of_prime_factors (fun q hq => (hf q hq).2)) hprod
end NagataFactoriality


