-- Prove2me | solution 1 for AlonTarsi.coeff_outExp_graphPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:49.439121+00:00
-- url     : https://prove2.me/submissions/ba4afb6d-c841-4fb7-8139-f87f5c2d1eaf

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
public import Theorems.Thm_AlonTarsi_sum_single_apply
public import Theorems.Thm_AlonTarsi_outExp_apply

set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open AlonTarsi
variable {V : Type*}
namespace AlonTarsi
theorem _root_.solution [DecidableEq V] [Fintype V] (A : Finset (V × V)) :
    (graphPoly A).coeff (outExp A) =
      ∑ t ∈ A.powerset with (∀ v, #{p ∈ t | p.1 = v} = #{p ∈ t | p.2 = v}), (-1 : ℤ) ^ #t := by
  have hexp : graphPoly A = ∑ t ∈ A.powerset,
      monomial (∑ a ∈ t, Finsupp.single a.2 1 + ∑ a ∈ A \ t, Finsupp.single a.1 1)
        ((-1 : ℤ) ^ #t) := by
    unfold graphPoly
    have : ∀ a : V × V, (X a.1 - X a.2 : MvPolynomial V ℤ) = -X a.2 + X a.1 := fun a => by ring
    simp_rw [this]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h1 : ∏ a ∈ t, (-X a.2 : MvPolynomial V ℤ) =
        C ((-1 : ℤ) ^ #t) * monomial (∑ a ∈ t, Finsupp.single a.2 1) 1 := by
      rw [monomial_sum_one]
      have : ∀ a : V × V,
          (-X a.2 : MvPolynomial V ℤ) = C (-1) * monomial (Finsupp.single a.2 1) 1 := fun a => by
            rw [← X, map_neg, map_one]; ring
      simp_rw [this]
      rw [Finset.prod_mul_distrib, Finset.prod_const, map_pow]
    have h2 : ∏ a ∈ A \ t, (X a.1 : MvPolynomial V ℤ) =
        monomial (∑ a ∈ A \ t, Finsupp.single a.1 1) 1 := by
      rw [monomial_sum_one]; rfl
    rw [h1, h2, mul_assoc, monomial_mul, one_mul, C_mul_monomial, mul_one]
  rw [hexp, coeff_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_powerset] at ht
  rw [coeff_monomial]
  congr 1
  apply propext
  rw [Finsupp.ext_iff]
  refine forall_congr' fun v => ?_
  rw [Finsupp.add_apply, sum_single_apply, sum_single_apply, outExp_apply]
  have hsplit : #{a ∈ A | a.1 = v} = #{a ∈ A \ t | a.1 = v} + #{a ∈ t | a.1 = v} := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext a
      simp only [mem_filter, mem_union, mem_sdiff]
      constructor
      · rintro ⟨ha, rfl⟩
        by_cases hat : a ∈ t
        · exact Or.inr ⟨hat, rfl⟩
        · exact Or.inl ⟨⟨ha, hat⟩, rfl⟩
      · rintro (⟨⟨ha, _⟩, rfl⟩ | ⟨ha, rfl⟩)
        · exact ⟨ha, rfl⟩
        · exact ⟨ht ha, rfl⟩
    · rw [Finset.disjoint_left]
      intro a ha hb
      simp only [mem_filter, mem_sdiff] at ha hb
      exact ha.1.2 hb.1
  omega
end AlonTarsi
