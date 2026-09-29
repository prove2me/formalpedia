-- Prove2me | solution 1 for AddMonoidHom.finite_setOf_pushPull_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8dff23f6-8e43-5cc4-b3ec-f09dc161a36b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddMonoidHom_finite_setOf_pushPull_eq_zero

set_option autoImplicit false

namespace KerFin

theorem finite_ker_comp {M : Type*} [AddCommGroup M] (A B : M →+ M) (hA : {x | A x = 0}.Finite) (hB : {x | B x = 0}.Finite) :
    {x | A (B x) = 0}.Finite := by
  classical
  have hsub : {x | A (B x) = 0} ⊆ ⋃ y ∈ {y | A y = 0}, {x | B x = y} := fun x hx => by
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨B x, hx, rfl⟩
  refine Set.Finite.subset (Set.Finite.biUnion hA fun y _ => ?_) hsub
  by_cases h : ∃ x₀, B x₀ = y
  · obtain ⟨x₀, rfl⟩ := h
    have : {x | B x = B x₀} = (fun k => x₀ + k) '' {k | B k = 0} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro hx; exact ⟨x - x₀, by rw [map_sub, hx, sub_self], by abel⟩
      · rintro ⟨k, hk, rfl⟩; rw [map_add, hk, add_zero]
    rw [this]; exact hB.image _
  · have : {x | B x = y} = ∅ := Set.eq_empty_of_forall_notMem fun x hx => h ⟨x, hx⟩
    rw [this]; exact Set.finite_empty

theorem det_apply_eq_zero {M : Type*} [AddCommGroup M] (p : ℕ) (F V δ δ' : M →+ M)
    (hFV : ∀ x, F (V x) = p • x) (hVF : ∀ x, V (F x) = p • x) (hδδ' : ∀ x, δ (δ' x) = x)
    (hFδ : ∀ x, F (δ x) = δ (F x)) (hFδ' : ∀ x, F (δ' x) = δ' (F x)) (hVδ' : ∀ x, V (δ' x) = δ' (V x))
    (a b : M) (ha : (1 + p) • a + (V b + F (δ b)) = 0) (hb : (F a + δ' (V a)) + (1 + p) • b = 0) :
    (a - δ' (V (V a))) - δ (F (F (a - δ' (V (V a))))) = 0 := by

  have e1 : δ (F (F (a - δ' (V (V a))))) = δ (F (F a)) - (p * p) • a := by
    rw [map_sub, map_sub, map_sub, hFδ', hFδ', hδδ', hFV, map_nsmul, hFV, smul_smul]

  have e2 : (1 + p) • ((1 + p) • a + (V b + F (δ b))) - (V (F a + δ' (V a) + (1 + p) • b) + F (δ (F a + δ' (V a) + (1 + p) • b))) = 0 := by
    rw [ha, hb, smul_zero, map_zero, map_zero, map_zero, add_zero, sub_zero]
  simp only [map_add, map_nsmul, hVF, hVδ', hFδ, hδδ', hFV] at e2
  rw [e1, ← e2]
  module

theorem _root_.P2MW.S_AddMonoidHom_finite_setOf_pushPull_eq_zero.solution {M : Type*} [AddCommGroup M] (p : ℕ) (F V δ δ' : M →+ M)
    (hFV : F.comp V = p • AddMonoidHom.id M) (hVF : V.comp F = p • AddMonoidHom.id M)
    (hδδ' : δ.comp δ' = AddMonoidHom.id M) (hδ'δ : δ'.comp δ = AddMonoidHom.id M)
    (hFδ : F.comp δ = δ.comp F) (hVδ : V.comp δ = δ.comp V) (hFδ' : F.comp δ' = δ'.comp F) (hVδ' : V.comp δ' = δ'.comp V)
    (h1 : {x | x - δ (F (F x)) = 0}.Finite) (h2 : {x | x - δ' (V (V x)) = 0}.Finite) :
    {ab : M × M | (1 + p) • ab.1 + (V ab.2 + F (δ ab.2)) = 0 ∧ (F ab.1 + δ' (V ab.1)) + (1 + p) • ab.2 = 0}.Finite := by

  have pFV : ∀ x, F (V x) = p • x := fun x => by simpa using DFunLike.congr_fun hFV x
  have pVF : ∀ x, V (F x) = p • x := fun x => by simpa using DFunLike.congr_fun hVF x
  have pδδ' : ∀ x, δ (δ' x) = x := fun x => by simpa using DFunLike.congr_fun hδδ' x
  have pδ'δ : ∀ x, δ' (δ x) = x := fun x => by simpa using DFunLike.congr_fun hδ'δ x
  have pFδ : ∀ x, F (δ x) = δ (F x) := fun x => by simpa using DFunLike.congr_fun hFδ x
  have pVδ : ∀ x, V (δ x) = δ (V x) := fun x => by simpa using DFunLike.congr_fun hVδ x
  have pFδ' : ∀ x, F (δ' x) = δ' (F x) := fun x => by simpa using DFunLike.congr_fun hFδ' x
  have pVδ' : ∀ x, V (δ' x) = δ' (V x) := fun x => by simpa using DFunLike.congr_fun hVδ' x

  let A : M →+ M := AddMonoidHom.id M - δ.comp (F.comp F)
  let B : M →+ M := AddMonoidHom.id M - δ'.comp (V.comp V)
  have hA : {x | A x = 0}.Finite := by simpa [A] using h1
  have hB : {x | B x = 0}.Finite := by simpa [B] using h2
  have hA' : {x | B x = 0}.Finite := hB
  have hAB := finite_ker_comp A B hA hB
  have hBA := finite_ker_comp B A hB hA
  refine Set.Finite.subset (hAB.prod hBA) ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  refine ⟨?_, ?_⟩
  ·
    show (a - δ' (V (V a))) - δ (F (F (a - δ' (V (V a))))) = 0
    exact det_apply_eq_zero p F V δ δ' pFV pVF pδδ' pFδ pFδ' pVδ' a b ha hb
  ·
    show (b - δ (F (F b))) - δ' (V (V (b - δ (F (F b))))) = 0
    refine det_apply_eq_zero p V F δ' δ pVF pFV pδ'δ pVδ' pVδ pFδ b a ?_ ?_
    · have : (1 + p) • b + (F a + V (δ' a)) = (F a + δ' (V a)) + (1 + p) • b := by rw [pVδ', add_comm]
      rw [this]; exact hb
    · have : (V b + δ (F b)) + (1 + p) • a = (1 + p) • a + (V b + F (δ b)) := by rw [pFδ, add_comm]
      rw [this]; exact ha

end KerFin

end S_AddMonoidHom_finite_setOf_pushPull_eq_zero
end P2MW
export P2MW.S_AddMonoidHom_finite_setOf_pushPull_eq_zero (solution)
