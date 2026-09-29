-- Prove2me | solution 1 for AdjoinRoot.exists_isLocalRing_isAdicComplete_of_monic_of_coeff_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/25ed4fb7-3380-5a4f-8cc0-8298937081f6

import Mathlib
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdjoinRoot_exists_isLocalRing_isAdicComplete_of_monic_of_coeff_mem_maximalIdeal

set_option autoImplicit false

open IsLocalRing Polynomial

namespace AdjoinRootCompleteAux

theorem aeval_sub_algebraMap_coeff_zero_mem {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (x : B) (p : R[X]) :
    aeval x p - algebraMap R B (p.coeff 0) ∈ Ideal.span ({x} : Set B) := by
  rw [Ideal.mem_span_singleton']
  refine ⟨aeval x p.divX, ?_⟩
  have h := congrArg (aeval x) (Polynomial.X_mul_divX_add p)
  rw [map_add, map_mul, aeval_X, aeval_C] at h
  rw [← h]
  ring

theorem mem_of_aeval_eq_zero_of_coeff_mem {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {P : R[X]} (hP : P.Monic) (𝔫 : Ideal B) [𝔫.IsPrime]
    (hcoef : ∀ i, i < P.natDegree → algebraMap R B (P.coeff i) ∈ 𝔫) {x : B} (hx : aeval x P = 0) : x ∈ 𝔫 := by
  apply Ideal.IsPrime.mem_of_pow_mem ‹𝔫.IsPrime› P.natDegree
  have h := hx
  rw [hP.as_sum, map_add, map_pow, aeval_X, map_sum] at h
  have hsum : ∑ i ∈ Finset.range P.natDegree, aeval x (C (P.coeff i) * X ^ i) ∈ 𝔫 := by
    refine Ideal.sum_mem _ fun i hi => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X]
    exact Ideal.mul_mem_right _ _ (hcoef i (Finset.mem_range.mp hi))
  have : x ^ P.natDegree = -(∑ i ∈ Finset.range P.natDegree, aeval x (C (P.coeff i) * X ^ i)) :=
    eq_neg_of_add_eq_zero_left h
  rw [this]
  exact Submodule.neg_mem _ hsum

section Main

variable {S : Type*} [CommRing S] [IsLocalRing S] (g : S[X]) (hg : g.Monic) (hn : 1 ≤ g.natDegree)
  (hcoeff : ∀ i < g.natDegree, g.coeff i ∈ maximalIdeal S)

theorem aeval_root : aeval (AdjoinRoot.root g) g = 0 := by
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem exists_sub_algebraMap_mem (a : AdjoinRoot g) :
    ∃ c : S, a - algebraMap S (AdjoinRoot g) c ∈ Ideal.span {AdjoinRoot.root g} := by
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective a
  refine ⟨r.coeff 0, ?_⟩
  rw [← AdjoinRoot.aeval_eq]
  exact aeval_sub_algebraMap_coeff_zero_mem (AdjoinRoot.root g) r

include hn hcoeff in
theorem eval₂_residue_zero : g.eval₂ (residue S) 0 = 0 := by
  rw [Polynomial.eval₂_at_zero, residue_eq_zero_iff]
  exact hcoeff 0 (by omega)

noncomputable def resA : AdjoinRoot g →+* ResidueField S :=
  AdjoinRoot.lift (residue S) 0 (eval₂_residue_zero g hn hcoeff)

theorem resA_algebraMap (s : S) : resA g hn hcoeff (algebraMap S (AdjoinRoot g) s) = residue S s := by
  rw [AdjoinRoot.algebraMap_eq, resA, AdjoinRoot.lift_of]

theorem resA_root : resA g hn hcoeff (AdjoinRoot.root g) = 0 := by
  rw [resA, AdjoinRoot.lift_root]

theorem resA_surjective : Function.Surjective (resA g hn hcoeff) := fun t => by
  obtain ⟨s, rfl⟩ := residue_surjective t
  exact ⟨algebraMap S (AdjoinRoot g) s, resA_algebraMap g hn hcoeff s⟩

theorem ker_isMaximal : (RingHom.ker (resA g hn hcoeff)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (resA_surjective g hn hcoeff)

theorem span_root_le_ker : Ideal.span {AdjoinRoot.root g} ≤ RingHom.ker (resA g hn hcoeff) := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact resA_root g hn hcoeff

include hg in

theorem eq_ker_of_isMaximal (𝔫 : Ideal (AdjoinRoot g)) [h𝔫 : 𝔫.IsMaximal] :
    𝔫 = RingHom.ker (resA g hn hcoeff) := by
  haveI : Module.Finite S (AdjoinRoot g) := hg.finite_adjoinRoot
  have hunder : ∀ s ∈ maximalIdeal S, algebraMap S (AdjoinRoot g) s ∈ 𝔫 := by
    intro s hs
    have hmax : (𝔫.comap (algebraMap S (AdjoinRoot g))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫
    have heq : 𝔫.comap (algebraMap S (AdjoinRoot g)) = maximalIdeal S := IsLocalRing.eq_maximalIdeal hmax
    rw [← heq] at hs
    exact hs
  have hcoef : ∀ i, i < g.natDegree → algebraMap S (AdjoinRoot g) (g.coeff i) ∈ 𝔫 :=
    fun i hi => hunder _ (hcoeff i hi)
  have hx : AdjoinRoot.root g ∈ 𝔫 := mem_of_aeval_eq_zero_of_coeff_mem hg 𝔫 hcoef (aeval_root g)
  have hsp : Ideal.span {AdjoinRoot.root g} ≤ 𝔫 := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hx
  symm
  refine (ker_isMaximal g hn hcoeff).eq_of_le h𝔫.ne_top ?_
  intro a ha
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem g a
  have hc0 : residue S c = 0 := by
    have h1 : resA g hn hcoeff (a - algebraMap S (AdjoinRoot g) c) = 0 := span_root_le_ker g hn hcoeff hc
    rw [map_sub, RingHom.mem_ker.mp ha, resA_algebraMap, zero_sub, neg_eq_zero] at h1
    exact h1
  have hcm : c ∈ maximalIdeal S := (residue_eq_zero_iff c).mp hc0
  have : a = (a - algebraMap S (AdjoinRoot g) c) + algebraMap S (AdjoinRoot g) c := by ring
  rw [this]
  exact Ideal.add_mem _ (hsp hc) (hunder c hcm)

include hg hn hcoeff in
theorem isLocalRing : IsLocalRing (AdjoinRoot g) :=
  IsLocalRing.of_unique_max_ideal
    ⟨RingHom.ker (resA g hn hcoeff), ker_isMaximal g hn hcoeff,
      fun 𝔫 h𝔫 => eq_ker_of_isMaximal g hg hn hcoeff 𝔫 (h𝔫 := h𝔫)⟩

include hg in
theorem ker_eq_maximalIdeal :
    RingHom.ker (resA g hn hcoeff) = @maximalIdeal (AdjoinRoot g) _ (isLocalRing g hg hn hcoeff) := by
  letI := isLocalRing g hg hn hcoeff
  exact IsLocalRing.eq_maximalIdeal (ker_isMaximal g hn hcoeff)

include hg in
theorem mem_maximalIdeal_iff (a : AdjoinRoot g) :
    a ∈ @maximalIdeal (AdjoinRoot g) _ (isLocalRing g hg hn hcoeff) ↔ resA g hn hcoeff a = 0 := by
  rw [← ker_eq_maximalIdeal g hg hn hcoeff, RingHom.mem_ker]

include hg hn hcoeff in
theorem isLocalHom_algebraMap : IsLocalHom (algebraMap S (AdjoinRoot g)) := by
  letI := isLocalRing g hg hn hcoeff
  refine ⟨fun s hs => ?_⟩
  by_contra hns
  have hsm : s ∈ maximalIdeal S := hns
  have : algebraMap S (AdjoinRoot g) s ∈ maximalIdeal (AdjoinRoot g) := by
    rw [mem_maximalIdeal_iff g hg hn hcoeff, resA_algebraMap, residue_eq_zero_iff]
    exact hsm
  exact (IsLocalRing.mem_maximalIdeal _).mp this hs

include hg in

theorem maximalIdeal_eq :
    @maximalIdeal (AdjoinRoot g) _ (isLocalRing g hg hn hcoeff) =
      (maximalIdeal S).map (algebraMap S (AdjoinRoot g)) ⊔ Ideal.span {AdjoinRoot.root g} := by
  letI := isLocalRing g hg hn hcoeff
  haveI := isLocalHom_algebraMap g hg hn hcoeff
  apply le_antisymm
  · intro a ha
    obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem g a
    have hcA : algebraMap S (AdjoinRoot g) c ∈ maximalIdeal (AdjoinRoot g) := by
      have : algebraMap S (AdjoinRoot g) c = a - (a - algebraMap S (AdjoinRoot g) c) := by ring
      rw [this]
      refine Ideal.sub_mem _ ha ?_
      rw [mem_maximalIdeal_iff g hg hn hcoeff]
      exact span_root_le_ker g hn hcoeff hc
    have hcm : c ∈ maximalIdeal S := by
      rw [mem_maximalIdeal_iff g hg hn hcoeff, resA_algebraMap, residue_eq_zero_iff] at hcA
      exact hcA
    have : a = algebraMap S (AdjoinRoot g) c + (a - algebraMap S (AdjoinRoot g) c) := by ring
    rw [this]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hcm) hc
  · refine sup_le ?_ ?_
    · exact ((IsLocalRing.local_hom_TFAE (algebraMap S (AdjoinRoot g))).out 0 2).mp ‹_›
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal_iff g hg hn hcoeff]
      exact resA_root g hn hcoeff

end Main

end AdjoinRootCompleteAux

theorem solution
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    (g : S[X]) (hg : g.Monic) (hn : 1 ≤ g.natDegree)
    (hcoeff : ∀ i < g.natDegree, g.coeff i ∈ maximalIdeal S) :
    ∃ (_ : IsLocalRing (AdjoinRoot g)),
      IsAdicComplete (maximalIdeal (AdjoinRoot g)) (AdjoinRoot g) ∧
      IsNoetherianRing (AdjoinRoot g) ∧ Module.Finite S (AdjoinRoot g) ∧
      Function.Surjective (⇑(residue (AdjoinRoot g)) ∘ ⇑(algebraMap S (AdjoinRoot g))) ∧
      AdjoinRoot.root g ∈ maximalIdeal (AdjoinRoot g) ∧
      maximalIdeal (AdjoinRoot g) =
        (maximalIdeal S).map (algebraMap S (AdjoinRoot g)) ⊔ Ideal.span {AdjoinRoot.root g} := by
  haveI hloc : IsLocalRing (AdjoinRoot g) := AdjoinRootCompleteAux.isLocalRing g hg hn hcoeff
  haveI hfin : Module.Finite S (AdjoinRoot g) := hg.finite_adjoinRoot
  haveI hlh : IsLocalHom (algebraMap S (AdjoinRoot g)) := AdjoinRootCompleteAux.isLocalHom_algebraMap g hg hn hcoeff
  haveI hnoeth : IsNoetherianRing (AdjoinRoot g) := isNoetherian_of_tower S (S := AdjoinRoot g) (M := AdjoinRoot g) inferInstance
  have hcpl : IsAdicComplete (maximalIdeal (AdjoinRoot g)) (AdjoinRoot g) :=
    IsLocalRing.isAdicComplete_of_module_finite (𝒪 := S)
  refine ⟨hloc, hcpl, hnoeth, hfin, fun t => ?_, ?_, AdjoinRootCompleteAux.maximalIdeal_eq g hg hn hcoeff⟩
  · obtain ⟨a, rfl⟩ := residue_surjective t
    obtain ⟨c, hc⟩ := AdjoinRootCompleteAux.exists_sub_algebraMap_mem g a
    refine ⟨c, ?_⟩
    show residue (AdjoinRoot g) (algebraMap S (AdjoinRoot g) c) = residue (AdjoinRoot g) a
    rw [eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      AdjoinRootCompleteAux.mem_maximalIdeal_iff g hg hn hcoeff]
    exact AdjoinRootCompleteAux.span_root_le_ker g hn hcoeff hc
  · rw [AdjoinRootCompleteAux.mem_maximalIdeal_iff g hg hn hcoeff]
    exact AdjoinRootCompleteAux.resA_root g hn hcoeff

end S_AdjoinRoot_exists_isLocalRing_isAdicComplete_of_monic_of_coeff_mem_maximalIdeal
end P2MW
export P2MW.S_AdjoinRoot_exists_isLocalRing_isAdicComplete_of_monic_of_coeff_mem_maximalIdeal (solution)
