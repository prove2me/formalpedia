-- Prove2me | solution 1 for AlgebraicGeometry.isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ab7bdbb4-28bb-5287-9197-4f2171941bd3

import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_CommRingCat_isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective
import Theorems.Thm_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld.SpecialFormal.ModuliPackage

universe u

namespace RAPProof
theorem po_surj {C C₀ A A₀ : CommRingCat.{u}} {φ : C ⟶ C₀} {u : C ⟶ A} {u₀ : C₀ ⟶ A₀} {q : A ⟶ A₀}
    (h : IsPushout φ u u₀ q) (hφ : Function.Surjective φ.hom) : Function.Surjective q.hom := by
  have htop := CommRingCat.closure_range_union_range_eq_top_of_isPushout h
  have hsub : Set.range u₀ ∪ Set.range q ⊆ (q.hom.range : Set A₀) := by
    rintro z (⟨c₀, rfl⟩ | ⟨a, rfl⟩)
    · obtain ⟨c, rfl⟩ := hφ c₀
      refine ⟨u c, ?_⟩
      have := congrArg (fun k : C ⟶ A₀ => k c) h.w
      simpa using this.symm
    · exact ⟨a, rfl⟩
  have hle : Subring.closure (Set.range u₀ ∪ Set.range q) ≤ q.hom.range := Subring.closure_le.mpr hsub
  rw [htop, top_le_iff] at hle
  intro z
  have hz : z ∈ q.hom.range := hle ▸ Subring.mem_top z
  exact hz

theorem po_ker {C C₀ A A₀ : CommRingCat.{u}} {φ : C ⟶ C₀} {u : C ⟶ A} {u₀ : C₀ ⟶ A₀} {q : A ⟶ A₀}
    (h : IsPushout φ u u₀ q) (hφ : Function.Surjective φ.hom) :
    RingHom.ker q.hom = (RingHom.ker φ.hom).map u.hom := by
  apply le_antisymm
  ·
    set I : Ideal A := (RingHom.ker φ.hom).map u.hom with hI
    have hker : RingHom.ker φ.hom ≤ RingHom.ker ((Ideal.Quotient.mk I).comp u.hom) := by
      intro c hc
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hc
    let c₀ : C₀ →+* A ⧸ I := φ.hom.liftOfSurjective hφ ⟨(Ideal.Quotient.mk I).comp u.hom, hker⟩
    have hc₀ : c₀.comp φ.hom = (Ideal.Quotient.mk I).comp u.hom := RingHom.liftOfSurjective_comp _ hφ _
    have hw : φ ≫ CommRingCat.ofHom c₀ = u ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      ext c
      exact congrArg (fun k : C →+* A ⧸ I => k c) hc₀
    let d := h.desc (CommRingCat.ofHom c₀) (CommRingCat.ofHom (Ideal.Quotient.mk I)) hw
    have hd : q ≫ d = CommRingCat.ofHom (Ideal.Quotient.mk I) := h.inr_desc _ _ hw
    intro x hx
    rw [RingHom.mem_ker] at hx
    have := congrArg (fun k : A ⟶ CommRingCat.of (A ⧸ I) => k x) hd
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hx, map_zero, CommRingCat.hom_ofHom] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [RingHom.mem_ker] at hc
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun k : C ⟶ A₀ => k c) h.w
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hc, map_zero] at this
    exact this.symm

theorem isPullback_pullbackRing {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] (φ' : B' →+* B) (φ'' : B'' →+* B) :
    IsPullback (CommRingCat.ofHom (pullbackFst φ' φ'')) (CommRingCat.ofHom (pullbackSnd φ' φ''))
      (CommRingCat.ofHom φ') (CommRingCat.ofHom φ'') := by
  have w : CommRingCat.ofHom (pullbackFst φ' φ'') ≫ CommRingCat.ofHom φ' =
      CommRingCat.ofHom (pullbackSnd φ' φ'') ≫ CommRingCat.ofHom φ'' := by
    ext ⟨x, hx⟩
    exact hx
  refine IsPullback.of_isLimit' ⟨w⟩ ?_
  fapply PullbackCone.IsLimit.mk
  · intro s
    refine CommRingCat.ofHom ((s.fst.hom.prod s.snd.hom).codRestrict (pullbackRing φ' φ'') ?_)
    intro x
    exact congr_arg (fun f : s.pt →+* B => f x) (congrArg CommRingCat.Hom.hom s.condition)
  · intro s
    ext x
    rfl
  · intro s
    ext x
    rfl
  · intro s m e₁ e₂
    refine CommRingCat.hom_ext (RingHom.ext fun (x : s.pt) => Subtype.ext ?_)
    change (m x).1 = (_, _)
    have eq1 := (congr_arg (fun f : s.pt →+* B' => f x) (congrArg CommRingCat.Hom.hom e₁) :)
    have eq2 := (congr_arg (fun f : s.pt →+* B'' => f x) (congrArg CommRingCat.Hom.hom e₂) :)
    rw [← eq1, ← eq2]
    rfl

end RAPProof

theorem solution
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    {A A' A'' A₀ : CommRingCat.{0}}
    {a' : A ⟶ A'} {a'' : A ⟶ A''} {g' : A' ⟶ A₀} {g'' : A'' ⟶ A₀} (hA : IsPullback a' a'' g' g'')
    (u : CommRingCat.of ↥(pullbackRing φ' φ'') ⟶ A) (s' : CommRingCat.of B' ⟶ A') (s'' : CommRingCat.of B'' ⟶ A'')
    (s₀ : CommRingCat.of B ⟶ A₀)
    (hu' : CommRingCat.ofHom (pullbackFst φ' φ'') ≫ s' = u ≫ a')
    (hu'' : CommRingCat.ofHom (pullbackSnd φ' φ'') ≫ s'' = u ≫ a'')
    (hg' : CommRingCat.ofHom φ' ≫ s₀ = s' ≫ g') (hg'' : CommRingCat.ofHom φ'' ≫ s₀ = s'' ≫ g'')
    (hco' : IsPushout (CommRingCat.ofHom φ') s' s₀ g') (hco'' : IsPushout (CommRingCat.ofHom φ'') s'' s₀ g'') :
    IsPullback (Spec.map a') (Spec.map s') (Spec.map u) (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ∧
    IsPullback (Spec.map a'') (Spec.map s'') (Spec.map u) (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) ∧
    IsPushout (Spec.map g') (Spec.map g'') (Spec.map a') (Spec.map a'') := by
  have hC := RAPProof.isPullback_pullbackRing φ' φ''
  obtain ⟨h1, h2⟩ := CommRingCat.isPushout_of_isPullback_of_isPullback_of_isPushout_of_surjective hC hA u s' s'' s₀
    hu' hu'' hg' hg'' hφ's hφ''s hco' hco''
  refine ⟨(AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _ h1).flip,
    (AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _ h2).flip, ?_⟩
  have hφc : Function.Surjective (CommRingCat.ofHom φ'').hom := hφ''s
  have hsurj : Function.Surjective g''.hom := RAPProof.po_surj hco'' hφc
  have hker : RingHom.ker g''.hom = (RingHom.ker (CommRingCat.ofHom φ'').hom).map s''.hom := RAPProof.po_ker hco'' hφc
  refine AlgebraicGeometry.isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent hA hsurj fun x hx => ?_
  rw [hker] at hx
  obtain ⟨n, hn⟩ := hφ''n
  refine ⟨n, ?_⟩
  have hx' : x ^ n ∈ ((RingHom.ker (CommRingCat.ofHom φ'').hom).map s''.hom) ^ n := Ideal.pow_mem_pow hx n
  have hn' : RingHom.ker (CommRingCat.ofHom φ'').hom ^ n = ⊥ := hn
  rw [← Ideal.map_pow, hn', Ideal.map_bot] at hx'
  exact (Submodule.mem_bot _).mp hx'

end S_AlgebraicGeometry_isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent
end P2MW
export P2MW.S_AlgebraicGeometry_isPullback_isPushout_specMap_of_isPullback_pullbackRing_of_isPushout_of_surjective_of_isNilpotent (solution)
