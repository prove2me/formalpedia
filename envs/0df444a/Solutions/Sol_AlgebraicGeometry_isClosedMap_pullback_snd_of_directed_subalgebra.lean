-- Prove2me | solution 1 for AlgebraicGeometry.isClosedMap_pullback_snd_of_directed_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/7e7b3f0c-e0ac-58bf-834c-3d7b1e5b9e95

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace ClosedLimitGC4

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

noncomputable def trans (S S' : Subalgebra R A) (h : S ≤ S') :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥S'))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥S))) :=
  pullback.lift (pullback.fst f _)
    (pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom))
    (by
      rw [pullback.condition, Category.assoc, ← Spec.map_comp]
      rfl)

theorem q_eq_comp_trans (S S' : Subalgebra R A) (h : S ≤ S')
    (q : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥S))))
    (hq₁ : q ≫ pullback.fst f _ = pullback.fst f _)
    (hq₂ : q ≫ pullback.snd f _ = pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S A)))
    (q' : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥S'))))
    (hq'₁ : q' ≫ pullback.fst f _ = pullback.fst f _)
    (hq'₂ : q' ≫ pullback.snd f _ = pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S' A))) :
    q = q' ≫ trans f S S' h := by
  apply pullback.hom_ext
  · rw [hq₁, Category.assoc, trans, pullback.lift_fst, hq'₁]
  · rw [hq₂, Category.assoc, trans, pullback.lift_snd, ← Category.assoc, hq'₂, Category.assoc, ← Spec.map_comp]
    rfl

theorem exists_lift (S : Subalgebra R A)
    (q : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥S))))
    (hq₁ : q ≫ pullback.fst f _ = pullback.fst f _)
    (hq₂ : q ≫ pullback.snd f _ = pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S A)))
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥S)))))
    (t : ↥(Spec (CommRingCat.of A)))
    (hzt : pullback.snd f _ z = Spec.map (CommRingCat.ofHom (algebraMap ↥S A)) t) :
    ∃ w : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A)))),
      q w = z ∧ pullback.snd f _ w = t := by
  obtain ⟨w', hw'₁, hw'₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R ↥S))))
    (g := Spec.map (CommRingCat.ofHom (algebraMap ↥S A))) z t hzt
  let φ : pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R ↥S))))
      (Spec.map (CommRingCat.ofHom (algebraMap ↥S A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst f _) (pullback.snd _ _)
      (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
          ← Spec.map_comp]
        rfl)
  have hφq : φ ≫ q = pullback.fst _ _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hq₁, pullback.lift_fst]
    · rw [Category.assoc, hq₂, ← Category.assoc, pullback.lift_snd, pullback.condition]
  refine ⟨φ w', ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hφq, hw'₁]
  · rw [← Scheme.Hom.comp_apply, pullback.lift_snd, hw'₂]

end ClosedLimitGC4

open ClosedLimitGC4 in
theorem solution
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type v} (S : ι → Subalgebra R A) (hdir : Directed (· ≤ ·) S) (hS : ∀ a : A, ∃ i, a ∈ S i)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (q : ∀ i, pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥(S i)))))
    (hq₁ : ∀ i, q i ≫ pullback.fst f _ = pullback.fst f _)
    (hq₂ : ∀ i, q i ≫ pullback.snd f _ =
      pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(S i) A)))
    (H : ∀ i, IsClosedMap (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R ↥(S i))))).base) :
    IsClosedMap (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).base := by
  classical
  haveI : Nonempty ι := by obtain ⟨i, -⟩ := hS 0; exact ⟨i⟩
  set fA := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A))) with hfA
  change IsClosedMap fA
  rw [isClosedMap_iff_specializingMap, specializingMap_iff_closure_singleton_subset]
  intro x t' ht'

  have hstage : ∀ i, ∃ w, q i w ∈ closure {q i x} ∧ fA w = t' := by
    intro i
    have hsp := (H i).specializingMap
    rw [specializingMap_iff_closure_singleton_subset] at hsp
    have ht'i : Spec.map (CommRingCat.ofHom (algebraMap ↥(S i) A)) t' ∈
        closure {pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R ↥(S i)))) (q i x)} := by
      rw [← Scheme.Hom.comp_apply, hq₂ i, Scheme.Hom.comp_apply, ← Set.image_singleton]
      exact image_closure_subset_closure_image (Scheme.Hom.continuous _) ⟨t', ht', rfl⟩
    obtain ⟨z, hz, hzt⟩ := hsp (q i x) ht'i
    obtain ⟨w, hwq, hwt⟩ := exists_lift f (S i) (q i) (hq₁ i) (hq₂ i) z t' (by rw [hzt])
    exact ⟨w, hwq.symm ▸ hz, hwt⟩

  have hF : IsCompact (fA.base ⁻¹' {t'} : Set _) := by
    rw [← Scheme.Hom.range_fiberι]
    exact isCompact_range (Scheme.Hom.continuous _)

  let C : ι → Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :=
    fun i => (q i).base ⁻¹' closure {q i x}
  have hC : ∀ i, IsClosed (C i) := fun i => isClosed_closure.preimage (Scheme.Hom.continuous _)
  have hmono : ∀ i i', S i ≤ S i' → C i' ⊆ C i := by
    intro i i' hle z hz
    change q i z ∈ closure {q i x}
    rw [q_eq_comp_trans f (S i) (S i') hle (q i) (hq₁ i) (hq₂ i) (q i') (hq₁ i') (hq₂ i'),
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← Set.image_singleton]
    exact image_closure_subset_closure_image (Scheme.Hom.continuous _) ⟨_, hz, rfl⟩
  have hfip : ∀ u : Finset ι, (fA.base ⁻¹' {t'} ∩ ⋂ i ∈ u, C i).Nonempty := by
    intro u
    obtain ⟨i₀, hi₀⟩ := hdir.finset_le u
    obtain ⟨w, hw, hwt⟩ := hstage i₀
    refine ⟨w, hwt, ?_⟩
    simp only [Set.mem_iInter]
    exact fun i hi => hmono i i₀ (hi₀ i hi) hw
  obtain ⟨z, hzt, hzC⟩ := hF.inter_iInter_nonempty C hC hfip

  have hzx : z ∈ closure {x} := by
    by_contra hcon
    let U : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).Opens :=
      ⟨(closure {x})ᶜ, isClosed_closure.isOpen_compl⟩
    obtain ⟨i, W, hzW, hWU⟩ :=
      AlgebraicGeometry.Scheme.exists_mem_preimage_le_of_directed_subalgebra S hdir hS f q hq₁ hq₂ U z hcon
    have hqz : q i z ∈ closure {q i x} := Set.mem_iInter.mp hzC i
    have hxi : q i x ∈ (W : Set _) := by
      obtain ⟨y, hyW, hyx⟩ := mem_closure_iff.mp hqz W W.isOpen hzW
      rw [Set.mem_singleton_iff.mp hyx] at hyW
      exact hyW
    have : x ∈ (U : Set _) := hWU hxi
    exact this (subset_closure (Set.mem_singleton x))
  exact ⟨z, hzx, hzt⟩

end S_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra
end P2MW
export P2MW.S_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra (solution)
