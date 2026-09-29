-- Prove2me | solution 1 for AlgebraicGeometry.isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/789480f5-5dc5-5d4a-8e31-a525287469ff

import Mathlib
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import Theorems.Thm_AlgebraicGeometry_isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld.SpecialFormal.ModuliPackage

namespace ProdPO31

universe v w

theorem isPullback_pullbackMap {C : Type v} [Category.{w} C] [HasPullbacks C]
    {S S' X Y X' Y' : C} (fX : X ⟶ S) (fY : Y ⟶ S) (fX' : X' ⟶ S') (fY' : Y' ⟶ S') (s : S' ⟶ S)
    (kX : X' ⟶ X) (kY : Y' ⟶ Y) (hX : IsPullback kX fX' fX s) (hY : IsPullback kY fY' fY s) :
    IsPullback (pullback.map fX' fY' fX fY kX kY s hX.w.symm hY.w.symm)
      (pullback.fst fX' fY' ≫ fX') (pullback.fst fX fY ≫ fX) s := by
  have comm : pullback.map fX' fY' fX fY kX kY s hX.w.symm hY.w.symm ≫ (pullback.fst fX fY ≫ fX) =
      (pullback.fst fX' fY' ≫ fX') ≫ s := by
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, hX.w, Category.assoc]
  refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm
    (fun c => pullback.lift
      (hX.lift (c.fst ≫ pullback.fst fX fY) c.snd (by rw [Category.assoc]; exact c.condition))
      (hY.lift (c.fst ≫ pullback.snd fX fY) c.snd
        (by rw [Category.assoc, ← pullback.condition]; exact c.condition))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd]))
    (fun c => ?_) (fun c => ?_) (fun c m h₁ h₂ => ?_)⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsPullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.lift_fst]
  · rw [pullback.lift_fst_assoc, IsPullback.lift_snd]
  · apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply hX.hom_ext
      · rw [IsPullback.lift_fst, Category.assoc, ← h₁, Category.assoc, pullback.lift_fst]
      · rw [IsPullback.lift_snd, Category.assoc]
        exact h₂
    · rw [pullback.lift_snd]
      apply hY.hom_ext
      · rw [IsPullback.lift_fst, Category.assoc, ← h₁, Category.assoc, pullback.lift_snd]
      · rw [IsPullback.lift_snd, Category.assoc, ← pullback.condition]
        exact h₂

end ProdPO31

theorem solution
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))

    {X X' X'' XZ : Scheme.{0}}
    (fX : X ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) [Flat fX]
    (fX' : X' ⟶ Spec (CommRingCat.of B')) (fX'' : X'' ⟶ Spec (CommRingCat.of B'')) (fXZ : XZ ⟶ Spec (CommRingCat.of B))
    (hX' : XZ ⟶ X') (cXh' : IsPullback hX' fXZ fX' (Spec.map (CommRingCat.ofHom φ')))
    (hX'' : XZ ⟶ X'') (cXh'' : IsPullback hX'' fXZ fX'' (Spec.map (CommRingCat.ofHom φ'')))
    (kX' : X' ⟶ X) (cXk' : IsPullback kX' fX' fX (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))))
    (kX'' : X'' ⟶ X) (cXk'' : IsPullback kX'' fX'' fX (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))))
    (poX : IsPushout hX' hX'' kX' kX'')

    {Y Y' Y'' YZ : Scheme.{0}}
    (fY : Y ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) [Flat fY]
    (fY' : Y' ⟶ Spec (CommRingCat.of B')) (fY'' : Y'' ⟶ Spec (CommRingCat.of B'')) (fYZ : YZ ⟶ Spec (CommRingCat.of B))
    (hY' : YZ ⟶ Y') (cYh' : IsPullback hY' fYZ fY' (Spec.map (CommRingCat.ofHom φ')))
    (hY'' : YZ ⟶ Y'') (cYh'' : IsPullback hY'' fYZ fY'' (Spec.map (CommRingCat.ofHom φ'')))
    (kY' : Y' ⟶ Y) (cYk' : IsPullback kY' fY' fY (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))))
    (kY'' : Y'' ⟶ Y) (cYk'' : IsPullback kY'' fY'' fY (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))))
    (poY : IsPushout hY' hY'' kY' kY'') :
    IsPushout
      (pullback.map fXZ fYZ fX' fY' hX' hY' (Spec.map (CommRingCat.ofHom φ')) cXh'.w.symm cYh'.w.symm)
      (pullback.map fXZ fYZ fX'' fY'' hX'' hY'' (Spec.map (CommRingCat.ofHom φ'')) cXh''.w.symm cYh''.w.symm)
      (pullback.map fX' fY' fX fY kX' kY' (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) cXk'.w.symm cYk'.w.symm)
      (pullback.map fX'' fY'' fX fY kX'' kY'' (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) cXk''.w.symm cYk''.w.symm) ∧
    IsPullback (pullback.map fX' fY' fX fY kX' kY' (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) cXk'.w.symm cYk'.w.symm)
      (pullback.fst fX' fY' ≫ fX') (pullback.fst fX fY ≫ fX) (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ∧
    IsPullback (pullback.map fX'' fY'' fX fY kX'' kY'' (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) cXk''.w.symm cYk''.w.symm)
      (pullback.fst fX'' fY'' ≫ fX'') (pullback.fst fX fY ≫ fX) (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) := by

  have bc' := ProdPO31.isPullback_pullbackMap fX fY fX' fY' _ kX' kY' cXk' cYk'
  have bc'' := ProdPO31.isPullback_pullbackMap fX fY fX'' fY'' _ kX'' kY'' cXk'' cYk''
  have bcZ' := ProdPO31.isPullback_pullbackMap fX' fY' fXZ fYZ _ hX' hY' cXh' cYh'
  have bcZ'' := ProdPO31.isPullback_pullbackMap fX'' fY'' fXZ fYZ _ hX'' hY'' cXh'' cYh''
  refine ⟨?_, bc', bc''⟩

  haveI : Flat (pullback.fst fX fY ≫ fX) := inferInstance
  refine AlgebraicGeometry.isPushout_of_flat_of_isPullback_specMap_pullbackFst_pullbackSnd φ' φ'' hφ's hφ''s hφ'n hφ''n
    (pullback.fst fX fY ≫ fX) (pullback.fst fX' fY' ≫ fX') (pullback.fst fX'' fY'' ≫ fX'') (pullback.fst fXZ fYZ ≫ fXZ)
    _ bc' _ bc'' _ bcZ' _ bcZ'' ?_

  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, poX.w]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, poY.w]

end S_AlgebraicGeometry_isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_isPushout_pullbackMap_of_isPushout_of_isPushout_of_flat (solution)
