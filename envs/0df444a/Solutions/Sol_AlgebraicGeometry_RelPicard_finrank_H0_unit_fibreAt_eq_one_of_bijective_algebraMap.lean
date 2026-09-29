-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/32ee5499-ffe8-5216-a357-aaa33828d03d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard"

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hH0 : letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd c x) ⊤
      Function.Bijective (algebraMap k Γ(pullback c x, ⊤)))
    (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
      (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H0 = 1 := by
  classical

  let Y : Scheme.{u} := pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x
  let y : Y ⟶ Spec (CommRingCat.of k) := fibreAt c (𝟙 _) x
  have hy : y = pullback.snd (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x := rfl

  obtain ⟨ψ, hψ⟩ : ∃ ψ : Y ≅ pullback c x, ψ.hom ≫ pullback.snd c x = y := by
    refine ⟨asIso (pullback.map (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x c x
      (pullback.fst c (𝟙 (Spec (CommRingCat.of R)))) (𝟙 _) (𝟙 _)
      (by simpa using (pullback.condition (f := c) (g := 𝟙 (Spec (CommRingCat.of R)))).symm) (by simp)), ?_⟩
    rw [hy, asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id]

  letI : Algebra k Γ(Y, ⊤) := Scheme.TwoAffineOpenCover.algebraOfHom y ⊤
  letI : Module k Γ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules), ⊤) :=
    Scheme.TwoAffineOpenCover.moduleSectionsOfHom y (SheafOfModules.unit Y.ringCatSheaf) ⊤
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒲 y
    (SheafOfModules.unit Y.ringCatSheaf)
  rw [← e.finrank_eq]

  have happ : ∀ {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of k)), f.appLE ⊤ ⊤ le_top = f.appTop := by
    intro Z f
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have hbij : Function.Bijective (algebraMap k Γ(Y, ⊤)) := by
    letI : Algebra k Γ(pullback c x, ⊤) := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd c x) ⊤
    have hfac : (algebraMap k Γ(Y, ⊤) : k → Γ(Y, ⊤)) = (ψ.hom.appTop).hom ∘ (algebraMap k Γ(pullback c x, ⊤)) := by
      funext r
      change (y.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r) =
        (ψ.hom.appTop).hom (((pullback.snd c x).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r))
      rw [happ, happ, ← hψ]
      rfl
    rw [hfac]
    exact (ConcreteCategory.bijective_of_isIso (ψ.hom.app ⊤)).comp hH0

  let f : k →ₗ[k] Γ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules), ⊤) :=
    { toFun := fun r => (algebraMap k Γ(Y, ⊤) r : Γ(Y, ⊤))
      map_add' := fun a b => by
        change algebraMap k Γ(Y, ⊤) (a + b) = algebraMap k Γ(Y, ⊤) a + algebraMap k Γ(Y, ⊤) b
        exact map_add _ a b
      map_smul' := fun a b => by
        change algebraMap k Γ(Y, ⊤) (a * b) = algebraMap k Γ(Y, ⊤) a * algebraMap k Γ(Y, ⊤) b
        exact map_mul _ a b }
  have hf : Function.Bijective f := hbij
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_self]

end S_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap (solution)
