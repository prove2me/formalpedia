-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_FilteredHomology
-- name    : GroundTheory_ProfiniteCohomology_FilteredHomology
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:36.517837+00:00
-- url     : https://prove2.me/theorems/85b965c8-2008-4643-84c8-3e124d07e5bb
-- title:
--   Filtered Homology
-- statement:
--   Definitions and structural lemmas for Filtered Homology, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/FilteredHomology.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory Limits
universe u
section Elements
variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{u} R) c)
theorem exists_iCycles_eq {i : ι} (x : K.X i) (hx : (K.d i (c.next i)).hom x = 0) :
    ∃ z : K.cycles i, (K.iCycles i).hom z = x := by
  refine ⟨(K.sc i).moduleCatCyclesIso.inv ⟨x, hx⟩, ?_⟩
  have := ShortComplex.moduleCatCyclesIso_inv_iCycles_apply (K.sc i) ⟨x, hx⟩
  exact this
theorem shortComplex_homologyπ_eq_zero_iff (S : ShortComplex (ModuleCat.{u} R)) (z : S.cycles) :
    S.homologyπ.hom z = 0 ↔ ∃ w : S.X₁, S.f.hom w = S.iCycles.hom z := by
  have hinj : Function.Injective S.moduleCatHomologyIso.hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have h1 : S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom z) =
      S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom.hom z) :=
    ShortComplex.π_moduleCatCyclesIso_hom_apply S z
  have h2 : S.moduleCatLeftHomologyData.i.hom (S.moduleCatCyclesIso.hom.hom z) =
      S.iCycles.hom z :=
    ShortComplex.moduleCatCyclesIso_hom_i_apply S z
  have h0 : S.homologyπ.hom z = 0 ↔ S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom z) = 0 :=
    ⟨fun h => by rw [h, map_zero], fun h => hinj (h.trans (map_zero _).symm)⟩
  rw [h0, h1]
  change Submodule.Quotient.mk (p := LinearMap.range S.moduleCatToCycles)
    (S.moduleCatCyclesIso.hom.hom z) = 0 ↔ _
  refine (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)
    (x := (S.moduleCatCyclesIso.hom.hom z : LinearMap.ker S.g.hom))).trans ?_
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (congrArg S.moduleCatLeftHomologyData.i.hom hw).trans h2⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (ModuleCat.mono_iff_injective S.moduleCatLeftHomologyData.i).1 inferInstance
      (hw.trans h2.symm)⟩
theorem homologyπ_eq_zero_iff {i : ι} (z : K.cycles i) :
    (K.homologyπ i).hom z = 0 ↔
      ∃ w : K.X (c.prev i), (K.d (c.prev i) i).hom w = (K.iCycles i).hom z :=
  shortComplex_homologyπ_eq_zero_iff (K.sc i) z
end Elements
section Apply
variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{u} R) c}
theorem hom_f_d_apply (φ : K ⟶ L) (i j : ι) (x : K.X i) :
    (φ.f j).hom ((K.d i j).hom x) = (L.d i j).hom ((φ.f i).hom x) :=
  (congrArg (fun g => ModuleCat.Hom.hom g x) (φ.comm i j)).symm
theorem iCycles_d_apply (K : HomologicalComplex (ModuleCat.{u} R) c) (i j : ι) (z : K.cycles i) :
    (K.d i j).hom ((K.iCycles i).hom z) = 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.iCycles_d, ModuleCat.hom_zero,
    LinearMap.zero_apply]
theorem iCycles_cyclesMap_apply (φ : K ⟶ L) (i : ι) (z : K.cycles i) :
    (L.iCycles i).hom ((HomologicalComplex.cyclesMap φ i).hom z) =
      (φ.f i).hom ((K.iCycles i).hom z) :=
  congrArg (fun g => ModuleCat.Hom.hom g z) (HomologicalComplex.cyclesMap_i φ i)
theorem homologyMap_homologyπ_apply (φ : K ⟶ L) (i : ι) (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i).hom ((K.homologyπ i).hom z) =
      (L.homologyπ i).hom ((HomologicalComplex.cyclesMap φ i).hom z) :=
by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.homologyπ_naturality]
  rfl
end Apply
section Filtered
variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {J : Type u} [SmallCategory J] [IsFiltered J]
  {F : J ⥤ HomologicalComplex (ModuleCat.{u} R) c} (t : Cocone F)
omit [IsFiltered J] in
theorem cocone_w_apply {j j' : J} (f : j ⟶ j') (i : ι) (y : (F.obj j).X i) :
    ((t.ι.app j').f i).hom (((F.map f).f i).hom y) = ((t.ι.app j).f i).hom y :=
  congrArg (fun φ : F.obj j ⟶ t.pt => (φ.f i).hom y) (t.w f)
omit [IsFiltered J] in

theorem exists_homologyMap_eq_of_cocone (i : ι)
    (hsurj : ∀ x : t.pt.X i, ∃ (j : J) (y : (F.obj j).X i), ((t.ι.app j).f i).hom y = x)
    (hinj : ∀ (j : J) (y : (F.obj j).X (c.next i)), ((t.ι.app j).f (c.next i)).hom y = 0 →
      ∃ (j' : J) (f : j ⟶ j'), ((F.map f).f (c.next i)).hom y = 0)
    (z : t.pt.homology i) :
    ∃ (j : J) (y : (F.obj j).homology i),
      (HomologicalComplex.homologyMap (t.ι.app j) i).hom y = z := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (t.pt.homologyπ i)).1 inferInstance z
  obtain ⟨j, y, hy⟩ := hsurj ((t.pt.iCycles i).hom z)
  have hdy : ((t.ι.app j).f (c.next i)).hom (((F.obj j).d i (c.next i)).hom y) = 0 := by
    rw [hom_f_d_apply, hy]
    exact iCycles_d_apply t.pt i _ z
  obtain ⟨j', f, hf⟩ := hinj j _ hdy
  rw [hom_f_d_apply] at hf
  obtain ⟨z', hz'⟩ := exists_iCycles_eq (F.obj j') (((F.map f).f i).hom y) hf
  refine ⟨j', (HomologicalComplex.homologyπ (F.obj j') i).hom z', ?_⟩
  rw [homologyMap_homologyπ_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (t.pt.iCycles i)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hz', cocone_w_apply, hy]
theorem exists_homologyMap_map_eq_zero_of_cocone (i : ι)
    (hsurj : ∀ x : t.pt.X (c.prev i),
      ∃ (j : J) (y : (F.obj j).X (c.prev i)), ((t.ι.app j).f (c.prev i)).hom y = x)
    (hinj : ∀ (j : J) (y : (F.obj j).X i), ((t.ι.app j).f i).hom y = 0 →
      ∃ (j' : J) (f : j ⟶ j'), ((F.map f).f i).hom y = 0)
    (j : J) (y : (F.obj j).homology i)
    (hy : (HomologicalComplex.homologyMap (t.ι.app j) i).hom y = 0) :
    ∃ (j' : J) (f : j ⟶ j'), (HomologicalComplex.homologyMap (F.map f) i).hom y = 0 := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((F.obj j).homologyπ i)).1 inferInstance y
  rw [homologyMap_homologyπ_apply, homologyπ_eq_zero_iff, iCycles_cyclesMap_apply] at hy
  obtain ⟨w, hw⟩ := hy
  obtain ⟨j₁, v, hv⟩ := hsurj w
  let m := IsFiltered.max j j₁
  let a : j ⟶ m := IsFiltered.leftToMax j j₁
  let b : j₁ ⟶ m := IsFiltered.rightToMax j j₁
  let e : (F.obj m).X i := ((F.map a).f i).hom (((F.obj j).iCycles i).hom z) -
    ((F.obj m).d (c.prev i) i).hom (((F.map b).f (c.prev i)).hom v)
  have he : ((t.ι.app m).f i).hom e = 0 := by
    simp only [e, map_sub]
    rw [cocone_w_apply, hom_f_d_apply, cocone_w_apply, hv]
    exact sub_eq_zero.2 hw.symm
  obtain ⟨j', g, hg⟩ := hinj m e he
  refine ⟨j', a ≫ g, ?_⟩
  rw [homologyMap_homologyπ_apply, homologyπ_eq_zero_iff, iCycles_cyclesMap_apply]
  refine ⟨((F.map (b ≫ g)).f (c.prev i)).hom v, ?_⟩
  simp only [e, map_sub, sub_eq_zero] at hg
  rw [F.map_comp, F.map_comp, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← hom_f_d_apply]
  exact hg.symm
noncomputable def isColimitHomologyMapCocone (i : ι)
    (hsurj : ∀ (n : ι) (x : t.pt.X n),
      ∃ (j : J) (y : (F.obj j).X n), ((t.ι.app j).f n).hom y = x)
    (hinj : ∀ (n : ι) (j : J) (y : (F.obj j).X n), ((t.ι.app j).f n).hom y = 0 →
      ∃ (j' : J) (f : j ⟶ j'), ((F.map f).f n).hom y = 0) :
    IsColimit ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c i).mapCocone t) :=
  isColimitOfReflects (forget (ModuleCat.{u} R)) <|
    Types.FilteredColimit.isColimitOf' _ _
      (fun z => by
        obtain ⟨j, y, hy⟩ := exists_homologyMap_eq_of_cocone t i (hsurj i) (hinj (c.next i)) z
        exact ⟨j, y, hy.symm⟩)
      (fun j (x y : (F.obj j).homology i) hxy => by
        have hxy' : (HomologicalComplex.homologyMap (t.ι.app j) i).hom x =
            (HomologicalComplex.homologyMap (t.ι.app j) i).hom y := hxy
        obtain ⟨j', f, h⟩ := exists_homologyMap_map_eq_zero_of_cocone t i (hsurj (c.prev i))
          (hinj i) j (x - y) (by rw [map_sub, hxy', sub_self])
        have h' : (HomologicalComplex.homologyMap (F.map f) i).hom x =
            (HomologicalComplex.homologyMap (F.map f) i).hom y := by
          rw [← sub_eq_zero, ← map_sub]
          exact h
        exact ⟨j', f, h'⟩)
end Filtered
end GroundTheory.ProfCoh


