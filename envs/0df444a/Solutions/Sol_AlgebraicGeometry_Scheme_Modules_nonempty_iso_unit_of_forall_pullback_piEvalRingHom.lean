-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_forall_pullback_piEvalRingHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e96df039-ad58-56c6-94a0-102b2f505242

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_piEvalRingHom
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace BenchQDT

theorem subsingleton_sections_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (B : Y.Modules) (U : Y.Opens) :
    Subsingleton (B.val.obj (Opposite.op U)) := by
  have hU : U = ⊥ := by ext x; exact (IsEmpty.false x).elim
  subst hU
  let F : TopCat.Sheaf AddCommGrpCat Y.carrier := ⟨B.val.presheaf, B.isSheaf⟩
  have hT : IsTerminal (F.obj.obj (Opposite.op ⊥)) := TopCat.Sheaf.isTerminalOfEmpty F
  have h10 : (𝟙 (F.obj.obj (Opposite.op ⊥))) = 0 := hT.hom_ext _ _
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have := congrArg (fun φ => (φ : F.obj.obj (Opposite.op ⊥) ⟶ _).hom a) h10
    simp at this
    exact this
  have hb : b = 0 := by
    have := congrArg (fun φ => (φ : F.obj.obj (Opposite.op ⊥) ⟶ _).hom b) h10
    simp at this
    exact this
  exact ha.trans hb.symm

theorem hom_eq_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] {A B : Y.Modules} (f g : A ⟶ B) : f = g := by
  ext U x
  exact (subsingleton_sections_of_isEmpty B U).elim _ _

theorem iso_eq_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] {A B : Y.Modules} (f g : A ≅ B) : f = g :=
  Iso.ext (hom_eq_of_isEmpty _ _)

theorem pullbackComp_id_app {X : Scheme.{u}} (V : X.Opens) (M : X.Modules) (hg : 𝟙 _ ≫ V.ι = V.ι) :
    (Scheme.Modules.pullbackComp (𝟙 _) V.ι).app M ≪≫ (Scheme.Modules.pullbackCongr hg).app M =
      (Scheme.Modules.pullbackId _).app ((Scheme.Modules.pullback V.ι).obj M) := by
  ext : 1
  have h := Scheme.Modules.pseudofunctor_right_unitality (V.ι)

  have h' := congrArg (fun t => (Scheme.Modules.pullbackComp (𝟙 _) V.ι).hom ≫ t) h
  simp only [Iso.hom_inv_id_assoc] at h'
  have h'' := NatTrans.congr_app h' M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at h''
  simp only [Iso.trans_hom, Iso.app_hom, Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]
  erw [Category.comp_id] at h''
  exact h''.symm

theorem key {X : Scheme.{u}} (V : X.Opens) (M M' : X.Modules) (g : (V : Scheme.{u}) ⟶ V)
    (hg : g ≫ V.ι = V.ι) (hg1 : g = 𝟙 _)
    (e : (Scheme.Modules.pullback V.ι).obj M ≅ (Scheme.Modules.pullback V.ι).obj M') :
    (Scheme.Modules.pullback g).mapIso e =
      ((Scheme.Modules.pullbackComp g V.ι).app M ≪≫ (Scheme.Modules.pullbackCongr hg).app M) ≪≫ e ≪≫
        ((Scheme.Modules.pullbackComp g V.ι).app M' ≪≫ (Scheme.Modules.pullbackCongr hg).app M').symm := by
  subst hg1
  rw [pullbackComp_id_app, pullbackComp_id_app]
  ext : 1
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  have nat := (Scheme.Modules.pullbackId (V : Scheme.{u})).hom.naturality e.hom

  rw [Functor.id_map] at nat
  calc (Scheme.Modules.pullback (𝟙 (V : Scheme.{u}))).map e.hom
      = ((Scheme.Modules.pullback (𝟙 (V : Scheme.{u}))).map e.hom ≫
          (Scheme.Modules.pullbackId (V : Scheme.{u})).hom.app ((Scheme.Modules.pullback V.ι).obj M')) ≫
          (Scheme.Modules.pullbackId (V : Scheme.{u})).inv.app ((Scheme.Modules.pullback V.ι).obj M') := by
        rw [Category.assoc, Iso.hom_inv_id_app]; erw [Category.comp_id]
    _ = ((Scheme.Modules.pullbackId (V : Scheme.{u})).hom.app ((Scheme.Modules.pullback V.ι).obj M) ≫ e.hom) ≫
          (Scheme.Modules.pullbackId (V : Scheme.{u})).inv.app ((Scheme.Modules.pullback V.ι).obj M') := by
        rw [nat]
    _ = _ := by rw [Category.assoc]

theorem main {k : ℕ} (R : Fin k → Type u) [∀ i, CommRing (R i)]
    (N : (Spec (CommRingCat.of (∀ i, R i))).Modules)
    (h : ∀ i, Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)))).obj N ≅
      SheafOfModules.unit (Spec (CommRingCat.of (R i))).ringCatSheaf)) :
    Nonempty (N ≅ SheafOfModules.unit (Spec (CommRingCat.of (∀ i, R i))).ringCatSheaf) := by
  classical
  let X : Scheme.{u} := Spec (CommRingCat.of (∀ i, R i))
  let j : ∀ i, Spec (CommRingCat.of (R i)) ⟶ X := fun i => Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i))
  haveI : ∀ i, IsOpenImmersion (j i) := fun i => inferInstance

  let ε : ∀ i : Fin k, (∀ i', R i') := fun i => Pi.single i 1
  let U : Fin k → X.Opens := fun i => PrimeSpectrum.basicOpen (ε i)

  have hrange : ∀ i, Set.range (j i).base = (U i : Set X) := by
    intro i
    letI := (Pi.evalRingHom R i).toAlgebra
    have : IsLocalization.Away (ε i) (R i) := by
      apply IsLocalization.away_of_isIdempotentElem_of_mul
      · ext i'; by_cases hi : i' = i
        · subst hi; simp [ε]
        · simp [ε, hi]
      · intro x y
        constructor
        · intro hxy; ext i'; by_cases hi : i' = i
          · subst hi; (simp [ε] at hxy ⊢; exact hxy)
          · simp [ε, hi]
        · intro hxy; (have h__af := congr_fun hxy i; simp [ε] at h__af; exact h__af)
      · exact Function.surjective_eval _
    exact PrimeSpectrum.localization_away_comap_range (R i) (ε i)

  have hU : ⨆ i, U i = ⊤ := by
    show (⨆ i, PrimeSpectrum.basicOpen (ε i) : TopologicalSpace.Opens (PrimeSpectrum (∀ i, R i))) = ⊤
    rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff, Ideal.eq_top_iff_one]
    have h1 : (1 : ∀ i, R i) = ∑ i, ε i := (Finset.univ_sum_single (1 : ∀ i, R i)).symm
    rw [h1]
    exact Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨i, rfl⟩

  have hdisj : ∀ i i', i ≠ i' → U i ⊓ U i' = ⊥ := by
    intro i i' hii
    show PrimeSpectrum.basicOpen (ε i) ⊓ PrimeSpectrum.basicOpen (ε i') = ⊥
    rw [← PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_eq_bot_iff]
    refine ⟨1, ?_⟩
    rw [pow_one]
    ext i''
    by_cases h1 : i'' = i
    · subst h1; simp [ε, Ne.symm hii]
    · simp [ε, h1]
  have hB : ∀ i i', U i ⊓ U i' ≤ ⨆ (m : {m : Fin k // U m ≤ U i ⊓ U i'}), U m.1 := by
    intro i i'
    by_cases hii : i = i'
    · exact le_iSup_of_le (f := fun m : {m : Fin k // U m ≤ U i ⊓ U i'} => U m.1)
        ⟨i, le_inf le_rfl (le_of_eq (congrArg U hii))⟩ inf_le_left
    · rw [hdisj i i' hii]; exact bot_le

  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj N ≅ (Scheme.Modules.pullback (U i).ι).obj O := by
    intro i
    let iso : Spec (CommRingCat.of (R i)) ≅ (U i : Scheme.{u}) :=
      IsOpenImmersion.isoOfRangeEq (j i) (U i).ι (by rw [Scheme.Opens.range_ι]; exact hrange i)
    have hfac : iso.inv ≫ j i = (U i).ι := by
      rw [Iso.inv_comp_eq]; exact (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm
    exact (Scheme.Modules.pullbackCongr hfac.symm).app N ≪≫ ((Scheme.Modules.pullbackComp iso.inv (j i)).app N).symm ≪≫
      (Scheme.Modules.pullback iso.inv).mapIso (h i).some ≪≫ Scheme.Modules.pullbackUnitIso iso.inv ≪≫
      (Scheme.Modules.pullbackUnitIso (U i).ι).symm
  have he : ∀ (i i' : Fin k) (hle : U i' ≤ U i),
      (Scheme.Modules.pullback (X.homOfLE hle)).mapIso (e i) =
        ((Scheme.Modules.pullbackComp (X.homOfLE hle) (U i).ι).app N ≪≫
            (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle)).app N) ≪≫
          e i' ≪≫
          ((Scheme.Modules.pullbackComp (X.homOfLE hle) (U i).ι).app O ≪≫
            (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle)).app O).symm := by
    intro i i' hle
    by_cases hii : i' = i
    · subst hii
      exact key (U _) N O (X.homOfLE hle) (X.homOfLE_ι hle) (Scheme.homOfLE_rfl _ _) (e _)
    · have hbot : U i' = ⊥ := by
        rw [← inf_eq_right.mpr hle]
        exact hdisj i i' (Ne.symm hii)
      have hno : ∀ y : X, y ∈ U i' → False := fun y hy => by rw [hbot] at hy; exact hy
      haveI : IsEmpty (U i' : Scheme.{u}) := ⟨fun x => hno x.1 x.2⟩
      exact iso_eq_of_isEmpty _ _
  obtain ⟨f, -⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_iso_forall_pullback_mapIso_eq_of_iSup_eq_top
    N O U hU hB e he
  exact ⟨f⟩

end BenchQDT

theorem solution
    {k : ℕ} (R : Fin k → Type u) [∀ i, CommRing (R i)]
    (N : (Spec (CommRingCat.of (∀ i, R i))).Modules)
    (h : ∀ i, Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)))).obj N ≅
      SheafOfModules.unit (Spec (CommRingCat.of (R i))).ringCatSheaf)) :
    Nonempty (N ≅ SheafOfModules.unit (Spec (CommRingCat.of (∀ i, R i))).ringCatSheaf) :=
  BenchQDT.main R N h

end S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_piEvalRingHom
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_piEvalRingHom (solution)
