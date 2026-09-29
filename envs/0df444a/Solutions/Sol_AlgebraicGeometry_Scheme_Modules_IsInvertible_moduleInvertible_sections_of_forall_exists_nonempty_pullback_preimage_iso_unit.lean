-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.moduleInvertible_sections_of_forall_exists_nonempty_pullback_preimage_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/6cc12825-50d3-513a-91fb-db1f5ae874ea

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_Module_Invertible_of_isLocalizedModule_span
import Theorems.Thm_Module_Invertible_of_ringEquiv
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial_of_qcqs
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_moduleInvertible_sections_of_forall_exists_nonempty_pullback_preimage_iso_unit

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace H0Inv

variable {Y : Scheme.{u}} (P : Y.Modules)

theorem nonempty_linearEquiv_of_trivial (D : Y.Opens)
    (T : (Scheme.Modules.pullback D.ι).obj P ≅ SheafOfModules.unit (↑D : Scheme.{u}).ringCatSheaf) :
    Nonempty (Γ(P, D) ≃ₗ[Γ(Y, D)] Γ(Y, D)) := by

  have hη : Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction D.ι).unit.app P).app D) :=
    AlgebraicGeometry.Scheme.Modules.bijective_unit_app_of_le_opensRange D.ι P D
      (by rw [Scheme.Opens.opensRange_ι])
  have hT : Function.Bijective (T.hom.app (D.ι ⁻¹ᵁ D)) := ConcreteCategory.bijective_of_isIso _
  have hE : D.ι ''ᵁ (D.ι ⁻¹ᵁ D) = D := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_idem]
  have hε : Function.Bijective (Y.presheaf.map (eqToHom hE.symm).op) := ConcreteCategory.bijective_of_isIso _

  let η' : Γ(P, D) → Γ((Scheme.Modules.pullback D.ι).obj P, D.ι ⁻¹ᵁ D) :=
    fun m => ((Scheme.Modules.pullbackPushforwardAdjunction D.ι).unit.app P).app D m
  let T' : Γ((Scheme.Modules.pullback D.ι).obj P, D.ι ⁻¹ᵁ D) → Γ(Y, D.ι ''ᵁ (D.ι ⁻¹ᵁ D)) :=
    fun y => T.hom.app (D.ι ⁻¹ᵁ D) y
  let ε' : Γ(Y, D.ι ''ᵁ (D.ι ⁻¹ᵁ D)) → Γ(Y, D) := fun z => Y.presheaf.map (eqToHom hE.symm).op z
  have hβ : Function.Bijective (ε' ∘ T' ∘ η') := hε.comp (hT.comp hη)

  have hεapp : ∀ a : Γ(Y, D), ε' (D.ι.app D a) = a := by
    intro a
    change (Y.presheaf.map (homOfLE (x := D.ι ''ᵁ D.ι ⁻¹ᵁ D) (Set.image_preimage_subset _ _)).op ≫
      Y.presheaf.map (eqToHom hE.symm).op) a = a
    rw [← Functor.map_comp, ← op_comp,
      Subsingleton.elim (eqToHom hE.symm ≫ homOfLE (Set.image_preimage_subset _ _)) (𝟙 D), op_id,
      CategoryTheory.Functor.map_id]
    rfl

  have hadd : ∀ a b, (ε' ∘ T' ∘ η') (a + b) = (ε' ∘ T' ∘ η') a + (ε' ∘ T' ∘ η') b := fun a b => by
    simp only [Function.comp_apply]
    have e1 : η' (a + b) = η' a + η' b :=
      map_add (ConcreteCategory.hom (((Scheme.Modules.pullbackPushforwardAdjunction D.ι).unit.app P).app D)) a b
    have e2 : T' (η' a + η' b) = T' (η' a) + T' (η' b) :=
      map_add (ConcreteCategory.hom (T.hom.app (D.ι ⁻¹ᵁ D))) (η' a) (η' b)
    have e3 : ∀ p q : Γ(Y, D.ι ''ᵁ (D.ι ⁻¹ᵁ D)), ε' (p + q) = ε' p + ε' q :=
      fun p q => map_add (ConcreteCategory.hom (Y.presheaf.map (eqToHom hE.symm).op)) p q
    rw [e1, e2, e3]
  have hsmul : ∀ (a : Γ(Y, D)) (m : Γ(P, D)), (ε' ∘ T' ∘ η') (a • m) = a * (ε' ∘ T' ∘ η') m := fun a m => by
    simp only [Function.comp_apply]
    have h1 : η' (a • m) = (D.ι.app D a) • η' m :=
      Scheme.Modules.Hom.app_smul ((Scheme.Modules.pullbackPushforwardAdjunction D.ι).unit.app P) a m
    have h2 : T.hom.app (D.ι ⁻¹ᵁ D) ((D.ι.app D a) • η' m) = (D.ι.app D a) • T.hom.app (D.ι ⁻¹ᵁ D) (η' m) :=
      Scheme.Modules.Hom.app_smul T.hom (D.ι.app D a) (η' m)
    rw [h1]
    change ε' (T.hom.app (D.ι ⁻¹ᵁ D) ((D.ι.app D a) • η' m)) = _
    rw [h2]
    obtain ⟨a', ha'⟩ : ∃ a' : Γ(Y, D.ι ''ᵁ (D.ι ⁻¹ᵁ D)), a' = D.ι.app D a := ⟨_, rfl⟩
    have hε' : ε' a' = a := by rw [ha']; exact hεapp a
    rw [← ha']
    change (ConcreteCategory.hom (Y.presheaf.map (eqToHom hE.symm).op)) (a' * T' (η' m)) = a * ε' (T' (η' m))
    rw [map_mul]
    change ε' a' * ε' (T' (η' m)) = a * ε' (T' (η' m))
    rw [hε']
  let β : Γ(P, D) →ₗ[Γ(Y, D)] Γ(Y, D) :=
    { toFun := ε' ∘ T' ∘ η'
      map_add' := hadd
      map_smul' := fun a m => by rw [RingHom.id_apply]; exact hsmul a m }
  exact ⟨LinearEquiv.ofBijective β hβ⟩

end H0Inv

theorem solution
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (h : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact h] [QuasiSeparated h]
    (hΓ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop).hom)
    (P : Y.Modules) (hP : Scheme.Modules.IsInvertible P)
    (hloc : ∀ y : ↥(Spec (CommRingCat.of R)), ∃ U : (Spec (CommRingCat.of R)).Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (h ⁻¹ᵁ U).ι).obj P ≅ SheafOfModules.unit (↑(h ⁻¹ᵁ U) : Scheme.{u}).ringCatSheaf)) :
    letI : Algebra R Γ(Y, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop).hom.toAlgebra
    letI : Module R Γ(P, ⊤) := Module.compHom _ (algebraMap R Γ(Y, ⊤))
    Module.Invertible R Γ(P, ⊤) := by
  letI algA : Algebra R Γ(Y, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop).hom.toAlgebra
  letI modP : Module R Γ(P, ⊤) := Module.compHom _ (algebraMap R Γ(Y, ⊤))
  show Module.Invertible R Γ(P, ⊤)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h
  haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated h
  have htop : IsCompact ((⊤ : Y.Opens) : Set Y) := by simpa using isCompact_univ
  have htop' : IsQuasiSeparated ((⊤ : Y.Opens) : Set Y) := by simpa using isQuasiSeparated_univ

  let good : Set Γ(Y, ⊤) := {f | Nonempty ((Scheme.Modules.pullback (Y.basicOpen f).ι).obj P ≅
      SheafOfModules.unit (↑(Y.basicOpen f) : Scheme.{u}).ringCatSheaf)}
  have hspan : Ideal.span good = ⊤ := by
    let s : Set R := {v | algebraMap R Γ(Y, ⊤) v ∈ good}
    have hs : Ideal.span s = ⊤ := by
      rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
      refine top_le_iff.mp fun y _ => ?_
      obtain ⟨U, hyU, ⟨eU⟩⟩ := hloc y
      obtain ⟨_, ⟨v, rfl⟩, hyv, hvU⟩ :=
        (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hyU U.isOpen
      have hpre : h ⁻¹ᵁ (PrimeSpectrum.basicOpen v) = Y.basicOpen (algebraMap R Γ(Y, ⊤) v) := by
        have e1 := basicOpen_eq_of_affine (R := CommRingCat.of R) v
        have e2 := Scheme.preimage_basicOpen_top h ((Scheme.ΓSpecIso (CommRingCat.of R)).inv v)
        rw [e1] at e2
        exact e2
      have hle : h ⁻¹ᵁ (PrimeSpectrum.basicOpen v) ≤ h ⁻¹ᵁ U := fun x hx => hvU hx
      have hv : v ∈ s := by
        change Nonempty _
        rw [← hpre]
        exact ⟨(Scheme.Modules.pullbackCongr (Scheme.homOfLE_ι Y hle).symm).app P ≪≫
          ((Scheme.Modules.pullbackComp (Y.homOfLE hle) (h ⁻¹ᵁ U).ι).app P).symm ≪≫
          (Scheme.Modules.pullback (Y.homOfLE hle)).mapIso eU ≪≫
          Scheme.Modules.pullbackUnitIso (Y.homOfLE hle)⟩
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨v, TopologicalSpace.Opens.mem_iSup.mpr ⟨hv, hyv⟩⟩
    have hmap : Ideal.map (algebraMap R Γ(Y, ⊤)) (Ideal.span s) ≤ Ideal.span good := by
      rw [Ideal.map_span]
      apply Ideal.span_mono
      rintro _ ⟨v, hv, rfl⟩
      exact hv
    rw [hs, Ideal.map_top] at hmap
    exact top_le_iff.mp hmap

  haveI : ∀ f : ↥good, IsLocalization.Away (f.1 : Γ(Y, ⊤)) Γ(Y, Y.basicOpen f.1) :=
    fun f => isLocalization_basicOpen_of_qcqs htop htop' f.1
  letI modloc : ∀ f : ↥good, Module Γ(Y, ⊤) Γ(P, Y.basicOpen f.1) :=
    fun f => Module.compHom _ (algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen f.1))
  haveI : ∀ f : ↥good, IsScalarTower Γ(Y, ⊤) Γ(Y, Y.basicOpen f.1) Γ(P, Y.basicOpen f.1) :=
    fun f => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let φ : ∀ f : ↥good, Γ(P, ⊤) →ₗ[Γ(Y, ⊤)] Γ(P, Y.basicOpen f.1) := fun f =>
    { toFun := fun m => P.presheaf.map (homOfLE (Y.basicOpen_le f.1)).op m
      map_add' := fun a b => map_add _ a b
      map_smul' := fun a m => by
        rw [RingHom.id_apply]
        exact Scheme.Modules.map_smul P (homOfLE (Y.basicOpen_le f.1)) a m }
  haveI : ∀ f : ↥good, IsLocalizedModule (Submonoid.powers (f.1 : Γ(Y, ⊤))) (φ f) := fun f => by
    obtain ⟨hsurj, hker⟩ :=
      AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial_of_qcqs P hP.1 htop htop' f.1
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, n, rfl⟩
      rw [Module.End.isUnit_iff]
      have hu : IsUnit ((Y.presheaf.map (homOfLE (Y.basicOpen_le f.1)).op f.1) ^ n) :=
        (RingedSpace.isUnit_res_basicOpen _ f.1).pow n
      have e : ⇑(algebraMap Γ(Y, ⊤) (Module.End Γ(Y, ⊤) Γ(P, Y.basicOpen f.1)) (f.1 ^ n)) =
          fun m => ((Y.presheaf.map (homOfLE (Y.basicOpen_le f.1)).op f.1) ^ n) • m := by
        funext m
        rw [Module.algebraMap_end_apply]
        change algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen f.1) (f.1 ^ n) • m = _
        rw [map_pow]
        rfl
      rw [e]
      exact hu.smul_bijective
    · intro x
      obtain ⟨n, y, hy⟩ := hsurj x
      exact ⟨(y, ⟨f.1 ^ n, n, rfl⟩), hy.symm⟩
    · intro x₁ x₂ he
      have h0 : P.presheaf.map (homOfLE (Y.basicOpen_le f.1)).op (x₁ - x₂) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr he
      obtain ⟨n, hn⟩ := hker _ h0
      refine ⟨⟨f.1 ^ n, n, rfl⟩, ?_⟩
      change (f.1 ^ n) • x₁ = (f.1 ^ n) • x₂
      rw [← sub_eq_zero, ← smul_sub]
      exact hn

  have H : ∀ f : ↥good, Module.Invertible Γ(Y, Y.basicOpen f.1) Γ(P, Y.basicOpen f.1) := fun f => by
    obtain ⟨T⟩ := f.2
    obtain ⟨e⟩ := H0Inv.nonempty_linearEquiv_of_trivial P _ T
    haveI : Module.Invertible Γ(Y, Y.basicOpen f.1) Γ(Y, Y.basicOpen f.1) := inferInstance
    exact Module.Invertible.congr e.symm

  haveI hA : Module.Invertible Γ(Y, ⊤) Γ(P, ⊤) :=
    Module.Invertible.of_isLocalizedModule_span good hspan (fun f => Γ(Y, Y.basicOpen f.1))
      (fun f => Γ(P, Y.basicOpen f.1)) φ H
  exact Module.Invertible.of_ringEquiv
    (RingEquiv.ofBijective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop).hom hΓ) Γ(P, ⊤) (fun r m => rfl)

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_moduleInvertible_sections_of_forall_exists_nonempty_pullback_preimage_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_moduleInvertible_sections_of_forall_exists_nonempty_pullback_preimage_iso_unit (solution)
