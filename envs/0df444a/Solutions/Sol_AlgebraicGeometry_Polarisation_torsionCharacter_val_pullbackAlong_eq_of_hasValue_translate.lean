-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.torsionCharacter_val_pullbackAlong_eq_of_hasValue_translate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/55fd34a1-ff67-5d29-9a20-d162ce1ce15c

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_TorsionCharacter
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_existsUnique_isBaseScalar_of_isInvertible_of_bijective
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_translate_comp_schemeNsmul_of_mem_torsionSubset
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_trans
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_pullback_mapIso_one
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_torsionCharacter_val_pullbackAlong_eq_of_hasValue_translate
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard AlgebraicGeometry.DescentCharacter"

namespace BCN22

open GoodReductionJacobian.RelativeGroupLaw

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem toBase_nsmul {Tr : Type} [CommRing Tr] (t : Spec (CommRingCat.of Tr) ⟶ Spec (CommRingCat.of S))
    {T' : Scheme.{0}} (t' : T' ⟶ Spec (CommRingCat.of Tr)) (n : ℕ) (P : SchemeHomOver t' (baseChangeStr t f)) :
    baseChangePointToBase t ((L.baseChange t).nsmul t' n P) = L.nsmul (t' ≫ t) n (baseChangePointToBase t P) := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, baseChangePointToBase_one]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, baseChangePointToBase_mul, ih]

theorem isTorsionPoint_ofBase {Tr : Type} [CommRing Tr] (t : Spec (CommRingCat.of Tr) ⟶ Spec (CommRingCat.of S))
    (n : ℕ) (x : SchemeHomOver t f) (hx : L.IsTorsionPoint t n x) :
    (L.baseChange t).IsTorsionPoint (𝟙 _) n
      (baseChangePointOfBase t (t' := 𝟙 (Spec (CommRingCat.of Tr))) ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) := by
  rw [isTorsionPoint_def]
  apply (baseChangePointEquiv t (𝟙 _)).injective
  show baseChangePointToBase t _ = baseChangePointToBase t _
  rw [toBase_nsmul, baseChangePointToBase_ofBase, baseChangePointToBase_one]
  have hx' := L.isTorsionPoint_schemeHomOverComp t (𝟙 _ ≫ t) (𝟙 _) rfl n hx
  have heq : schemeHomOverComp (𝟙 _) rfl x =
      (⟨x.1, by rw [Category.id_comp]; exact x.2⟩ : SchemeHomOver (𝟙 _ ≫ t) f) :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp])
  rw [← heq]
  exact hx'

theorem schemeNsmul_comp_pinned {Tr R : Type} [CommRing Tr] [CommRing R]
    (t : Spec (CommRingCat.of Tr) ⟶ Spec (CommRingCat.of S)) (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (k : Spec (CommRingCat.of Tr) ⟶ Spec (CommRingCat.of R))
    (a : pullback f t ⟶ pullback f ι) (ha₁ : a ≫ pullback.fst f ι = pullback.fst f t)
    (ha₂ : a ≫ pullback.snd f ι = pullback.snd f t ≫ k) (n : ℕ) :
    (L.baseChange t).schemeNsmul n ≫ a = a ≫ (L.baseChange ι).schemeNsmul n := by
  obtain ⟨h1t, h2t, -⟩ := baseChange_schemeNsmul_comp_fst_and_eq_pullback_map t L n
  obtain ⟨h1i, h2i, -⟩ := baseChange_schemeNsmul_comp_fst_and_eq_pullback_map ι L n
  apply pullback.hom_ext
  · rw [Category.assoc, ha₁, h1t, Category.assoc, h1i, ← Category.assoc, ha₁]
  · rw [Category.assoc, ha₂, ← Category.assoc, h2t, Category.assoc, h2i, ha₂]

theorem val_eq (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    {Tr : Type} [CommRing Tr] (t : Spec (CommRingCat.of Tr) ⟶ Spec (CommRingCat.of S))
    {R : Type} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (k : Spec (CommRingCat.of Tr) ⟶ Spec (CommRingCat.of R))
    (𝓝 : (pullback f ι).Modules)
    (hAdm : Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj 𝓝 ≅ 𝟙_ _))
    (a₁ a₂ : pullback f t ⟶ pullback f ι)
    (ha₁ : a₁ ≫ pullback.fst f ι = pullback.fst f t) (ha₁' : a₁ ≫ pullback.snd f ι = pullback.snd f t ≫ k)
    (ha₂ : a₂ ≫ pullback.fst f ι = pullback.fst f t) (ha₂' : a₂ ≫ pullback.snd f ι = pullback.snd f t ≫ k)
    (N₁ : (pullback f t).Modules) (e₁ : N₁ ≅ (Scheme.Modules.pullback a₁).obj 𝓝)
    (x : SchemeHomOver t f) (hx : L.IsTorsionPoint t 2 x) (v₁ v₂ : Tr)
    (P₁ : ∀ (hTq : (L.baseChange t).translate
          (baseChangePointOfBase t (t' := 𝟙 (Spec (CommRingCat.of Tr))) ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫
          (L.baseChange t).schemeNsmul 2 = (L.baseChange t).schemeNsmul 2)
        (β : (Scheme.Modules.pullback ((L.baseChange t).schemeNsmul 2)).obj N₁ ≅
          (Scheme.Modules.pullback ((L.baseChange t).schemeNsmul 2)).obj (𝟙_ _)),
        HasValue (pullback.snd f t) hTq β v₁)
    (P₂ : ∀ (hTq : (L.baseChange t).translate
          (baseChangePointOfBase t (t' := 𝟙 (Spec (CommRingCat.of Tr))) ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫
          (L.baseChange t).schemeNsmul 2 = (L.baseChange t).schemeNsmul 2)
        (β : (Scheme.Modules.pullback ((L.baseChange t).schemeNsmul 2)).obj ((Scheme.Modules.pullback a₂).obj 𝓝) ≅
          (Scheme.Modules.pullback ((L.baseChange t).schemeNsmul 2)).obj (𝟙_ _)),
        HasValue (pullback.snd f t) hTq β v₂) :
    v₁ = v₂ := by
  classical

  obtain rfl : a₁ = a₂ := pullback.hom_ext (ha₁.trans ha₂.symm) (ha₁'.trans ha₂'.symm)

  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of S ⟶ CommRingCat.of Tr, t = Spec.map φ := ⟨Spec.preimage t, (Spec.map_preimage t).symm⟩

  have hTq : (L.baseChange (Spec.map φ)).translate
      (baseChangePointOfBase (Spec.map φ) (t' := 𝟙 (Spec (CommRingCat.of Tr))) ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫
      (L.baseChange (Spec.map φ)).schemeNsmul 2 = (L.baseChange (Spec.map φ)).schemeNsmul 2 :=
    translate_comp_schemeNsmul_of_mem_torsionSubset _ (hc.baseChange _) 2 _
      ((mem_torsionSubset _ _ _ _).2 (isTorsionPoint_ofBase L _ 2 x hx))

  have hnat := schemeNsmul_comp_pinned L (Spec.map φ) ι k a₁ ha₁ ha₁' 2
  obtain ⟨τ⟩ := hAdm
  let β₂ : (Scheme.Modules.pullback ((L.baseChange (Spec.map φ)).schemeNsmul 2)).obj ((Scheme.Modules.pullback a₁).obj 𝓝) ≅
      (Scheme.Modules.pullback ((L.baseChange (Spec.map φ)).schemeNsmul 2)).obj (𝟙_ _) :=
    (Scheme.Modules.pullbackComp _ a₁).app 𝓝 ≪≫ (Scheme.Modules.pullbackCongr hnat).app 𝓝 ≪≫
      ((Scheme.Modules.pullbackComp a₁ _).app 𝓝).symm ≪≫ (Scheme.Modules.pullback a₁).mapIso τ ≪≫
      Scheme.Modules.pullbackUnitIso a₁ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm
  let β₁ := (Scheme.Modules.pullback ((L.baseChange (Spec.map φ)).schemeNsmul 2)).mapIso e₁ ≪≫ β₂
  have h1 : HasValue (pullback.snd f (Spec.map φ)) hTq β₁ v₁ := P₁ hTq β₁
  have h2 : HasValue (pullback.snd f (Spec.map φ)) hTq β₁ v₂ := by
    have := hasValue_trans (pullback.snd f (Spec.map φ)) hTq
      ((Scheme.Modules.pullback ((L.baseChange (Spec.map φ)).schemeNsmul 2)).mapIso e₁) β₂ 1 v₂
      (hasValue_pullback_mapIso_one _ hTq e₁) (P₂ hTq β₂)
    rwa [_root_.one_mul] at this

  letI : Algebra S Tr := φ.hom.toAlgebra
  have hH0 : Function.Bijective fun c : Tr =>
      (pullback.snd f (Spec.map φ)).appTop ((Scheme.ΓSpecIso (CommRingCat.of Tr)).inv c) := by
    have hb := GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_algebraMap_sections_pullback hA Tr
    have heq : (fun c : Tr => (pullback.snd f (Spec.map φ)).appTop ((Scheme.ΓSpecIso (CommRingCat.of Tr)).inv c)) =
        (letI := Scheme.TwoAffineOpenCover.algebraOfHom
          (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S Tr)) ⊤
         ⇑(algebraMap Tr Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap S Tr), ⊤))) := by
      funext c
      rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
      change ((pullback.snd f (Spec.map φ)).app ⊤).hom _ = _
      rw [Scheme.Hom.app_eq_appLE]
      rfl
    rw [heq]
    exact hb
  have hinv : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback ((L.baseChange (Spec.map φ)).schemeNsmul 2)).obj
        (𝟙_ (pullback f (Spec.map φ)).Modules)) :=
    (Scheme.Modules.isInvertible_unit _).pullback _
  obtain ⟨c, -, huniq⟩ := existsUnique_isBaseScalar_of_isInvertible_of_bijective (pullback.snd f (Spec.map φ)) hH0 hinv
    (discrepancy hTq β₁).hom
  exact (huniq v₁ h1).trans (huniq v₂ h2).symm

theorem val_eq' (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    {Tr : Type} [CommRing Tr] (t₁ t₂ : Spec (CommRingCat.of Tr) ⟶ Spec (CommRingCat.of S)) (ht : t₁ = t₂)
    {R : Type} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (k : Spec (CommRingCat.of Tr) ⟶ Spec (CommRingCat.of R))
    (𝓝 : (pullback f ι).Modules)
    (hAdm : Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj 𝓝 ≅ 𝟙_ _))
    (a₁ : pullback f t₁ ⟶ pullback f ι) (a₂ : pullback f t₂ ⟶ pullback f ι)
    (ha₁ : a₁ ≫ pullback.fst f ι = pullback.fst f t₁) (ha₁' : a₁ ≫ pullback.snd f ι = pullback.snd f t₁ ≫ k)
    (ha₂ : a₂ ≫ pullback.fst f ι = pullback.fst f t₂) (ha₂' : a₂ ≫ pullback.snd f ι = pullback.snd f t₂ ≫ k)
    (N₁ : (pullback f t₁).Modules) (e₁ : N₁ ≅ (Scheme.Modules.pullback a₁).obj 𝓝)
    (x₁ : SchemeHomOver t₁ f) (x₂ : SchemeHomOver t₂ f) (hx₁₂ : x₁.1 = x₂.1) (hx : L.IsTorsionPoint t₂ 2 x₂) (v₁ v₂ : Tr)
    (P₁ : ∀ (hTq : (L.baseChange t₁).translate
          (baseChangePointOfBase t₁ (t' := 𝟙 (Spec (CommRingCat.of Tr))) ⟨x₁.1, by rw [Category.id_comp]; exact x₁.2⟩) ≫
          (L.baseChange t₁).schemeNsmul 2 = (L.baseChange t₁).schemeNsmul 2)
        (β : (Scheme.Modules.pullback ((L.baseChange t₁).schemeNsmul 2)).obj N₁ ≅
          (Scheme.Modules.pullback ((L.baseChange t₁).schemeNsmul 2)).obj (𝟙_ _)),
        HasValue (pullback.snd f t₁) hTq β v₁)
    (P₂ : ∀ (hTq : (L.baseChange t₂).translate
          (baseChangePointOfBase t₂ (t' := 𝟙 (Spec (CommRingCat.of Tr))) ⟨x₂.1, by rw [Category.id_comp]; exact x₂.2⟩) ≫
          (L.baseChange t₂).schemeNsmul 2 = (L.baseChange t₂).schemeNsmul 2)
        (β : (Scheme.Modules.pullback ((L.baseChange t₂).schemeNsmul 2)).obj ((Scheme.Modules.pullback a₂).obj 𝓝) ≅
          (Scheme.Modules.pullback ((L.baseChange t₂).schemeNsmul 2)).obj (𝟙_ _)),
        HasValue (pullback.snd f t₂) hTq β v₂) :
    v₁ = v₂ := by
  subst ht
  obtain rfl : x₁ = x₂ := Subtype.ext hx₁₂
  exact val_eq L hc hA t₁ ι k 𝓝 hAdm a₁ a₂ ha₁ ha₁' ha₂ ha₂' N₁ e₁ x₁ hx v₁ v₂ P₁ P₂

@[reassoc]
theorem baseChangeSnd_fst' {R : Type} [CommRing R] {C T T' : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (s : SchemeHomOver t' t) :
    baseChangeSnd c s ≫ pullback.fst c t = pullback.fst c t' := by
  unfold baseChangeSnd; rw [pullback.lift_fst, Category.comp_id]

@[reassoc]
theorem baseChangeSnd_snd' {R : Type} [CommRing R] {C T T' : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (s : SchemeHomOver t' t) :
    baseChangeSnd c s ≫ pullback.snd c t = pullback.snd c t' ≫ s.1 := by
  unfold baseChangeSnd; rw [pullback.lift_snd]

end BCN22

open BCN22 GoodReductionJacobian.RelativeGroupLaw in

theorem solution
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (hker : IsFinite (L.schemeKerStr 2) ∧ Flat (L.schemeKerStr 2) ∧ LocallyOfFinitePresentation (L.schemeKerStr 2))
    (h2fl : IsAffineHom (L.schemeNsmul 2) ∧ Flat (L.schemeNsmul 2) ∧ Surjective (L.schemeNsmul 2)) :
    let Adm : ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)),
        RigidifiedLineBundle f (L.one (𝟙 _)) ι → Prop :=
      fun R _ ι N =>
        Nonempty ((Scheme.Modules.pullback ((L.baseChange ι).schemeNsmul 2)).obj N.L ≅ 𝟙_ _)
    let IsCharOf : ∀ (R : Type) [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)),
        RigidifiedLineBundle f (L.one (𝟙 _)) ι → L.TorsionCharacter 2 ι → Prop :=
      fun R _ ι N χ =>
        ∀ (T : Type) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
          (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) 2 x)
          (hTq : (L.baseChange (κ ≫ ι)).translate
              (RelativeGroupLaw.baseChangePointOfBase (κ ≫ ι) (t' := 𝟙 (Spec (CommRingCat.of T)))
                ⟨x.1, by rw [Category.id_comp]; exact x.2⟩) ≫ (L.baseChange (κ ≫ ι)).schemeNsmul 2 =
            (L.baseChange (κ ≫ ι)).schemeNsmul 2)
          (β : (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj
                (N.pullbackAlong (⟨κ, rfl⟩ : SchemeHomOver (κ ≫ ι) ι)).L ≅
              (Scheme.Modules.pullback ((L.baseChange (κ ≫ ι)).schemeNsmul 2)).obj (𝟙_ _)),
          HasValue (pullback.snd f (κ ≫ ι)) hTq β ((χ.val T κ x hx : Tˣ) : T)
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
      (ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)) (ψ : SchemeHomOver ι' ι)
      (N : RigidifiedLineBundle f (L.one (𝟙 _)) ι) (χ : L.TorsionCharacter 2 ι) (χ' : L.TorsionCharacter 2 ι'),
      Adm R ι N → IsCharOf R ι N χ → IsCharOf R' ι' (N.pullbackAlong ψ) χ' →
      ∀ (T : Type) [CommRing T] (κ' : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R'))
        (x' : SchemeHomOver (κ' ≫ ι') f) (hx' : L.IsTorsionPoint (κ' ≫ ι') 2 x')
        (x : SchemeHomOver ((κ' ≫ ψ.1) ≫ ι) f) (hx : L.IsTorsionPoint ((κ' ≫ ψ.1) ≫ ι) 2 x),
        x'.1 = x.1 → χ'.val T κ' x' hx' = χ.val T (κ' ≫ ψ.1) x hx := by
  intro Adm IsCharOf R R' _ _ ι ι' ψ N χ χ' hAdm hχ hχ' T _ κ' x' hx' x hx hxx
  obtain ⟨ψ₁, hψ⟩ := ψ
  subst hψ
  apply Units.ext
  refine val_eq' L hc hA (κ' ≫ ψ₁ ≫ ι) ((κ' ≫ ψ₁) ≫ ι) (Category.assoc _ _ _).symm ι (κ' ≫ ψ₁) N.L hAdm
    (baseChangeSnd f (⟨κ', rfl⟩ : SchemeHomOver (κ' ≫ ψ₁ ≫ ι) (ψ₁ ≫ ι)) ≫
      baseChangeSnd f (⟨ψ₁, rfl⟩ : SchemeHomOver (ψ₁ ≫ ι) ι))
    (baseChangeSnd f (⟨κ' ≫ ψ₁, rfl⟩ : SchemeHomOver ((κ' ≫ ψ₁) ≫ ι) ι))
    (by rw [Category.assoc, baseChangeSnd_fst', baseChangeSnd_fst'])
    (by rw [Category.assoc, baseChangeSnd_snd', baseChangeSnd_snd'_assoc])
    (baseChangeSnd_fst' f _) (baseChangeSnd_snd' f _)
    _ ((Scheme.Modules.pullbackComp _ _).app N.L) x' x hxx hx _ _
    (fun hTq β => hχ' T κ' x' hx' hTq β) (fun hTq β => hχ T (κ' ≫ ψ₁) x hx hTq β)

end S_AlgebraicGeometry_Polarisation_torsionCharacter_val_pullbackAlong_eq_of_hasValue_translate
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_torsionCharacter_val_pullbackAlong_eq_of_hasValue_translate (solution)
