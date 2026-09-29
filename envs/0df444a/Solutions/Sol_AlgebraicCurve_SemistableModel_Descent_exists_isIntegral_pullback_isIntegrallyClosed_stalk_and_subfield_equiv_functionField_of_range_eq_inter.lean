-- Prove2me | solution 1 for AlgebraicCurve.SemistableModel.Descent.exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ca9cb07c-e7d7-5bc6-adcf-f47081272a05

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_SemistableModel_isIntegrallyClosed_stalk
import Theorems.Thm_IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableModel_Descent_exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_SemistableModel_Descent_exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter.AlgebraicCurve"

universe u u'

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place SemistableModel.baseToFunctionField SemistableModel SemistableModel.isIntegrallyClosed_stalk"
namespace SemistableModel
p2m_export "AlgebraicCurve.SemistableModel" "baseToFunctionField Descent mk flat toBase X ffEquiv ffEquiv_algebraMap isIntegrallyClosed_stalk"
namespace DescentD2
p2m_open "AlgebraicCurve.SemistableModel AlgebraicCurve"

theorem alg_tower {F : Type*} [Field F] (F₀ F₁ : Subfield F) (h : F₀ ≤ F₁) [Algebra.IsAlgebraic F₀ F] :
    Algebra.IsAlgebraic F₁ F := by
  letI : Algebra F₀ F₁ := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower F₀ F₁ F := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  exact Algebra.IsAlgebraic.tower_top (K := F₀) (L := F₁) (A := F)

theorem base_genericPoint_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : X ⟶ Y) [Surjective g] :
    g.base (genericPoint X) = genericPoint Y := by
  have hX := genericPoint_spec X
  have hY := genericPoint_spec Y
  have h1 : IsGenericPoint (g.base (genericPoint X)) (⊤ : Set Y) := by
    rw [isGenericPoint_def]
    apply Set.eq_univ_of_univ_subset
    have h2 : g.base '' closure ({genericPoint X} : Set X) ⊆ closure (g.base '' {genericPoint X}) :=
      image_closure_subset_closure_image g.base.hom.continuous
    rw [hX.def, Set.image_singleton] at h2
    intro y _
    obtain ⟨x, rfl⟩ := g.surjective y
    exact h2 ⟨x, trivial, rfl⟩
  exact h1.eq hY

section Ring
variable {L : Type u} [Field L] (A : ValuationSubring L) {A₁ : Type u} [CommRing A₁] (ι₁ : A₁ →+* A)

theorem valuationRing_of_range_eq_inter (hι₁ : Function.Injective ι₁) (K₁ : Subfield L)
    (range_ι₁ : Set.range (fun a : A₁ => ((ι₁ a : A) : L)) = (A : Set L) ∩ (K₁ : Set L)) :
    haveI := Function.Injective.isDomain ι₁ hι₁; ValuationRing A₁ := by
  haveI := Function.Injective.isDomain ι₁ hι₁
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  have ha : ((ι₁ a : A) : L) ∈ (A : Set L) ∩ (K₁ : Set L) := range_ι₁ ▸ ⟨a, rfl⟩
  have hb : ((ι₁ b : A) : L) ∈ (A : Set L) ∩ (K₁ : Set L) := range_ι₁ ▸ ⟨b, rfl⟩
  by_cases hb0 : b = 0
  · exact ⟨0, Or.inl (by simp [hb0])⟩
  by_cases ha0 : a = 0
  · exact ⟨0, Or.inr (by simp [ha0])⟩
  have hbL : ((ι₁ b : A) : L) ≠ 0 := by
    intro h; apply hb0; apply hι₁; simpa using h
  have haL : ((ι₁ a : A) : L) ≠ 0 := by
    intro h; apply ha0; apply hι₁; simpa using h
  rcases A.mem_or_inv_mem (((ι₁ b : A) : L) / ((ι₁ a : A) : L)) with h | h
  ·
    have hK : ((ι₁ b : A) : L) / ((ι₁ a : A) : L) ∈ (K₁ : Set L) := K₁.div_mem hb.2 ha.2
    obtain ⟨c, hc⟩ : ((ι₁ b : A) : L) / ((ι₁ a : A) : L) ∈ Set.range (fun a : A₁ => ((ι₁ a : A) : L)) :=
      range_ι₁ ▸ ⟨h, hK⟩
    refine ⟨c, Or.inl ?_⟩
    apply hι₁; ext
    simp only [map_mul]
    push_cast
    simp only at hc
    rw [hc]; field_simp
  · rw [inv_div] at h
    have hK : ((ι₁ a : A) : L) / ((ι₁ b : A) : L) ∈ (K₁ : Set L) := K₁.div_mem ha.2 hb.2
    obtain ⟨c, hc⟩ : ((ι₁ a : A) : L) / ((ι₁ b : A) : L) ∈ Set.range (fun a : A₁ => ((ι₁ a : A) : L)) :=
      range_ι₁ ▸ ⟨h, hK⟩
    refine ⟨c, Or.inr ?_⟩
    apply hι₁; ext
    simp only [map_mul]
    push_cast
    simp only at hc
    rw [hc]; field_simp

theorem faithfullyFlat_of_range_eq_inter [IsLocalHom ι₁] (hι₁ : Function.Injective ι₁) (K₁ : Subfield L)
    (range_ι₁ : Set.range (fun a : A₁ => ((ι₁ a : A) : L)) = (A : Set L) ∩ (K₁ : Set L)) :
    ι₁.FaithfullyFlat := by
  haveI := Function.Injective.isDomain ι₁ hι₁
  haveI : ValuationRing A₁ := valuationRing_of_range_eq_inter A ι₁ hι₁ K₁ range_ι₁
  letI : Algebra A₁ A := ι₁.toAlgebra
  have halg : algebraMap A₁ A = ι₁ := rfl
  haveI : IsLocalHom (algebraMap A₁ A) := halg ▸ inferInstance
  haveI : Module.IsTorsionFree A₁ A := ⟨fun r hr x y hxy => by
    have hr0 : r ≠ 0 := hr.ne_zero
    have h' : ι₁ r * x = ι₁ r * y := by simp [Algebra.smul_def] at hxy ⊢; exact hxy
    exact mul_left_cancel₀ (fun h => hr0 (hι₁ (by simpa using h))) h'⟩
  haveI : Module.Flat A₁ A :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  have : Module.FaithfullyFlat A₁ A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (RingHom.faithfullyFlat_algebraMap_iff.mpr this)

theorem flat_and_surjective_specMap [IsLocalHom ι₁] (hι₁ : Function.Injective ι₁) (K₁ : Subfield L)
    (range_ι₁ : Set.range (fun a : A₁ => ((ι₁ a : A) : L)) = (A : Set L) ∩ (K₁ : Set L)) :
    Flat (Spec.map (CommRingCat.ofHom ι₁)) ∧ Surjective (Spec.map (CommRingCat.ofHom ι₁)) :=
  (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ι₁)).mpr
    (by simpa using faithfullyFlat_of_range_eq_inter A ι₁ hι₁ K₁ range_ι₁)

end Ring

theorem isIntegral_of_flat_of_surjective {X Y : Scheme.{u}} [IsIntegral X] (g : X ⟶ Y) [Flat g] [Surjective g] :
    IsIntegral Y := by
  haveI : IrreducibleSpace Y := by
    have h := (IrreducibleSpace.isIrreducible_univ X).image g.base g.base.hom.continuous.continuousOn
    rw [Set.image_univ, g.surjective.range_eq] at h
    exact { isPreirreducible_univ := h.2, toNonempty := Set.nonempty_iff_univ_nonempty.mpr h.1 }
  haveI : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨x, rfl⟩ := g.surjective y
    algebraize [(g.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ (Flat.stalkMap g x) (g.toLRSHom.prop x)
    exact isReduced_of_injective (g.stalkMap x).hom ‹RingHom.FaithfullyFlat _›.injective
  haveI : IsReduced Y := isReduced_of_isReduced_stalk Y
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

theorem isIntegrallyClosed_stalk_of_flat_of_surjective {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : X ⟶ Y)
    [Flat g] [Surjective g] (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (y : Y) :
    IsIntegrallyClosed (Y.presheaf.stalk y) := by
  obtain ⟨x, rfl⟩ := g.surjective y
  haveI := hX x
  exact (IsIntegrallyClosed.isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom
    (g.stalkMap x).hom (Flat.stalkMap g x)).2

theorem stalkMap_stalkSpecializes_chain {X Y Z : Scheme.{u}} (g : X ⟶ Y) (π : Y ⟶ Z) (x : X) {y : Y} {z : Z}
    (hy : g.base x = y) (hz : π.base y = z) (q : X ⟶ Z) (hq : q = g ≫ π) (hxz : q.base x = z)
    (t : Z.presheaf.stalk z) :
    (q.stalkMap x).hom ((Z.presheaf.stalkSpecializes (specializes_of_eq hxz)).hom t) =
    (g.stalkMap x).hom ((Y.presheaf.stalkSpecializes (specializes_of_eq hy)).hom
      ((π.stalkMap y).hom ((Z.presheaf.stalkSpecializes (specializes_of_eq hz)).hom t))) := by
  subst hy hz hq
  change ((g ≫ π).stalkMap x).hom ((Z.presheaf.stalkSpecializes (specializes_refl (π.base (g.base x)))).hom t) =
    (g.stalkMap x).hom ((Y.presheaf.stalkSpecializes (specializes_refl (g.base x))).hom
      ((π.stalkMap (g.base x)).hom ((Z.presheaf.stalkSpecializes (specializes_refl (π.base (g.base x)))).hom t)))
  simp only [TopCat.Presheaf.stalkSpecializes_refl, Scheme.Hom.stalkMap_comp]
  rfl

theorem stalkMap_baseToFunctionField {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (g : X ⟶ Y) (fY : Y ⟶ Spec (CommRingCat.of R)) (fX : X ⟶ Spec (CommRingCat.of S))
    (hsq : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    (hgen : g.base (genericPoint X) = genericPoint Y) (r : R) :
    (g.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom
      (SemistableModel.baseToFunctionField fY r)) = SemistableModel.baseToFunctionField fX (φ r) := by
  have hnat : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (φ r) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ : CommRingCat.of R ⟶ CommRingCat.of S)
    have h2 := congrArg (fun k => CommRingCat.Hom.hom k r) h
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] using h2
  have hsq' : fY.appTop ≫ g.appTop = (Spec.map (CommRingCat.ofHom φ)).appTop ≫ fX.appTop := by
    rw [← Scheme.Hom.comp_appTop, hsq, Scheme.Hom.comp_appTop]
  have hsq'' := congrArg (fun k => CommRingCat.Hom.hom k ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) hsq'
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hsq''
  simp only [SemistableModel.baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  rw [hnat, ← hsq'']
  rw [← CommRingCat.comp_apply (Y.presheaf.germ ⊤ _ _), TopCat.Presheaf.germ_stalkSpecializes]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rfl

end AlgebraicCurve.SemistableModel.DescentD2

open AlgebraicCurve.SemistableModel.DescentD2

theorem solution
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (A₁ : Type u) [CommRing A₁] (j : D.A₀ →+* A₁) (ι₁ : A₁ →+* A) [IsLocalHom ι₁]
    (hι₁ : Function.Injective ι₁) (hcomp : ι₁.comp j = D.ι)
    (K₁ : Subfield L) (range_ι₁ : Set.range (fun a : A₁ => ((ι₁ a : A) : L)) = (A : Set L) ∩ (K₁ : Set L)) :
    ∃ (X₁ : Scheme.{u}) (_ : IsIntegral X₁) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁)) (_ : IsProper f₁) (_ : Flat f₁)
      (e₁ : M.X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁))),
      e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = M.toBase ∧
      (∀ x : X₁, IsIntegrallyClosed (X₁.presheaf.stalk x)) ∧
    ∃ (F₁ : Subfield F) (φ₁ : F₁ ≃+* X₁.functionField),
      (D.F₀ ≤ F₁) ∧ (∀ x : L, x ∈ K₁ → algebraMap L F x ∈ F₁) ∧ Algebra.IsAlgebraic F₁ F ∧
      (∃ hgen : (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) =
          genericPoint X₁,
        ∀ s : F₁, M.ffEquiv (s : F) =
          ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint M.X)).hom
            ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₁ s))) := by
  classical

  let Sj := Spec.map (CommRingCat.ofHom j)
  let Sι := Spec.map (CommRingCat.ofHom ι₁)
  let X₁ : Scheme.{u} := pullback D.toBase₀ Sj
  let f₁ : X₁ ⟶ Spec (CommRingCat.of A₁) := pullback.snd D.toBase₀ Sj
  let π : X₁ ⟶ D.X₀ := pullback.fst D.toBase₀ Sj

  have hSpec : Spec.map (CommRingCat.ofHom D.ι) = Sι ≫ Sj := by
    rw [← hcomp, CommRingCat.ofHom_comp, Spec.map_comp]

  let e₁ : M.X ≅ pullback f₁ Sι :=
    D.iso ≪≫ pullback.congrHom rfl hSpec ≪≫ (pullbackLeftPullbackSndIso D.toBase₀ Sj Sι).symm
  have he₁ : e₁.hom ≫ pullback.snd f₁ Sι = M.toBase := by
    have h0 := D.iso_snd
    simp only [e₁, f₁, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd,
      pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
    exact h0

  let g : M.X ⟶ X₁ := e₁.hom ≫ pullback.fst f₁ Sι

  have hgπ : g ≫ π = D.iso.hom ≫ pullback.fst D.toBase₀ (Spec.map (CommRingCat.ofHom D.ι)) := by
    simp only [g, π, e₁, f₁, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
      pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]

  have hsq : g ≫ f₁ = M.toBase ≫ Sι := by
    rw [← he₁, Category.assoc, Category.assoc, pullback.condition]

  obtain ⟨hSιflat, hSιsurj⟩ := flat_and_surjective_specMap A ι₁ hι₁ K₁ range_ι₁
  haveI := hSιflat
  haveI := hSιsurj
  haveI hgflat : Flat g := inferInstance
  haveI hgsurj : Surjective g := inferInstance
  haveI hX₁ : IsIntegral X₁ := isIntegral_of_flat_of_surjective g
  have hgen : g.base (genericPoint M.X) = genericPoint X₁ := base_genericPoint_eq g
  have hπgen : π.base (genericPoint X₁) = genericPoint D.X₀ := by
    rw [← hgen]
    change (g ≫ π).base (genericPoint M.X) = genericPoint D.X₀
    rw [hgπ]
    exact D.base_genericPoint

  let ψ : X₁.functionField →+* M.X.functionField :=
    (g.stalkMap (genericPoint M.X)).hom.comp (X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom
  let ψF : X₁.functionField →+* F := M.ffEquiv.symm.toRingHom.comp ψ
  let F₁ : Subfield F := ψF.fieldRange
  let φ₁ : F₁ ≃+* X₁.functionField := ψF.rangeRestrictFieldEquiv.symm
  have hφ₁ : ∀ s : F₁, M.ffEquiv (s : F) = ψ (φ₁ s) := by
    intro s
    have h1 : ψF (φ₁ s) = s := ψF.rangeRestrictFieldEquiv_apply_symm_apply s
    have h2 : (s : F) = M.ffEquiv.symm (ψ (φ₁ s)) := by rw [← h1]; rfl
    rw [h2, RingEquiv.apply_symm_apply]

  have hF₀ : D.F₀ ≤ F₁ := by
    intro s hs
    let t : X₁.functionField := (π.stalkMap (genericPoint X₁)).hom
      ((D.X₀.presheaf.stalkSpecializes (specializes_of_eq hπgen)).hom (D.ffEquiv₀ ⟨s, hs⟩))
    have key : ψ t = M.ffEquiv s := by
      have h1 := D.ffEquiv₀_ffEquiv ⟨s, hs⟩
      rw [stalkMap_stalkSpecializes_chain g π (genericPoint M.X) hgen hπgen _ hgπ.symm D.base_genericPoint] at h1
      exact h1.symm
    refine ⟨t, ?_⟩
    show M.ffEquiv.symm (ψ t) = s
    rw [key, RingEquiv.symm_apply_apply]

  have hK₁A : ∀ a : A₁, algebraMap L F ((ι₁ a : A) : L) ∈ F₁ := by
    intro a
    refine ⟨SemistableModel.baseToFunctionField f₁ a, ?_⟩
    show M.ffEquiv.symm ((g.stalkMap (genericPoint M.X)).hom
      ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (SemistableModel.baseToFunctionField f₁ a))) = _
    rw [stalkMap_baseToFunctionField ι₁ g f₁ M.toBase hsq hgen a, ← M.ffEquiv_algebraMap (ι₁ a),
      RingEquiv.symm_apply_apply]
  have hK₁ : ∀ x : L, x ∈ K₁ → algebraMap L F x ∈ F₁ := by
    intro x hx
    rcases A.mem_or_inv_mem x with h | h
    · obtain ⟨a, ha⟩ : x ∈ Set.range (fun a : A₁ => ((ι₁ a : A) : L)) := range_ι₁ ▸ ⟨h, hx⟩
      simp only at ha
      rw [← ha]; exact hK₁A a
    · by_cases hx0 : x = 0
      · rw [hx0, map_zero]; exact F₁.zero_mem
      obtain ⟨a, ha⟩ : x⁻¹ ∈ Set.range (fun a : A₁ => ((ι₁ a : A) : L)) := range_ι₁ ▸ ⟨h, K₁.inv_mem hx⟩
      simp only at ha
      have h1 := hK₁A a
      rw [ha, map_inv₀] at h1
      simpa using F₁.inv_mem h1

  have halg : Algebra.IsAlgebraic F₁ F := alg_tower D.F₀ F₁ hF₀
  refine ⟨X₁, hX₁, f₁, inferInstance, inferInstance, e₁, he₁, ?_, F₁, φ₁, hF₀, hK₁, halg, hgen, hφ₁⟩
  exact isIntegrallyClosed_stalk_of_flat_of_surjective g
    (AlgebraicCurve.SemistableModel.isIntegrallyClosed_stalk M)

end S_AlgebraicCurve_SemistableModel_Descent_exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter
end P2MW
export P2MW.S_AlgebraicCurve_SemistableModel_Descent_exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter (solution)
