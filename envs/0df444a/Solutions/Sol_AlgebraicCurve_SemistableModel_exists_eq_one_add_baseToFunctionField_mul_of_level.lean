-- Prove2me | solution 1 for AlgebraicCurve.SemistableModel.exists_eq_one_add_baseToFunctionField_mul_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/fb63f566-20ea-5932-8477-8cae33259cb5

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicGeometry_mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback
import Theorems.Thm_AlgebraicCurve_SemistableModel_mem_localRing_iff_mem_range_of_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableModel_exists_eq_one_add_baseToFunctionField_mul_of_level

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

namespace T5b2Sol

section Generic

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

theorem base_asIdeal_eq_comap {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    (f.base x).asIdeal = Ideal.comap ((X.presheaf.Γgerm x).hom.comp (f.appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) := by
  have hfac : f = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  conv_lhs => rw [hfac]
  rfl

end Generic

section Core
variable {L : Type u} [Field L] {A : ValuationSubring L} {F : Type u'} [Field F] [Algebra L F]
  {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
  {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
  {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))} {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
  (M : SemistableModel A F Fbar C An src tgt xs xt)

theorem toBase_eq_closedPoint_of_gen_specializes (i : ιV) (x : M.X) (h : M.gen i ⤳ x) :
    M.toBase.base x = IsLocalRing.closedPoint A := by
  have h' : M.toBase.base (M.gen i) ⤳ M.toBase.base x := h.map M.toBase.base.hom.continuous
  rw [M.toBase_gen] at h'
  have hle := (PrimeSpectrum.le_iff_specializes _ _).mpr h'
  exact (PrimeSpectrum.ext ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le (M.toBase.base x).2.ne_top hle)).symm

theorem localRing_genericPoint_eq_top :
    SemistableModel.localRing M.X M.ffEquiv (genericPoint M.X) = ⊤ := by
  refine eq_top_iff.mpr (fun f _ => ?_)
  unfold SemistableModel.localRing
  refine ⟨M.ffEquiv f, ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.algebraMap_toAlgebra]
  have : (M.X.presheaf.stalkSpecializes ((genericPoint_spec M.X).specializes (Set.mem_univ _))) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  rw [this]
  simp

end Core

end T5b2Sol

open T5b2Sol in
theorem solution
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (A₁ : Type u) [CommRing A₁] [IsLocalRing A₁] (ι₁ : A₁ →+* A) [IsLocalHom ι₁]
    (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    (ϖ₁ : A₁) (hϖ₁0 : ϖ₁ ≠ 0) (hϖ₁ : IsLocalRing.maximalIdeal A₁ = Ideal.span {ϖ₁})
    [Flat (Spec.map (CommRingCat.ofHom ι₁))]
    (X₁ : Scheme.{u}) [IsIntegral X₁] (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (e₁ : M.X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = M.toBase)
    (F₁ : Subfield F) (φ₁ : F₁ ≃+* X₁.functionField)
    (hcompat : ∃ hgen : (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) =
        genericPoint X₁,
      ∀ s : F₁, M.ffEquiv (s : F) =
        ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint M.X)).hom
          ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₁ s)))
    (x : M.X) (u : F) (hu : u ∈ F₁) :
    (∃ t ∈ IsLocalRing.maximalIdeal A, ∃ r ∈ SemistableModel.localRing M.X M.ffEquiv x,
        u = 1 + algebraMap L F ((t : A) : L) * r) →
      ∃ t₁ ∈ IsLocalRing.maximalIdeal A₁,
        ∃ s ∈ (algebraMap (X₁.presheaf.stalk
          ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) X₁.functionField).range,
        φ₁ ⟨u, hu⟩ = 1 + AlgebraicCurve.SemistableModel.baseToFunctionField f₁ t₁ * s := by
  classical
  rintro ⟨t, ht, r, hr, hutr⟩
  obtain ⟨hgen, hcompat'⟩ := id hcompat

  let π : M.X ⟶ X₁ := e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))
  let Sι := Spec.map (CommRingCat.ofHom ι₁)
  have hsq : π ≫ f₁ = M.toBase ≫ Sι := by
    show (e₁.hom ≫ pullback.fst f₁ _) ≫ f₁ = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, he₁]
  let y : X₁ := π.base x
  let θ : ↥A →+* M.X.presheaf.stalk x := (M.X.presheaf.germ ⊤ x trivial).hom.comp
    (M.toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom)
  let θ₁ : A₁ →+* X₁.presheaf.stalk y := (X₁.presheaf.germ ⊤ y trivial).hom.comp
    (f₁.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom)
  let ψ : M.X.presheaf.stalk x →+* F :=
    (M.ffEquiv.symm : M.X.functionField ≃+* F).toRingHom.comp (algebraMap (M.X.presheaf.stalk x) M.X.functionField)
  have hψinj : Function.Injective ψ := by
    refine (M.ffEquiv.symm.injective).comp ?_
    exact IsFractionRing.injective (M.X.presheaf.stalk x) M.X.functionField
  have hψsurj : ∀ v ∈ SemistableModel.localRing M.X M.ffEquiv x, ∃ q, ψ q = v := fun v hv => hv
  have hψmem : ∀ q, ψ q ∈ SemistableModel.localRing M.X M.ffEquiv x := fun q => ⟨q, rfl⟩

  have hψθ : ∀ a : ↥A, ψ (θ a) = algebraMap L F (a : L) := by
    intro a
    apply M.ffEquiv.injective
    show M.ffEquiv (M.ffEquiv.symm (algebraMap _ M.X.functionField (θ a))) = _
    rw [RingEquiv.apply_symm_apply, M.ffEquiv_algebraMap]
    show (M.X.presheaf.stalkSpecializes _).hom ((M.X.presheaf.germ ⊤ x trivial).hom _) = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rfl

  have hθ₁ : ∀ a : A₁, algebraMap (X₁.presheaf.stalk y) X₁.functionField (θ₁ a) =
      SemistableModel.baseToFunctionField f₁ a := by
    intro a
    show (X₁.presheaf.stalkSpecializes _).hom ((X₁.presheaf.germ ⊤ y trivial).hom _) = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rfl

  have hread : ∀ r₁ : X₁.presheaf.stalk y,
      ψ ((π.stalkMap x).hom r₁) = (φ₁.symm (algebraMap (X₁.presheaf.stalk y) X₁.functionField r₁) : F) := by
    intro r₁
    have h12 : genericPoint M.X ⤳ x := (genericPoint_spec M.X).specializes trivial
    have hsp : π.base (genericPoint M.X) ⤳ y := h12.map π.base.hom.continuous
    apply M.ffEquiv.injective
    show M.ffEquiv (M.ffEquiv.symm (algebraMap _ M.X.functionField ((π.stalkMap x).hom r₁))) = _
    rw [RingEquiv.apply_symm_apply, hcompat', RingEquiv.apply_symm_apply]
    simp only [RingHom.algebraMap_toAlgebra]
    have key := congrArg (fun k => (CommRingCat.Hom.hom k) r₁)
      (Scheme.Hom.stalkSpecializes_stalkMap π (genericPoint M.X) x h12)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at key
    change (M.X.presheaf.stalkSpecializes h12).hom ((π.stalkMap x).hom r₁) = _
    rw [← key]
    congr 1
    change _ = (X₁.presheaf.stalkSpecializes _ ≫ X₁.presheaf.stalkSpecializes _).hom r₁
    rw [TopCat.Presheaf.stalkSpecializes_comp]

  have hι₁inj : Function.Injective ι₁ := by
    have hflat : ι₁.Flat := by
      have hF : Flat (Spec.map (CommRingCat.ofHom ι₁)) := inferInstance
      rwa [HasRingHomProperty.Spec_iff (P := @Flat)] at hF
    algebraize [ι₁]
    haveI : Module.FaithfullyFlat A₁ ↥A := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact (RingHom.faithfullyFlat_algebraMap_iff.mpr ‹_›).injective

  have hconst : ∀ a : A₁, ∃ hmem : algebraMap L F ((ι₁ a : ↥A) : L) ∈ F₁,
      φ₁ ⟨_, hmem⟩ = SemistableModel.baseToFunctionField f₁ a := by
    intro a
    have hval : ((φ₁.symm (SemistableModel.baseToFunctionField f₁ a) : F₁) : F) = algebraMap L F ((ι₁ a : ↥A) : L) := by
      apply M.ffEquiv.injective
      rw [hcompat', RingEquiv.apply_symm_apply, M.ffEquiv_algebraMap]
      exact stalkMap_baseToFunctionField ι₁ π f₁ M.toBase hsq hgen a
    refine ⟨hval ▸ (φ₁.symm (SemistableModel.baseToFunctionField f₁ a)).2, ?_⟩
    have : (⟨_, hval ▸ (φ₁.symm (SemistableModel.baseToFunctionField f₁ a)).2⟩ : F₁) =
        φ₁.symm (SemistableModel.baseToFunctionField f₁ a) := Subtype.ext hval.symm
    rw [this, RingEquiv.apply_symm_apply]
  obtain ⟨hcF₁, hφc⟩ := hconst ϖ₁
  set c : F := algebraMap L F ((ι₁ ϖ₁ : ↥A) : L) with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, map_ne_zero_iff _ (algebraMap L F).injective]
    intro h
    exact hϖ₁0 (hι₁inj (Subtype.ext (by simpa using h)))

  have hv1 : (u - 1) / c ∈ F₁ := F₁.div_mem (F₁.sub_mem hu F₁.one_mem) hcF₁
  refine ⟨ϖ₁, by rw [hϖ₁]; exact Ideal.mem_span_singleton_self ϖ₁, φ₁ ⟨(u - 1) / c, hv1⟩, ?_, ?_⟩
  swap
  ·
    have : (⟨u, hu⟩ : F₁) = 1 + ⟨c, hcF₁⟩ * ⟨(u - 1) / c, hv1⟩ := Subtype.ext (by
      show u = 1 + c * ((u - 1) / c)
      field_simp; ring)
    rw [this, map_add, map_one, map_mul, hφc]

  have hreg := AlgebraicCurve.SemistableModel.mem_localRing_iff_mem_range_of_level M A₁ ι₁ hres₁ X₁ f₁ e₁ he₁ F₁ φ₁
    hcompat x
  by_cases hsp : M.toBase.base x = IsLocalRing.closedPoint ↥A
  ·
    have hvF₁ : u - 1 ∈ F₁ := F₁.sub_mem hu F₁.one_mem
    have hvloc : u - 1 ∈ SemistableModel.localRing M.X M.ffEquiv x := by
      rw [hutr, add_sub_cancel_left]
      exact Subring.mul_mem _ (hψθ t ▸ hψmem (θ t)) hr
    obtain ⟨r₁, hr₁⟩ := (hreg (u - 1) hvF₁).mp hvloc

    obtain ⟨q, hq⟩ := hψsurj r hr
    have hπr₁ : (π.stalkMap x).hom r₁ = θ t * q := by
      apply hψinj
      rw [hread r₁, hr₁, RingEquiv.symm_apply_apply, map_mul, hψθ, hq]
      show u - 1 = _
      rw [hutr, add_sub_cancel_left]
    have hmem : (π.stalkMap x).hom r₁ ∈ Ideal.map θ (IsLocalRing.maximalIdeal ↥A) := by
      rw [hπr₁]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem θ ht)
    have hCF := AlgebraicGeometry.mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback
      ι₁ hres₁ M.toBase f₁ e₁ he₁ x hsp r₁ hmem

    rw [hϖ₁, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hCF
    obtain ⟨s₁, hs₁⟩ := hCF
    refine ⟨s₁, ?_⟩
    apply (mul_right_injective₀ ((map_ne_zero φ₁).mpr (show (⟨c, hcF₁⟩ : F₁) ≠ 0 from
      fun h => hc0 (congrArg Subtype.val h))))
    show φ₁ ⟨c, hcF₁⟩ * algebraMap _ _ s₁ = φ₁ ⟨c, hcF₁⟩ * φ₁ ⟨(u - 1) / c, hv1⟩
    rw [← map_mul]
    have : (⟨c, hcF₁⟩ : F₁) * ⟨(u - 1) / c, hv1⟩ = ⟨u - 1, hvF₁⟩ := Subtype.ext (by
      show c * ((u - 1) / c) = u - 1
      field_simp)
    rw [this, ← hr₁, ← hs₁, map_mul, hθ₁, hφc, mul_comm]
  ·
    have hLreg : ∀ z : L, algebraMap L F z ∈ SemistableModel.localRing M.X M.ffEquiv x := by
      intro z
      obtain ⟨w, rfl⟩ := M.classify_bijective.2 x
      rcases w with ⟨⟩ | P | i | ⟨i, q'⟩ | e₀
      · change algebraMap L F z ∈ SemistableModel.localRing M.X M.ffEquiv (genericPoint M.X)
        rw [localRing_genericPoint_eq_top M]; trivial
      · change algebraMap L F z ∈ SemistableModel.localRing M.X M.ffEquiv (M.pt P)
        rw [M.localRing_pt P]; exact P.algebraMap_mem' z
      · exact absurd (M.toBase_gen i) hsp
      · exact absurd (toBase_eq_closedPoint_of_gen_specializes M i _ (M.gen_specializes_sm i q')) hsp
      · exact absurd (toBase_eq_closedPoint_of_gen_specializes M (src e₀) _ (M.gen_specializes_nd e₀).1) hsp
    apply (hreg ((u - 1) / c) hv1).mp
    rw [div_eq_mul_inv]
    refine Subring.mul_mem _ ?_ ?_
    · rw [hutr, add_sub_cancel_left]
      exact Subring.mul_mem _ (hLreg _) hr
    · rw [hcdef, ← map_inv₀]
      exact hLreg _

end S_AlgebraicCurve_SemistableModel_exists_eq_one_add_baseToFunctionField_mul_of_level
end P2MW
export P2MW.S_AlgebraicCurve_SemistableModel_exists_eq_one_add_baseToFunctionField_mul_of_level (solution)
