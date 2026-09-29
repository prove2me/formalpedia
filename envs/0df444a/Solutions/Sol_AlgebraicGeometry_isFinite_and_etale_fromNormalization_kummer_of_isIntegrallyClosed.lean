-- Prove2me | solution 1 for AlgebraicGeometry.isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9d57471e-9f1f-5bf9-9b97-3c9a16d241f9

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"

namespace KFEAux
open AlgebraicGeometry.Scheme
variable {X : Scheme.{u}} [IsIntegral X]

abbrev Kum (X : Scheme.{u}) [IsIntegral X] (k : ℕ) (g : X.functionField) : Type u :=
  AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)

noncomputable abbrev kumHom (X : Scheme.{u}) [IsIntegral X] (k : ℕ) (g : X.functionField) :
    Spec (CommRingCat.of (Kum X k g)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap X.functionField (Kum X k g))) ≫ X.fromSpecStalk (genericPoint X)

theorem kumHom_preimage_eq_top (k : ℕ) (g : X.functionField) {V : X.Opens} (hη : genericPoint X ∈ V) :
    (kumHom X k g) ⁻¹ᵁ V = ⊤ := by
  apply le_antisymm le_top
  intro p _
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply]
  have hmem : X.fromSpecStalk (genericPoint X)
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (Kum X k g))) p) ∈
      Set.range (X.fromSpecStalk (genericPoint X)) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hmem
  exact hmem.mem_open V.2 hη

noncomputable def secIso (k : ℕ) (g : X.functionField) {V : X.Opens} (hη : genericPoint X ∈ V) :
    Γ(Spec (CommRingCat.of (Kum X k g)), (kumHom X k g) ⁻¹ᵁ V) ≅ CommRingCat.of (Kum X k g) :=
  (Spec (CommRingCat.of (Kum X k g))).presheaf.mapIso (eqToIso (kumHom_preimage_eq_top k g hη).symm).op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (Kum X k g))

set_option maxHeartbeats 3200000 in
theorem app_secIso_hom (k : ℕ) (g : X.functionField) {V : X.Opens} (hη : genericPoint X ∈ V) :
    (kumHom X k g).app V ≫ (secIso k g hη).hom =
      X.presheaf.germ V (genericPoint X) hη ≫ CommRingCat.ofHom (algebraMap X.functionField (Kum X k g)) := by
  have hle : (⊤ : (Spec (CommRingCat.of (Kum X k g))).Opens) ≤ (kumHom X k g) ⁻¹ᵁ V :=
    (kumHom_preimage_eq_top k g hη).ge
  simp only [secIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op]
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [Scheme.Hom.comp_appLE, Scheme.fromSpecStalk_app hη]
  simp only [Category.assoc, Scheme.Hom.map_appLE_assoc]
  congr 1
  rw [show Scheme.Hom.appLE (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (Kum X k g)))) ⊤ ⊤ le_top
      = (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (Kum X k g)))).appTop from
    Scheme.Hom.appLE_eq_app _]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end KFEAux

namespace KFEAux
open AlgebraicGeometry.Scheme
variable {X : Scheme.{u}} [IsIntegral X]

theorem isIntegrallyClosed_sections (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (V : X.affineOpens) (hη : genericPoint X ∈ (V : X.Opens)) : IsIntegrallyClosed Γ(X, (V : X.Opens)) := by
  haveI : Nonempty (V : X.Opens) := ⟨⟨_, hη⟩⟩
  haveI : IsDomain Γ(X, (V : X.Opens)) := IsIntegral.component_integral (V : X.Opens)
  refine IsIntegrallyClosed.of_localization_maximal fun p hp hmax => ?_
  let y : PrimeSpectrum Γ(X, (V : X.Opens)) := ⟨p, hmax.isPrime⟩
  have hy : V.2.fromSpec y ∈ (V : X.Opens) := by
    have : V.2.fromSpec y ∈ Set.range (V.2.fromSpec) := Set.mem_range_self y
    rwa [V.2.range_fromSpec] at this
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨V.2.fromSpec y, hy⟩
  haveI hloc : IsLocalization p.primeCompl (X.presheaf.stalk (V.2.fromSpec y)) := V.2.isLocalization_stalk' y hy
  exact (hnorm _).of_equiv
    (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (V.2.fromSpec y)) (Localization.AtPrime p)).toRingEquiv

end KFEAux

namespace KFEAux
open AlgebraicGeometry.Scheme
variable {X : Scheme.{u}} [IsIntegral X]

def Good (k : ℕ) (g : X.functionField) {r : ℕ} (U : Fin r → X.Opens) (h : Fin r → X.functionField)
    (V : X.affineOpens) : Prop :=
  ∃ hη : genericPoint X ∈ (V : X.Opens), ∃ a, (V : X.Opens) ≤ U a ∧ ∃ v w : Γ(X, (V : X.Opens)), v * w = 1 ∧
    (X.presheaf.germ (V : X.Opens) (genericPoint X) hη).hom v = g / h a ^ k

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem key {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (hk : IsUnit ((k : ℕ) : R)) (g : X.functionField) (hg : g ≠ 0)
    {r : ℕ} (U : Fin r → X.Opens) (h : Fin r → X.functionField) (hh : ∀ a, h a ≠ 0)
    (V : X.affineOpens) (hV : Good k g U h V) :
    letI := ((kumHom X k g).app (V : X.Opens)).hom.toAlgebra
    Module.Finite Γ(X, (V : X.Opens)) (integralClosure Γ(X, (V : X.Opens))
        Γ(Spec (CommRingCat.of (Kum X k g)), (kumHom X k g) ⁻¹ᵁ (V : X.Opens))) ∧
    Algebra.Etale Γ(X, (V : X.Opens)) (integralClosure Γ(X, (V : X.Opens))
        Γ(Spec (CommRingCat.of (Kum X k g)), (kumHom X k g) ⁻¹ᵁ (V : X.Opens))) := by
  obtain ⟨hη, a, hVU, v, w, hvw, hgerm⟩ := hV
  letI inst := ((kumHom X k g).app (V : X.Opens)).hom.toAlgebra
  haveI : Nonempty (V : X.Opens) := ⟨⟨_, hη⟩⟩
  haveI : IsDomain Γ(X, (V : X.Opens)) := IsIntegral.component_integral (V : X.Opens)
  haveI : IsFractionRing Γ(X, (V : X.Opens)) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (V : X.Opens) V.2
  haveI : IsIntegrallyClosed Γ(X, (V : X.Opens)) := isIntegrallyClosed_sections hnorm V hη

  have hkB : IsUnit ((k : ℕ) : Γ(X, (V : X.Opens))) := by
    have := hk.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫
      X.presheaf.map (homOfLE (le_top : (V : X.Opens) ≤ ⊤)).op).hom
    simpa using this
  have hvu : IsUnit v := isUnit_iff_exists_inv.mpr ⟨w, hvw⟩
  have hgeq : g = algebraMap Γ(X, (V : X.Opens)) X.functionField v * h a ^ k := by
    have : algebraMap Γ(X, (V : X.Opens)) X.functionField v = g / h a ^ k := hgerm
    rw [this, div_mul_cancel₀ _ (pow_ne_zero _ (hh a))]
  obtain ⟨-, hEt, hFin⟩ := IsIntegrallyClosed.integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow
    (B := Γ(X, (V : X.Opens))) (F := X.functionField) k hkB v hvu (h a) (hh a) g hgeq

  let e : Γ(Spec (CommRingCat.of (Kum X k g)), (kumHom X k g) ⁻¹ᵁ (V : X.Opens)) ≃ₐ[Γ(X, (V : X.Opens))] Kum X k g :=
    AlgEquiv.ofRingEquiv (f := (secIso k g hη).commRingCatIsoToRingEquiv) (fun s => by
      change ((kumHom X k g).app (V : X.Opens) ≫ (secIso k g hη).hom) s =
        algebraMap X.functionField (Kum X k g) (algebraMap Γ(X, (V : X.Opens)) X.functionField s)
      rw [app_secIso_hom]
      rfl)
  let e' := (AlgEquiv.mapIntegralClosure e).symm
  exact ⟨Module.Finite.equiv e'.toLinearEquiv, Algebra.Etale.of_equiv e'⟩

end KFEAux

namespace KFEAux
open AlgebraicGeometry.Scheme
variable {X : Scheme.{u}} [IsIntegral X]

theorem genericPoint_mem_of_nonempty {V : X.Opens} (hV : Nonempty (V : X.Opens)) : genericPoint X ∈ V :=
  ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using hV)

omit [IsIntegral X] in

theorem res_res {A B C : X.Opens} (i : C ⟶ B) (j : B ⟶ A) (s : X.presheaf.obj (Opposite.op A)) :
    X.presheaf.map i.op (X.presheaf.map j.op s) = X.presheaf.map (homOfLE (i.le.trans j.le)).op s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem iSup_good_eq_top (k : ℕ) (g : X.functionField) (hg : g ≠ 0)
    {r : ℕ} (U : Fin r → X.Opens) (hU : (⨆ a, U a) = ⊤) (h : Fin r → X.functionField) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (x : X), x ∈ U a →
      g / h a ^ k ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
      h a ^ k / g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    (⨆ V : {V : X.affineOpens // Good k g U h V}, ((V : X.affineOpens) : X.Opens)) = ⊤ := by
  apply le_antisymm le_top
  intro x _
  have hx : x ∈ (⨆ a, U a) := by rw [hU]; trivial
  obtain ⟨a, hxa⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨⟨s, hs⟩, ⟨s', hs'⟩⟩ := hdiv a x hxa
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
    IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have hk0 : h a ^ k ≠ 0 := pow_ne_zero k (hh a)
  have hss' : s * s' = 1 := hinj (by
    rw [map_mul, hs, hs', map_one, div_mul_div_comm, mul_comm g (h a ^ k), div_self (mul_ne_zero hk0 hg)])
  obtain ⟨W₁, hxW₁, t, ht⟩ := X.presheaf.exists_germ_eq s
  obtain ⟨W₂, hxW₂, t', ht'⟩ := X.presheaf.exists_germ_eq s'
  have hgerm1 : X.presheaf.germ (W₁ ⊓ W₂) x ⟨hxW₁, hxW₂⟩
      (X.presheaf.map (homOfLE inf_le_left).op t * X.presheaf.map (homOfLE inf_le_right).op t') =
      X.presheaf.germ (W₁ ⊓ W₂) x ⟨hxW₁, hxW₂⟩ 1 := by
    rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ht, ht', hss']
  obtain ⟨W, hxW, i₁, i₂, hW⟩ := X.presheaf.germ_eq x _ _ _ _ hgerm1
  obtain ⟨V', hV'mem, hxV', hV'le⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ W ⊓ U a from ⟨hxW, hxa⟩)
  let V : X.affineOpens := ⟨V', hV'mem⟩
  have hη : genericPoint X ∈ (V : X.Opens) := genericPoint_mem_of_nonempty ⟨⟨x, hxV'⟩⟩
  have hVW : (V : X.Opens) ≤ W := hV'le.trans inf_le_left
  have iV1 : (V : X.Opens) ≤ W₁ := hVW.trans (i₁.le.trans inf_le_left)
  have iV2 : (V : X.Opens) ≤ W₂ := hVW.trans (i₁.le.trans inf_le_right)
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hη, a, hV'le.trans inf_le_right,
    X.presheaf.map (homOfLE iV1).op t, X.presheaf.map (homOfLE iV2).op t', ?_, ?_⟩, hxV'⟩
  ·
    have e1 : X.presheaf.map (homOfLE iV1).op t =
        X.presheaf.map (homOfLE hVW).op (X.presheaf.map i₁.op (X.presheaf.map (homOfLE inf_le_left).op t)) := by
      rw [res_res, res_res]
    have e2 : X.presheaf.map (homOfLE iV2).op t' =
        X.presheaf.map (homOfLE hVW).op (X.presheaf.map i₁.op (X.presheaf.map (homOfLE inf_le_right).op t')) := by
      rw [res_res, res_res]
    rw [e1, e2, ← map_mul, ← map_mul, hW, map_one, map_one]
  ·
    have h1 : X.presheaf.germ (V : X.Opens) (genericPoint X) hη (X.presheaf.map (homOfLE iV1).op t)
        = X.presheaf.germ W₁ (genericPoint X) (iV1 hη) t := TopCat.Presheaf.germ_res_apply ..
    have h2 : X.presheaf.germ W₁ (genericPoint X) (iV1 hη) t
        = algebraMap (X.presheaf.stalk x) X.functionField s := by
      rw [← ht]
      change _ = (X.presheaf.germ W₁ x hxW₁ ≫ X.presheaf.stalkSpecializes _) t
      rw [TopCat.Presheaf.germ_stalkSpecializes]
    change X.presheaf.germ (V : X.Opens) (genericPoint X) hη _ = _
    rw [h1, h2, hs]

end KFEAux

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of R))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (hk : IsUnit ((k : ℕ) : R))
    (g : X.functionField) (hg : g ≠ 0)
    (r : ℕ) (U : Fin r → X.Opens) (hU : (⨆ a, U a) = ⊤) (h : Fin r → X.functionField) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (x : X), x ∈ U a →
      g / h a ^ k ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
      h a ^ k / g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    let π := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization
    IsFinite π ∧ AlgebraicGeometry.Etale π := by
  set φ := Spec.map (CommRingCat.ofHom (algebraMap X.functionField
        (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X) with hφ
  intro π
  change IsFinite φ.fromNormalization ∧ Etale φ.fromNormalization
  have hcov := KFEAux.iSup_good_eq_top k g hg U hU h hh hdiv
  constructor
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _ hcov]
    rintro ⟨V, hV⟩
    let e := IsOpenImmersion.isoOfRangeEq (φ.fromNormalization ⁻¹ᵁ (V : X.Opens)).ι (φ.normalizationOpenCover.f V)
      (by simpa using congr($(φ.fromNormalization_preimage V).1))
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
      ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ V.2.isoSpec.hom]
    have : (φ.normalizationDiagramMap.app (.op V)).hom.Finite := by
      letI := (φ.app V).hom.toAlgebra
      change (algebraMap Γ(X, (V : X.Opens)) (integralClosure Γ(X, (V : X.Opens))
        Γ(Spec (CommRingCat.of (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField))), φ ⁻¹ᵁ (V : X.Opens)))).Finite
      rw [RingHom.finite_algebraMap]
      exact (KFEAux.key f hnorm k hk g hg U h hh V hV).1
    convert! (IsFinite.SpecMap_iff _).mpr this
    rw [← cancel_mono V.2.fromSpec]
    simp [IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Etale) _ hcov]
    rintro ⟨V, hV⟩
    let e := IsOpenImmersion.isoOfRangeEq (φ.fromNormalization ⁻¹ᵁ (V : X.Opens)).ι (φ.normalizationOpenCover.f V)
      (by simpa using congr($(φ.fromNormalization_preimage V).1))
    rw [← MorphismProperty.cancel_left_of_respectsIso @Etale e.inv,
      ← MorphismProperty.cancel_right_of_respectsIso @Etale _ V.2.isoSpec.hom]
    have : (φ.normalizationDiagramMap.app (.op V)).hom.Etale := by
      letI := (φ.app V).hom.toAlgebra
      change (algebraMap Γ(X, (V : X.Opens)) (integralClosure Γ(X, (V : X.Opens))
        Γ(Spec (CommRingCat.of (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField))), φ ⁻¹ᵁ (V : X.Opens)))).Etale
      rw [RingHom.etale_algebraMap]
      exact (KFEAux.key f hnorm k hk g hg U h hh V hV).2
    convert! (HasRingHomProperty.Spec_iff (P := @Etale)).mpr this
    rw [← cancel_mono V.2.fromSpec]
    simp [IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]

end S_AlgebraicGeometry_isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed
end P2MW
export P2MW.S_AlgebraicGeometry_isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed (solution)
