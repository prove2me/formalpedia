-- Prove2me | solution 1 for AlgebraicCurve.cechH1ToH1_corrH1_of_pullback_specMap_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/22a16254-fe71-5390-8c75-63f446746e78

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import Theorems.Thm_AlgebraicCurve_placesOf_preimage_eq_preimage_restrictAlong_placesOf
import Theorems.Thm_AlgebraicCurve_germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
import Theorems.Thm_AlgebraicCurve_germToFunctionField_mem_lSpaceOn_placesOf
import Theorems.Thm_AlgebraicCurve_cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_cechH1ToH1_corrH1_of_pullback_specMap_self
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.Scheme.TwoAffineOpenCover"

namespace T3Kit

section IsoPackage

variable {K : Type u} [Field K] {X X₁ : Scheme.{u}} [IsIntegral X] [IsIntegral X₁] (p : X₁ ⟶ X) [IsIso p]

theorem app_genericPoint : p (genericPoint X₁) = genericPoint X := genericPoint_eq_of_isOpenImmersion p

theorem insep : Inseparable (genericPoint X) (p (genericPoint X₁)) := Inseparable.of_eq (app_genericPoint p).symm

noncomputable def θiso : X.functionField ≅ X₁.functionField :=
  X.presheaf.stalkCongr (insep p) ≪≫ asIso (p.stalkMap (genericPoint X₁))

theorem θiso_hom_apply (z : X.functionField) :
    (θiso p).hom z = p.stalkMap (genericPoint X₁) (X.presheaf.stalkSpecializes (insep p).ge z) := rfl

theorem θiso_germ (U : X.Opens) (hU : genericPoint X ∈ U) (hU₁ : genericPoint X₁ ∈ p ⁻¹ᵁ U) (a : Γ(X, U)) :
    (θiso p).hom (X.presheaf.germ U (genericPoint X) hU a) =
      X₁.presheaf.germ (p ⁻¹ᵁ U) (genericPoint X₁) hU₁ (p.app U a) := by
  rw [θiso_hom_apply, TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

theorem θiso_algebraMap (x₁ : X₁) (z : X.presheaf.stalk (p x₁)) :
    algebraMap (X₁.presheaf.stalk x₁) X₁.functionField (p.stalkMap x₁ z) =
      (θiso p).hom (algebraMap (X.presheaf.stalk (p x₁)) X.functionField z) := by
  rw [θiso_hom_apply, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
    TopCat.Presheaf.stalkSpecializes_comp_apply]
  exact (Scheme.Hom.stalkSpecializes_stalkMap_apply p (genericPoint X₁) x₁
    ((genericPoint_spec X₁).specializes (Set.mem_univ x₁)) z).symm

theorem range_algebraMap_eq (x₁ : X₁) :
    Set.range (algebraMap (X₁.presheaf.stalk x₁) X₁.functionField) =
      (θiso p).hom '' Set.range (algebraMap (X.presheaf.stalk (p x₁)) X.functionField) := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (p.stalkMap x₁)).2 w
    exact ⟨_, ⟨z, rfl⟩, (θiso_algebraMap p x₁ z).symm⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨p.stalkMap x₁ z, θiso_algebraMap p x₁ z⟩

variable (cX : X ⟶ Spec (.of K))

noncomputable def θalg :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField (p ≫ cX)).toAlgebra
    X.functionField ≃ₐ[K] X₁.functionField :=
  letI := (baseToFunctionField cX).toAlgebra
  letI := (baseToFunctionField (p ≫ cX)).toAlgebra
  { (θiso p).commRingCatIsoToRingEquiv with
    commutes' := fun k => by
      change (θiso p).hom (baseToFunctionField cX k) = baseToFunctionField (p ≫ cX) k
      simp only [baseToFunctionField, RingHom.comp_apply]
      rw [θiso_germ p ⊤ trivial trivial]
      rfl }

theorem θalg_apply (z : X.functionField) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField (p ≫ cX)).toAlgebra
    θalg p cX z = (θiso p).hom z := rfl

theorem θalg_toRingHom :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField (p ≫ cX)).toAlgebra
    CommRingCat.ofHom (θalg p cX).toAlgHom.toRingHom = (θiso p).hom := rfl

end IsoPackage

theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    f ∈ (Place.restrictAlong φ hφ w).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem exists_algEquiv_functionField_of_isIso
    {K : Type u} [Field K] {X X₁ : Scheme.{u}} [IsIntegral X] [IsIntegral X₁]
    (cX : X ⟶ Spec (.of K)) (c₁ : X₁ ⟶ Spec (.of K)) (p : X₁ ⟶ X) [IsIso p] (hp : p ≫ cX = c₁) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField c₁).toAlgebra
    ∃ (θ : X.functionField ≃ₐ[K] X₁.functionField) (hθ : θ.toAlgHom.toRingHom.IsIntegral),
      X₁.fromSpecStalk (genericPoint X₁) ≫ p =
          Spec.map (CommRingCat.ofHom θ.toAlgHom.toRingHom) ≫ X.fromSpecStalk (genericPoint X) ∧
      (∀ U : X.Opens, placesOf c₁ (p ⁻¹ᵁ U) = (Place.restrictAlong θ.toAlgHom hθ) ⁻¹' placesOf cX U) ∧
      (∀ (U : X.Opens) [Nonempty (U : X.Opens)] [Nonempty (p ⁻¹ᵁ U : X₁.Opens)] (a : Γ(X, U)),
          (X₁.germToFunctionField (p ⁻¹ᵁ U)).hom (p.app U a) = θ ((X.germToFunctionField U).hom a)) := by
  subst hp
  letI := (baseToFunctionField cX).toAlgebra
  letI := (baseToFunctionField (p ≫ cX)).toAlgebra
  have hθ : (θalg p cX).toAlgHom.toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ (θalg p cX).surjective
  refine ⟨θalg p cX, hθ, ?_, ?_, ?_⟩
  ·
    rw [θalg_toRingHom]
    change _ = Spec.map (X.presheaf.stalkSpecializes (insep p).ge ≫ p.stalkMap (genericPoint X₁)) ≫ _
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  ·
    intro U
    have hO : ∀ v : Place K X₁.functionField,
        ((Place.restrictAlong (θalg p cX).toAlgHom hθ v).toValuationSubring : Set X.functionField) =
          (θiso p).hom ⁻¹' (v.toValuationSubring : Set X₁.functionField) := fun v => by
      ext f; exact mem_restrictAlong_iff _ hθ v f
    ext v
    simp only [Set.mem_preimage, mem_placesOf_iff]
    constructor
    · rintro ⟨x₁, hx₁U, hcl, hrg⟩
      refine ⟨p x₁, hx₁U, ?_, ?_⟩
      · have : ({p x₁} : Set X) = p.homeomorph '' {x₁} := by rw [Set.image_singleton]; rfl
        rw [this]; exact p.homeomorph.isClosedMap _ hcl
      · apply SetLike.coe_injective
        change Set.range _ = ((Place.restrictAlong (θalg p cX).toAlgHom hθ v).toValuationSubring : Set X.functionField)
        rw [hO, ← Set.preimage_image_eq (Set.range _) (θiso p).commRingCatIsoToRingEquiv.injective]
        change (θiso p).hom ⁻¹' ((θiso p).hom '' _) = _
        rw [← range_algebraMap_eq p x₁]
        exact congrArg _ (congrArg SetLike.coe hrg)
    · rintro ⟨x, hxU, hcl, hrg⟩
      obtain ⟨x₁, hx₁⟩ : ∃ x₁ : X₁, p x₁ = x := ⟨p.homeomorph.symm x, p.homeomorph.apply_symm_apply x⟩
      subst hx₁
      have hinj : Function.Injective p := p.homeomorph.injective
      refine ⟨x₁, hxU, ?_, ?_⟩
      · have : ({x₁} : Set X₁) = p ⁻¹' {p x₁} := by
          rw [← Set.image_singleton, hinj.preimage_image]
        rw [this]; exact hcl.preimage p.continuous
      · apply SetLike.coe_injective
        change Set.range _ = (v.toValuationSubring : Set X₁.functionField)
        rw [range_algebraMap_eq p x₁]
        rw [show Set.range (algebraMap (X.presheaf.stalk (p x₁)) X.functionField) =
            ((Place.restrictAlong (θalg p cX).toAlgHom hθ v).toValuationSubring : Set X.functionField) from
          congrArg SetLike.coe hrg, hO]
        exact Set.image_preimage_eq _ (θiso p).commRingCatIsoToRingEquiv.surjective
  ·
    intro U _ _ a
    rw [θalg_apply]
    exact (θiso_germ p U ((genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr
      (let ⟨⟨x, hx⟩⟩ := ‹Nonempty (U : X.Opens)›; ⟨x, Set.mem_univ _, hx⟩)) _ a).symm

end T3Kit

namespace T3Kit

section FieldLevel
variable {K F F₁ F' : Type*} [Field K] [Field F] [Field F₁] [Field F'] [Algebra K F] [Algebra K F₁] [Algebra K F']

theorem isIntegral_algEquiv (θ : F ≃ₐ[K] F₁) : θ.toAlgHom.toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ θ.surjective

theorem isIntegral_comp_symm (θ : F ≃ₐ[K] F₁) (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) :
    (φ.comp θ.symm.toAlgHom).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans θ.symm.toAlgHom.toRingHom φ.toRingHom (RingHom.isIntegral_of_surjective _ θ.symm.surjective) hφ

theorem mem_restrictAlong_iff' (φ : F →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral) (w : Place K F₁) (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem restrictAlong_injective_of_surjective (φ : F →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral)
    (hsurj : Function.Surjective φ) : Function.Injective (fun w : Place K F₁ => w.restrictAlong φ hφ) := by
  intro w w' h
  apply Place.ext
  ext y
  obtain ⟨x, rfl⟩ := hsurj y
  rw [← mem_restrictAlong_iff' φ hφ w x, ← mem_restrictAlong_iff' φ hφ w' x]
  exact congrArg (fun v : Place K F => x ∈ v.toValuationSubring) h |>.to_iff

theorem traceFunAlong_comp_symm (θ : F ≃ₐ[K] F₁) (φ : F →ₐ[K] F') (g : F') :
    traceFunAlong (φ.comp θ.symm.toAlgHom) g = θ (traceFunAlong φ g) := by
  rw [traceFunAlong_apply, traceFunAlong_apply]
  letI A₁ : Algebra F F' := algebraAlong φ
  letI A₂ : Algebra F₁ F' := algebraAlong (φ.comp θ.symm.toAlgHom)
  have key := Algebra.trace_eq_of_equiv_equiv (A₁ := F) (B₁ := F') (A₂ := F₁) (B₂ := F')
    θ.toRingEquiv (RingEquiv.refl F') (by
      ext x
      change (φ.comp θ.symm.toAlgHom) (θ x) = φ x
      simp) g
  rw [key]
  simp

theorem traceIntegralAlong_comp_symm (θ : F ≃ₐ[K] F₁) (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hψ : (φ.comp θ.symm.toAlgHom).toRingHom.IsIntegral) (htr : TraceIntegralAlong φ hφ) :
    TraceIntegralAlong (φ.comp θ.symm.toAlgHom) hψ := by
  intro v₁ f' H
  have hθ := isIntegral_algEquiv θ
  rw [traceFunAlong_comp_symm]
  refine (mem_restrictAlong_iff' θ.toAlgHom hθ v₁ _).mp (htr (v₁.restrictAlong θ.toAlgHom hθ) f' fun w hw => H w ?_)
  apply restrictAlong_injective_of_surjective θ.toAlgHom hθ θ.surjective
  change (w.restrictAlong _ hψ).restrictAlong θ.toAlgHom hθ = v₁.restrictAlong θ.toAlgHom hθ
  have hcomp : ((φ.comp θ.symm.toAlgHom).comp θ.toAlgHom) = φ := by
    ext x; change φ (θ.symm (θ x)) = φ x; rw [AlgEquiv.symm_apply_apply]
  rw [AlgebraicCurve.Place.restrictAlong_restrictAlong θ.toAlgHom (φ.comp θ.symm.toAlgHom) hθ hψ
      (by rw [hcomp]; exact hφ) w, Place.restrictAlong_congr hcomp _ hφ]
  exact hw

theorem cechH1ToH1_mk_congr {S₀ S₁ T₀ T₁ : Set (Place K F)} (h₀ : S₀ = T₀) (h₁ : S₁ = T₁)
    (hS : S₀ ∪ S₁ = Set.univ) (hT : T₀ ∪ T₁ = Set.univ)
    (f : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F))) (g : ↥(lSpaceOn (T₀ ∩ T₁) (0 : Divisor K F)))
    (hfg : (f : F) = g) :
    cechH1ToH1 hS 0 (Submodule.Quotient.mk f) = cechH1ToH1 hT 0 (Submodule.Quotient.mk g) := by
  subst h₀ h₁
  obtain rfl : f = g := Subtype.ext hfg
  rfl

end FieldLevel

section SchemeLevel
open Opposite

theorem fromSpecStalk_comp_eq_of_comp_symm {K : Type u} [Field K] {X X₁ Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral X₁] [IsIntegral Y]
    (cX : X ⟶ Spec (.of K)) (c₁ : X₁ ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
    (p : X₁ ⟶ X) [IsIso p] :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField c₁).toAlgebra
    letI := (baseToFunctionField cY).toAlgebra
    ∀ (θ : X.functionField ≃ₐ[K] X₁.functionField)
      (hθ : X₁.fromSpecStalk (genericPoint X₁) ≫ p =
        Spec.map (CommRingCat.ofHom θ.toAlgHom.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
      (π : Y ⟶ X) (π₁ : Y ⟶ X₁) (hπ₁ : π₁ ≫ p = π)
      (φ : X.functionField →ₐ[K] Y.functionField)
      (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X)),
      Y.fromSpecStalk (genericPoint Y) ≫ π₁ =
        Spec.map (CommRingCat.ofHom (φ.comp θ.symm.toAlgHom).toRingHom) ≫ X₁.fromSpecStalk (genericPoint X₁) := by
  intro θ hθ π π₁ hπ₁ φ hφπ
  letI := (baseToFunctionField cX).toAlgebra
  letI := (baseToFunctionField c₁).toAlgebra
  letI := (baseToFunctionField cY).toAlgebra
  rw [← cancel_mono p, Category.assoc, hπ₁, hφπ, Category.assoc, hθ]
  have h0 : (φ.comp θ.symm.toAlgHom).toRingHom.comp θ.toAlgHom.toRingHom = φ.toRingHom := by
    ext x
    change φ (θ.symm (θ x)) = φ x
    rw [AlgEquiv.symm_apply_apply]
  have h3 : Spec.map (CommRingCat.ofHom (φ.comp θ.symm.toAlgHom).toRingHom) ≫
      Spec.map (CommRingCat.ofHom θ.toAlgHom.toRingHom) = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h0]
  rw [← h3, Category.assoc]

theorem germ_map {X : Scheme.{u}} [IsIntegral X] {U V : X.Opens} [Nonempty (U : X.Opens)] [Nonempty (V : X.Opens)]
    (i : U ≤ V) (s : Γ(X, V)) :
    (X.germToFunctionField U).hom ((X.presheaf.map (homOfLE i).op).hom s) = (X.germToFunctionField V).hom s := by
  change (X.presheaf.map (homOfLE i).op ≫ X.germToFunctionField U) s = _
  rw [Scheme.germToFunctionField, Scheme.germToFunctionField, TopCat.Presheaf.germ_res]

end SchemeLevel

end T3Kit

set_option maxHeartbeats 6400000 in

theorem solution
    (K : Type u) [Field K] {X : Scheme.{u}} (cX : X ⟶ Spec (.of K))
    [IsIntegral X] [IsSeparated cX] [SmoothOfRelativeDimension 1 cX]
    [IsIntegral (Limits.pullback cX (specMap K K))]
    [IsSeparated (pullback.snd cX (specMap K K))]
    [SmoothOfRelativeDimension 1 (pullback.snd cX (specMap K K))]
    (W : X.TwoAffineOpenCover)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K)) [IsIntegral Y] [IsProper y] [SmoothOfRelativeDimension 1 y]
    (πα πβ : Y ⟶ X) (Hα : πα ≫ cX = y) (Hβ : πβ ≫ cX = y)
    (πα₁ πβ₁ : Y ⟶ Limits.pullback cX (specMap K K))
    (hα₁ : πα₁ ≫ pullback.fst cX (specMap K K) = πα) (hβ₁ : πβ₁ ≫ pullback.fst cX (specMap K K) = πβ)
    (s : (W.cover cX).A01) (z : (W.structureSheafSections cX).H1)
    (hcore : letI X₁ := Limits.pullback cX (specMap K K)
      letI c₁ : X₁ ⟶ Spec (.of K) := pullback.snd cX (specMap K K)
      letI := (AlgebraicCurve.baseToFunctionField c₁).toAlgebra
      letI := (AlgebraicCurve.baseToFunctionField y).toAlgebra
      letI W₁ := W.pullback cX K
      ∀ [Nonempty (W₁.U0 ⊓ W₁.U1 : X₁.Opens)]
        (ψα ψβ : X₁.functionField →ₐ[K] Y.functionField)
        (hψπα : Y.fromSpecStalk (genericPoint Y) ≫ πα₁ =
          Spec.map (CommRingCat.ofHom ψα.toRingHom) ≫ X₁.fromSpecStalk (genericPoint X₁))
        (hψπβ : Y.fromSpecStalk (genericPoint Y) ≫ πβ₁ =
          Spec.map (CommRingCat.ofHom ψβ.toRingHom) ≫ X₁.fromSpecStalk (genericPoint X₁))
        (hψα : ψα.toRingHom.IsIntegral) (hψβ : ψβ.toRingHom.IsIntegral) (htrψα : TraceIntegralAlong ψα hψα)
        (hW₁ : AlgebraicCurve.placesOf c₁ W₁.U0 ∪ AlgebraicCurve.placesOf c₁ W₁.U1 = Set.univ)
        (hs₁ : (X₁.germToFunctionField (W₁.U0 ⊓ W₁.U1)).hom ((HomOver.baseChange W cX K).map01 s) ∈
          AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c₁ W₁.U0 ∩ AlgebraicCurve.placesOf c₁ W₁.U1)
            (0 : AlgebraicCurve.Divisor K X₁.functionField)),
        ∃ (sr₁ : (W₁.cover c₁).A01)
          (hsrr₁ : (X₁.germToFunctionField (W₁.U0 ⊓ W₁.U1)).hom sr₁ ∈
            AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c₁ W₁.U0 ∩ AlgebraicCurve.placesOf c₁ W₁.U1)
              (0 : AlgebraicCurve.Divisor K X₁.functionField))
          (x₁' : AlgebraicCurve.cechH1 ((AlgebraicCurve.Place.restrictAlong ψα hψα) ⁻¹' AlgebraicCurve.placesOf c₁ W₁.U0)
            ((AlgebraicCurve.Place.restrictAlong ψα hψα) ⁻¹' AlgebraicCurve.placesOf c₁ W₁.U1)
            (0 : AlgebraicCurve.Divisor K Y.functionField)),
          Scheme.TwoAffineOpenCover.H1baseChangeMap W cX K z = Submodule.Quotient.mk sr₁ ∧
          AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ ψα hψα hW₁) 0 x₁' =
            AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ ψβ hψβ hW₁) 0
              (AlgebraicCurve.cechH1.pullbackAlong ψβ hψβ _ _
                (Submodule.Quotient.mk ⟨(X₁.germToFunctionField (W₁.U0 ⊓ W₁.U1)).hom
                  ((HomOver.baseChange W cX K).map01 s), hs₁⟩)) ∧
          AlgebraicCurve.cechH1ToH1 hW₁ 0
              (Submodule.Quotient.mk ⟨(X₁.germToFunctionField (W₁.U0 ⊓ W₁.U1)).hom sr₁, hsrr₁⟩) =
            AlgebraicCurve.cechH1ToH1 hW₁ 0 (AlgebraicCurve.cechH1.traceAlong ψα hψα htrψα _ _ x₁')) :
    letI := (AlgebraicCurve.baseToFunctionField cX).toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField y).toAlgebra
    ∀ [Nonempty (W.U0 ⊓ W.U1 : X.Opens)]
      (φα φβ : X.functionField →ₐ[K] Y.functionField)
      (hφπα : Y.fromSpecStalk (genericPoint Y) ≫ πα =
        Spec.map (CommRingCat.ofHom φα.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
      (hφπβ : Y.fromSpecStalk (genericPoint Y) ≫ πβ =
        Spec.map (CommRingCat.ofHom φβ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
      (hφα : φα.toRingHom.IsIntegral) (hφβ : φβ.toRingHom.IsIntegral) (htrα : TraceIntegralAlong φα hφα)
      (hW : AlgebraicCurve.placesOf cX W.U0 ∪ AlgebraicCurve.placesOf cX W.U1 = Set.univ)
      (hsr : (X.germToFunctionField (W.U0 ⊓ W.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf cX W.U0 ∩ AlgebraicCurve.placesOf cX W.U1)
          (0 : AlgebraicCurve.Divisor K X.functionField)),
      ∃ (sr : (W.cover cX).A01)
        (hsrr : (X.germToFunctionField (W.U0 ⊓ W.U1)).hom sr ∈
          AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf cX W.U0 ∩ AlgebraicCurve.placesOf cX W.U1)
            (0 : AlgebraicCurve.Divisor K X.functionField))
        (x' : AlgebraicCurve.cechH1 ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf cX W.U0)
          ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf cX W.U1)
          (0 : AlgebraicCurve.Divisor K Y.functionField)),
        z = Submodule.Quotient.mk sr ∧
        AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φα hφα hW) 0 x' =
          AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φβ hφβ hW) 0
            (AlgebraicCurve.cechH1.pullbackAlong φβ hφβ _ _
              (Submodule.Quotient.mk ⟨(X.germToFunctionField (W.U0 ⊓ W.U1)).hom s, hsr⟩)) ∧
        AlgebraicCurve.cechH1ToH1 hW 0
            (Submodule.Quotient.mk ⟨(X.germToFunctionField (W.U0 ⊓ W.U1)).hom sr, hsrr⟩) =
          AlgebraicCurve.cechH1ToH1 hW 0 (AlgebraicCurve.cechH1.traceAlong φα hφα htrα _ _ x') := by
  intro _ φα φβ hφπα hφπβ hφα hφβ htrα hW hsr
  letI := (AlgebraicCurve.baseToFunctionField cX).toAlgebra
  letI := (AlgebraicCurve.baseToFunctionField y).toAlgebra
  letI := (AlgebraicCurve.baseToFunctionField (pullback.snd cX (specMap K K))).toAlgebra

  have hKK : specMap K K = 𝟙 (Spec (.of K)) := by
    simp only [Scheme.TwoAffineOpenCover.specMap, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  haveI : IsIso (specMap K K) := by rw [hKK]; infer_instance
  haveI : IsIso (pullback.fst cX (specMap K K)) := (IsPullback.of_hasPullback cX (specMap K K)).isIso_fst_of_isIso
  have hp : pullback.fst cX (specMap K K) ≫ cX = pullback.snd cX (specMap K K) := by rw [pullback.condition, hKK, Category.comp_id]
  have hα₁' : πα₁ ≫ pullback.snd cX (specMap K K) = y := by rw [← hp, ← Category.assoc, hα₁, Hα]
  have hβ₁' : πβ₁ ≫ pullback.snd cX (specMap K K) = y := by rw [← hp, ← Category.assoc, hβ₁, Hβ]
  haveI : IsSeparated (pullback.fst cX (specMap K K)) := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : UniversallyClosed πα := MorphismProperty.of_postcomp (W := @UniversallyClosed) (W' := @IsSeparated)
    πα cX inferInstance (by rw [Hα]; infer_instance)
  haveI : UniversallyClosed πβ := MorphismProperty.of_postcomp (W := @UniversallyClosed) (W' := @IsSeparated)
    πβ cX inferInstance (by rw [Hβ]; infer_instance)
  haveI : UniversallyClosed πα₁ := MorphismProperty.of_postcomp (W := @UniversallyClosed) (W' := @IsSeparated)
    πα₁ (pullback.fst cX (specMap K K)) inferInstance (by rw [hα₁]; infer_instance)
  haveI : UniversallyClosed πβ₁ := MorphismProperty.of_postcomp (W := @UniversallyClosed) (W' := @IsSeparated)
    πβ₁ (pullback.fst cX (specMap K K)) inferInstance (by rw [hβ₁]; infer_instance)

  obtain ⟨θ, hθ, hθsq, hθpl, hθgerm⟩ := T3Kit.exists_algEquiv_functionField_of_isIso cX (pullback.snd cX (specMap K K)) (pullback.fst cX (specMap K K)) hp
  have hψα : (φα.comp θ.symm.toAlgHom).toRingHom.IsIntegral := T3Kit.isIntegral_comp_symm θ φα hφα
  have hψβ : (φβ.comp θ.symm.toAlgHom).toRingHom.IsIntegral := T3Kit.isIntegral_comp_symm θ φβ hφβ
  have hψπα := T3Kit.fromSpecStalk_comp_eq_of_comp_symm cX (pullback.snd cX (specMap K K)) y (pullback.fst cX (specMap K K)) θ hθsq πα πα₁ hα₁ φα hφπα
  have hψπβ := T3Kit.fromSpecStalk_comp_eq_of_comp_symm cX (pullback.snd cX (specMap K K)) y (pullback.fst cX (specMap K K)) θ hθsq πβ πβ₁ hβ₁ φβ hφπβ
  have htrψα : TraceIntegralAlong (φα.comp θ.symm.toAlgHom) hψα := T3Kit.traceIntegralAlong_comp_symm θ φα hφα hψα htrα

  have nW01 : Nonempty (W.U0 ⊓ W.U1 : X.Opens) := inferInstance
  obtain ⟨⟨x0, hx0⟩⟩ := nW01
  haveI : Nonempty (W.U0 : X.Opens) := ⟨⟨x0, hx0.1⟩⟩
  haveI : Nonempty (W.U1 : X.Opens) := ⟨⟨x0, hx0.2⟩⟩
  haveI nX₁ : ∀ (U : X.Opens) [Nonempty (U : X.Opens)], Nonempty (pullback.fst cX (specMap K K) ⁻¹ᵁ U : (Limits.pullback cX (specMap K K)).Opens) := by
    intro U hU
    obtain ⟨⟨x, hx⟩⟩ := hU
    refine ⟨⟨(inv (pullback.fst cX (specMap K K))) x, ?_⟩⟩
    show (inv (pullback.fst cX (specMap K K)) ≫ pullback.fst cX (specMap K K)) x ∈ U
    rw [IsIso.inv_hom_id]; exact hx
  haveI : Nonempty ((W.pullback cX K).U0 ⊓ (W.pullback cX K).U1 : (Limits.pullback cX (specMap K K)).Opens) := nX₁ (W.U0 ⊓ W.U1)
  haveI : Nonempty ((W.pullback cX K).U0 : (Limits.pullback cX (specMap K K)).Opens) := nX₁ W.U0
  haveI : Nonempty ((W.pullback cX K).U1 : (Limits.pullback cX (specMap K K)).Opens) := nX₁ W.U1
  have hT0 : AlgebraicCurve.placesOf (pullback.snd cX (specMap K K)) (W.pullback cX K).U0 =
      (AlgebraicCurve.Place.restrictAlong θ.toAlgHom hθ) ⁻¹' AlgebraicCurve.placesOf cX W.U0 := hθpl W.U0
  have hT1 : AlgebraicCurve.placesOf (pullback.snd cX (specMap K K)) (W.pullback cX K).U1 =
      (AlgebraicCurve.Place.restrictAlong θ.toAlgHom hθ) ⁻¹' AlgebraicCurve.placesOf cX W.U1 := hθpl W.U1
  have hW₁ : AlgebraicCurve.placesOf (pullback.snd cX (specMap K K)) (W.pullback cX K).U0 ∪ AlgebraicCurve.placesOf (pullback.snd cX (specMap K K)) (W.pullback cX K).U1 = Set.univ := by
    rw [hT0, hT1]; exact AlgebraicCurve.preimage_restrictAlong_union_eq_univ _ _ hW
  have hs₁ := AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf (pullback.snd cX (specMap K K)) (W.pullback cX K).U0 (W.pullback cX K).U1
    ((HomOver.baseChange W cX K).map01 s)

  obtain ⟨sr₁, hsrr₁, x₁', h1, h2, h3⟩ := hcore (φα.comp θ.symm.toAlgHom) (φβ.comp θ.symm.toAlgHom) hψπα hψπβ hψα hψβ htrψα hW₁ hs₁
  obtain ⟨f₁, rfl⟩ := Submodule.Quotient.mk_surjective _ x₁'
  obtain ⟨sr, rfl⟩ := Submodule.Quotient.mk_surjective _ z

  have EA : ∀ (U : X.Opens), (AlgebraicCurve.Place.restrictAlong (φα.comp θ.symm.toAlgHom) hψα) ⁻¹'
      AlgebraicCurve.placesOf (pullback.snd cX (specMap K K)) (pullback.fst cX (specMap K K) ⁻¹ᵁ U) =
      (AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf cX U := fun U => by
    rw [← AlgebraicCurve.placesOf_preimage_eq_preimage_restrictAlong_placesOf (pullback.snd cX (specMap K K)) y πα₁ _ hψα hψπα,
      ← AlgebraicCurve.placesOf_preimage_eq_preimage_restrictAlong_placesOf cX y πα φα hφα hφπα,
      ← Scheme.Hom.comp_preimage, hα₁]
  have EB : ∀ (U : X.Opens), (AlgebraicCurve.Place.restrictAlong (φβ.comp θ.symm.toAlgHom) hψβ) ⁻¹'
      AlgebraicCurve.placesOf (pullback.snd cX (specMap K K)) (pullback.fst cX (specMap K K) ⁻¹ᵁ U) =
      (AlgebraicCurve.Place.restrictAlong φβ hφβ) ⁻¹' AlgebraicCurve.placesOf cX U := fun U => by
    rw [← AlgebraicCurve.placesOf_preimage_eq_preimage_restrictAlong_placesOf (pullback.snd cX (specMap K K)) y πβ₁ _ hψβ hψπβ,
      ← AlgebraicCurve.placesOf_preimage_eq_preimage_restrictAlong_placesOf cX y πβ φβ hφβ hφπβ,
      ← Scheme.Hom.comp_preimage, hβ₁]

  have hgerm01 : ∀ a : (W.cover cX).A01, ((Limits.pullback cX (specMap K K)).germToFunctionField ((W.pullback cX K).U0 ⊓ (W.pullback cX K).U1)).hom
      ((HomOver.baseChange W cX K).map01 a) = θ ((X.germToFunctionField (W.U0 ⊓ W.U1)).hom a) := by
    intro a
    rw [HomOver.map01_apply, Scheme.Hom.appLE]
    change ((Limits.pullback cX (specMap K K)).germToFunctionField (pullback.fst cX (specMap K K) ⁻¹ᵁ (W.U0 ⊓ W.U1))).hom
      ((((Limits.pullback cX (specMap K K)).presheaf.map (homOfLE _).op)).hom ((pullback.fst cX (specMap K K)).app _ a)) = _
    rw [T3Kit.germ_map]
    exact hθgerm _ a

  have mf₁ : (f₁ : Y.functionField) ∈ AlgebraicCurve.lSpaceOn
      ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf cX W.U0 ∩
        (AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf cX W.U1)
      (0 : AlgebraicCurve.Divisor K Y.functionField) := by
    rw [← EA, ← EA]; exact f₁.2
  have c2 : AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φα hφα hW) 0
      (Submodule.Quotient.mk ⟨(f₁ : Y.functionField), mf₁⟩) =
      AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φβ hφβ hW) 0
        (AlgebraicCurve.cechH1.pullbackAlong φβ hφβ _ _
          (Submodule.Quotient.mk ⟨(X.germToFunctionField (W.U0 ⊓ W.U1)).hom s, hsr⟩)) := by
    rw [AlgebraicCurve.cechH1.pullbackAlong_mk] at h2 ⊢
    refine (T3Kit.cechH1ToH1_mk_congr (EA W.U0) (EA W.U1) _ _ f₁ _ rfl).symm.trans (h2.trans ?_)
    refine T3Kit.cechH1ToH1_mk_congr (EB W.U0) (EB W.U1) _ _ _ _ ?_
    change (φβ.comp θ.symm.toAlgHom) (((Limits.pullback cX (specMap K K)).germToFunctionField
        ((W.pullback cX K).U0 ⊓ (W.pullback cX K).U1)).hom ((HomOver.baseChange W cX K).map01 s)) =
      φβ ((X.germToFunctionField (W.U0 ⊓ W.U1)).hom s)
    rw [hgerm01, AlgHom.comp_apply]
    exact congrArg φβ (θ.symm_apply_apply _)

  rw [Scheme.TwoAffineOpenCover.H1baseChangeMap_mk] at h1
  obtain ⟨⟨u₀, u₁⟩, hu⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.eq _).mp h1)
  have hu' : ((Limits.pullback cX (specMap K K)).presheaf.map (homOfLE (inf_le_right : (W.pullback cX K).U0 ⊓ (W.pullback cX K).U1 ≤ (W.pullback cX K).U1)).op).hom u₁ -
      ((Limits.pullback cX (specMap K K)).presheaf.map (homOfLE (inf_le_left : (W.pullback cX K).U0 ⊓ (W.pullback cX K).U1 ≤ (W.pullback cX K).U0)).op).hom u₀ =
      (show Γ(Limits.pullback cX (specMap K K), (W.pullback cX K).U0 ⊓ (W.pullback cX K).U1) from (HomOver.baseChange W cX K).map01 sr) - (show Γ(Limits.pullback cX (specMap K K), (W.pullback cX K).U0 ⊓ (W.pullback cX K).U1) from sr₁) := by
    have := hu
    rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r1_apply,
      TwoChartCech.Cover.lineBundle_r0_apply, Units.val_one, one_mul] at this
    exact this
  have msr : ((Limits.pullback cX (specMap K K)).germToFunctionField ((W.pullback cX K).U0 ⊓ (W.pullback cX K).U1)).hom ((HomOver.baseChange W cX K).map01 sr) ∈
      AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf (pullback.snd cX (specMap K K)) (W.pullback cX K).U0 ∩ AlgebraicCurve.placesOf (pullback.snd cX (specMap K K)) (W.pullback cX K).U1)
        (0 : AlgebraicCurve.Divisor K (Limits.pullback cX (specMap K K)).functionField) :=
    AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf (pullback.snd cX (specMap K K)) _ _ _
  have hcl : (Submodule.Quotient.mk ⟨_, msr⟩ : AlgebraicCurve.cechH1 (AlgebraicCurve.placesOf (pullback.snd cX (specMap K K)) (W.pullback cX K).U0)
      (AlgebraicCurve.placesOf (pullback.snd cX (specMap K K)) (W.pullback cX K).U1) (0 : AlgebraicCurve.Divisor K (Limits.pullback cX (specMap K K)).functionField)) =
      Submodule.Quotient.mk ⟨_, hsrr₁⟩ := by
    apply (Submodule.Quotient.eq _).mpr
    rw [AlgebraicCurve.mem_range_cechDiff_iff]
    have e := congrArg ((Limits.pullback cX (specMap K K)).germToFunctionField
      ((W.pullback cX K).U0 ⊓ (W.pullback cX K).U1)).hom hu'
    rw [map_sub, map_sub, T3Kit.germ_map, T3Kit.germ_map] at e
    change ((Limits.pullback cX (specMap K K)).germToFunctionField ((W.pullback cX K).U0 ⊓ (W.pullback cX K).U1)).hom
        ((HomOver.baseChange W cX K).map01 sr) -
      ((Limits.pullback cX (specMap K K)).germToFunctionField ((W.pullback cX K).U0 ⊓ (W.pullback cX K).U1)).hom sr₁ ∈ _
    exact e ▸ sub_mem
      (Submodule.mem_sup_right (AlgebraicCurve.germToFunctionField_mem_lSpaceOn_placesOf (pullback.snd cX (specMap K K)) _ u₁))
      (Submodule.mem_sup_left (AlgebraicCurve.germToFunctionField_mem_lSpaceOn_placesOf (pullback.snd cX (specMap K K)) _ u₀))
  rw [← hcl, AlgebraicCurve.cechH1.traceAlong_mk] at h3
  have hsrr : (X.germToFunctionField (W.U0 ⊓ W.U1)).hom sr ∈
      AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf cX W.U0 ∩ AlgebraicCurve.placesOf cX W.U1)
        (0 : AlgebraicCurve.Divisor K X.functionField) :=
    AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf cX _ _ _
  let tr := AlgebraicCurve.lSpaceOnZero.traceAlong φα hφα htrα (AlgebraicCurve.placesOf cX W.U0)
    (AlgebraicCurve.placesOf cX W.U1) ⟨(f₁ : Y.functionField), mf₁⟩
  have key : AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ θ.toAlgHom hθ hW) 0
      (AlgebraicCurve.cechH1.pullbackAlong θ.toAlgHom hθ _ _
        (Submodule.Quotient.mk ⟨(X.germToFunctionField (W.U0 ⊓ W.U1)).hom sr, hsrr⟩)) =
      AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ θ.toAlgHom hθ hW) 0
        (AlgebraicCurve.cechH1.pullbackAlong θ.toAlgHom hθ _ _ (Submodule.Quotient.mk tr)) := by
    rw [AlgebraicCurve.cechH1.pullbackAlong_mk, AlgebraicCurve.cechH1.pullbackAlong_mk]
    refine (T3Kit.cechH1ToH1_mk_congr hT0 hT1 hW₁ _ _ _ ?_).symm.trans (h3.trans (T3Kit.cechH1ToH1_mk_congr hT0 hT1 hW₁ _ _ _ ?_))
    · rw [AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply]; exact hgerm01 sr
    · rw [AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply, AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply,
        AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply]
      exact T3Kit.traceFunAlong_comp_symm θ φα _
  have c3 := AlgebraicCurve.cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq θ.toAlgHom hθ θ.bijective hW _ _ key

  refine ⟨sr, hsrr, Submodule.Quotient.mk ⟨(f₁ : Y.functionField), mf₁⟩, rfl, c2, ?_⟩
  rw [AlgebraicCurve.cechH1.traceAlong_mk]
  exact c3

end S_AlgebraicCurve_cechH1ToH1_corrH1_of_pullback_specMap_self
end P2MW
export P2MW.S_AlgebraicCurve_cechH1ToH1_corrH1_of_pullback_specMap_self (solution)
