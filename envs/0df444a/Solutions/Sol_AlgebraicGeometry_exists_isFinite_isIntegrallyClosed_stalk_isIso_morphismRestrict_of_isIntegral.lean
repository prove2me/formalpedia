-- Prove2me | solution 1 for AlgebraicGeometry.exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9a654b30-74e4-574d-b25a-52a587f373d6

import Mathlib
import Theorems.Thm_IsIntegralClosure_finite_of_finiteType
import Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import Theorems.Thm_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType
import Theorems.Thm_Algebra_IsIntegral_ringKrullDim_le_of_injective
import Theorems.Thm_ringKrullDim_le_of_ringHom_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.fromSpecStalk_app Scheme.Opens.ι_image_le Surjective Scheme.fromSpecStalk_closedPoint Spec.map_apply morphismRestrict_ι Scheme.Opens.range_ι Scheme.Hom iSup_affineOpens_eq_top IsAffineOpen.isoSpec_inv_ι morphismRestrictRestrict IsFinite IsZariskiLocalAtTarget LocallyOfFiniteType Spec StructureSheaf.toStalk IsIntegral Spec.map Scheme Scheme.Hom.toNormalization_fromNormalization IsOpenImmersion functionField_isFractionRing_of_isAffineOpen exists_isAffineOpen_mem_and_subset IsOpenImmersion.isoOfRangeEq isAffineOpen_top IsZariskiLocalAtTarget.iff_of_iSup_eq_top IsAffineOpen IsAffineOpen.range_fromSpec StructureSheaf.IsLocalization.to_stalk Scheme.Opens Scheme.Hom.comp_apply IsOpenImmersion.isoOfRangeEq_hom_fac Scheme.ΓSpecIso"
namespace NormalizationOfVariety
p2m_open "AlgebraicGeometry"

section Algebra

theorem exists_ringKrullDim_eq_natCast (k : Type u) [Field k] (A : Type u) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) := by
  have h := Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k A
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := k) (S := A))
  exact ⟨n, by rw [h, hn]; simp⟩

theorem enat_eq_of_add_natCast_eq {a b : ℕ∞} {m : ℕ}
    (h : (a : WithBot ℕ∞) + (m : WithBot ℕ∞) = (b : WithBot ℕ∞) + (m : WithBot ℕ∞)) : a = b := by
  rw [← WithBot.coe_natCast, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at h
  exact (ENat.add_left_injective_of_ne_top (ENat.coe_ne_top m)) h

theorem height_eq_height_comap (k : Type u) [Field k] {A B : Type u} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra k B]
    [IsScalarTower k A B] [Module.Finite A B] [FaithfulSMul A B] (Q : Ideal B) [Q.IsPrime] :
    Q.height = (Q.comap (algebraMap A B)).height := by
  haveI : Algebra.FiniteType A B := inferInstance
  haveI : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI : Algebra.IsIntegral A B := inferInstance
  haveI : FaithfulSMul k A :=
    (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k A).injective
  set P : Ideal A := Q.comap (algebraMap A B) with hP
  haveI : P.IsPrime := Ideal.comap_isPrime _ _

  have hdim : ringKrullDim B = ringKrullDim A := by
    have h1 := trdeg_add_eq k A (A := B)
    rw [trdeg_eq_zero (R := A) (A := B), add_zero] at h1
    rw [Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k B,
      Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k A, h1]

  have hquot : ringKrullDim (B ⧸ Q) = ringKrullDim (A ⧸ P) := by
    haveI : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) := Algebra.IsIntegral.quotient
    have hinj : Function.Injective (algebraMap (A ⧸ P) (B ⧸ Q)) :=
      Ideal.quotientMap_injective
    have h1 : ringKrullDim (A ⧸ P) ≤ ringKrullDim (B ⧸ Q) :=
      Algebra.IsIntegral.ringKrullDim_le_of_injective hinj
    have h2 : ringKrullDim (B ⧸ Q) ≤ ringKrullDim (A ⧸ P) :=
      ringKrullDim_le_of_ringHom_isIntegral (algebraMap (A ⧸ P) (B ⧸ Q))
        (algebraMap_isIntegral_iff.mpr inferInstance)
    exact le_antisymm h2 h1

  have hB := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k Q
  have hA := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k P
  haveI : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_natCast k (A ⧸ P)
  rw [hquot, hm, hdim, ← hA, hm] at hB
  exact enat_eq_of_add_natCast_eq hB

theorem integralClosure_transport {A K L : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CommRing L] [Algebra A L] (e : K ≃ₐ[A] L)
    (hfin : Module.Finite A (integralClosure A K)) :
    IsFractionRing A L ∧ Module.Finite A (integralClosure A L) ∧
      IsDomain (integralClosure A L) ∧ IsIntegrallyClosed (integralClosure A L) := by
  haveI : IsFractionRing A L := IsLocalization.isLocalization_of_algEquiv _ e
  let Φ : integralClosure A K ≃ₐ[A] integralClosure A L :=
    (e.subalgebraMap _).trans (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv e))
  have h1 : Module.Finite A (integralClosure A L) := Module.Finite.equiv Φ.toLinearEquiv
  haveI : IsDomain (integralClosure A K) := inferInstance
  have h2 : IsDomain (integralClosure A L) :=
    Function.Injective.isDomain Φ.symm.toAlgHom.toRingHom Φ.symm.injective
  have h3 : IsIntegrallyClosed (integralClosure A K) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance
  have h4 : IsIntegrallyClosed (integralClosure A L) := IsIntegrallyClosed.of_equiv Φ.toRingEquiv
  exact ⟨inferInstance, h1, h2, h4⟩

theorem bijective_algebraMap_integralClosure {A L : Type u} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing L] [Algebra A L] [IsFractionRing A L] :
    Function.Bijective (algebraMap A (integralClosure A L)) := by
  have hbot : integralClosure A L = ⊥ :=
    (IsIntegrallyClosedIn.integralClosure_eq_bot_iff L (IsFractionRing.injective A L)).mpr
      ((isIntegrallyClosed_iff_isIntegrallyClosedIn L).mp inferInstance)
  refine ⟨fun a b hab => IsFractionRing.injective A L
    (congrArg (fun x : integralClosure A L => (x : L)) hab), fun x => ?_⟩
  have hx : (x : L) ∈ (⊥ : Subalgebra A L) := hbot ▸ x.2
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hx
  exact ⟨a, Subtype.ext ha⟩

end Algebra

theorem subsingleton_sections_of_eq_bot (X : Scheme.{u}) {U : X.Opens} (h : U = ⊥) :
    Subsingleton Γ(X, U) :=
  CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty h)

theorem primeIdealOf_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (p : Spec Γ(X, U)) (h : hU.fromSpec.base p ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec.base p, h⟩ = p := by
  apply hU.fromSpec.isOpenEmbedding.injective
  exact hU.fromSpec_primeIdealOf ⟨_, h⟩

theorem ringKrullDim_stalk_eq_height {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) = (hU.primeIdealOf ⟨x, hx⟩).asIdeal.height := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (X.presheaf.stalk x)

theorem isIntegrallyClosed_localization_of_stalk {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (p : Spec Γ(X, U)) (h : hU.fromSpec.base p ∈ U)
    (hn : IsIntegrallyClosed (X.presheaf.stalk (hU.fromSpec.base p))) :
    IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec.base p)) :=
    (X.presheaf.germ U _ h).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨_, h⟩
  rw [primeIdealOf_fromSpec hU p h] at this
  let e : Localization.AtPrime p.asIdeal ≃ₐ[Γ(X, U)] X.presheaf.stalk (hU.fromSpec.base p) :=
    IsLocalization.algEquiv p.asIdeal.primeCompl _ _
  exact IsIntegrallyClosed.of_equiv e.symm.toRingEquiv

theorem isLocalization_stalk_Spec (R : CommRingCat.{u}) (t : Spec R) :
    letI : Algebra R ((Spec R).presheaf.stalk t) := (StructureSheaf.toStalk R t).hom.toAlgebra
    IsLocalization.AtPrime ((Spec R).presheaf.stalk t) t.asIdeal := by
  convert! StructureSheaf.IsLocalization.to_stalk R t

theorem ringKrullDim_stalk_Spec (R : CommRingCat.{u}) (t : Spec R) :
    ringKrullDim ((Spec R).presheaf.stalk t) = t.asIdeal.height := by
  letI : Algebra R ((Spec R).presheaf.stalk t) := (StructureSheaf.toStalk R t).hom.toAlgebra
  haveI := isLocalization_stalk_Spec R t
  exact IsLocalization.AtPrime.ringKrullDim_eq_height t.asIdeal _

theorem isIntegrallyClosed_stalk_Spec (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
    (t : Spec R) : IsIntegrallyClosed ((Spec R).presheaf.stalk t) := by
  letI : Algebra R ((Spec R).presheaf.stalk t) := (StructureSheaf.toStalk R t).hom.toAlgebra
  haveI := isLocalization_stalk_Spec R t
  exact isIntegrallyClosed_of_isLocalization ((Spec R).presheaf.stalk t) t.asIdeal.primeCompl
    t.asIdeal.primeCompl_le_nonZeroDivisors

theorem stalk_iso_of_isOpenImmersion {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g] (x : X) :
    Nonempty (Y.presheaf.stalk (g.base x) ≅ X.presheaf.stalk x) := ⟨asIso (g.stalkMap x)⟩

theorem isIso_morphismRestrict_of_chart {X Y : Scheme.{u}} (g : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) {R : CommRingCat.{u}} (c : Spec R ⟶ X) [IsOpenImmersion c]
    (hrange : (g ⁻¹ᵁ U : Set X) = Set.range c.base) (φ : Γ(Y, U) ⟶ R) [IsIso φ]
    (hc : c ≫ g = Spec.map φ ≫ hU.fromSpec) : IsIso (g ∣_ U) := by
  let e : Spec R ≅ (g ⁻¹ᵁ U : Scheme.{u}) :=
    IsOpenImmersion.isoOfRangeEq c (g ⁻¹ᵁ U).ι (by rw [Scheme.Opens.range_ι]; exact hrange.symm)
  have he : e.hom ≫ (g ⁻¹ᵁ U).ι = c := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h1 : e.hom ≫ (g ∣_ U) = Spec.map φ ≫ hU.isoSpec.inv := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc]
    rw [morphismRestrict_ι, ← Category.assoc, he, hc, IsAffineOpen.isoSpec_inv_ι]
  have h2 : g ∣_ U = e.inv ≫ Spec.map φ ≫ hU.isoSpec.inv := by
    rw [← h1, Iso.inv_hom_id_assoc]
  rw [h2]
  infer_instance

section Chart

variable {k : Type u} [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k))

noncomputable abbrev chartAlgebra (U : Y.Opens) : Algebra k Γ(Y, U) :=
  ((q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra

theorem chart_finiteType [LocallyOfFiniteType q] {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := chartAlgebra q U
    Algebra.FiniteType k Γ(Y, U) := by
  have h1 : (q.appLE ⊤ U le_top).hom.FiniteType :=
    q.finiteType_appLE (isAffineOpen_top _) hU le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

theorem preimage_fromSpecStalk_genericPoint_eq_top [IsIntegral Y] (U : Y.Opens)
    (hUne : (U : Set Y).Nonempty) :
    (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U = ⊤ := by
  have hη : genericPoint Y ∈ U := ((genericPoint_spec Y).mem_open_set_iff U.2).mpr
    (by obtain ⟨y, hy⟩ := hUne; exact ⟨y, Set.mem_univ _, hy⟩)
  refine eq_top_iff.mpr fun pt _ => ?_
  have hsub : Subsingleton (PrimeSpectrum Y.functionField) := inferInstance
  have hpt : pt = IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y)) :=
    Subsingleton.elim (α := PrimeSpectrum Y.functionField) pt _
  change (Y.fromSpecStalk (genericPoint Y)).base pt ∈ U
  rw [hpt, Scheme.fromSpecStalk_closedPoint]
  exact hη

include q in

theorem chart_facts [IsIntegral Y] [LocallyOfFiniteType q] (U : Y.Opens) (hU : IsAffineOpen U)
    (hUne : (U : Set Y).Nonempty) :
    letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
    IsFractionRing Γ(Y, U) Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
        (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) ∧
      Module.Finite Γ(Y, U) (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) ∧
      IsDomain (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) ∧
      IsIntegrallyClosed (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) := by
  letI algL := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  haveI : Nonempty U := by obtain ⟨y, hy⟩ := hUne; exact ⟨⟨y, hy⟩⟩
  have hη : genericPoint Y ∈ U := ((genericPoint_spec Y).mem_open_set_iff U.2).mpr
    (by obtain ⟨y, hy⟩ := hUne; exact ⟨y, Set.mem_univ _, hy⟩)

  have htop : (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U = ⊤ :=
    preimage_fromSpecStalk_genericPoint_eq_top U hUne
  let eKL : Y.functionField ≅
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso (Y.presheaf.stalk (genericPoint Y))).symm ≪≫
      (Spec (Y.presheaf.stalk (genericPoint Y))).presheaf.mapIso (eqToIso htop).op
  have happ : (Y.fromSpecStalk (genericPoint Y)).app U =
      Y.presheaf.germ U (genericPoint Y) hη ≫ eKL.hom := by
    rw [Scheme.fromSpecStalk_app hη]
    simp only [eKL, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
    rw [show (homOfLE le_top : (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U ⟶ ⊤) = eqToHom htop from
      Subsingleton.elim _ _]
  haveI : IsFractionRing Γ(Y, U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  let eA : Y.functionField ≃ₐ[Γ(Y, U)]
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) :=
    AlgEquiv.ofRingEquiv (f := eKL.commRingCatIsoToRingEquiv) (fun a => by
      change eKL.hom (Y.germToFunctionField U a) = ((Y.fromSpecStalk (genericPoint Y)).app U) a
      rw [happ]
      rfl)

  letI := chartAlgebra q U
  haveI := chart_finiteType q hU
  have hfin : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Y.functionField) :=
    IsIntegralClosure.finite_of_finiteType k Γ(Y, U) Y.functionField Y.functionField
      (integralClosure Γ(Y, U) Y.functionField)
  exact integralClosure_transport eA hfin

end Chart

section Main

variable {k : Type u} [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k))
  [IsIntegral Y] [LocallyOfFiniteType q]

theorem chart (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
    ∃ cU : Spec (CommRingCat.of (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U))) ⟶
        (Y.fromSpecStalk (genericPoint Y)).normalization,
      IsOpenImmersion cU ∧
      ((Y.fromSpecStalk (genericPoint Y)).fromNormalization ⁻¹ᵁ U :
          Set (Y.fromSpecStalk (genericPoint Y)).normalization) = Set.range cU.base ∧
      cU ≫ (Y.fromSpecStalk (genericPoint Y)).fromNormalization =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (integralClosure Γ(Y, U)
          Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)))) ≫
          hU.fromSpec := by
  letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  refine ⟨(Y.fromSpecStalk (genericPoint Y)).normalizationOpenCover.f ⟨U, hU⟩,
    by exact (Y.fromSpecStalk (genericPoint Y)).normalizationOpenCover.map_prop ⟨U, hU⟩, ?_, ?_⟩
  · have h := (Y.fromSpecStalk (genericPoint Y)).fromNormalization_preimage ⟨U, hU⟩
    change (Y.fromSpecStalk (genericPoint Y)).fromNormalization ⁻¹ᵁ U = _ at h
    rw [h]
    rfl
  · exact (Y.fromSpecStalk (genericPoint Y)).ι_fromNormalization ⟨U, hU⟩

omit [LocallyOfFiniteType q] in

theorem exists_affine_mem (z : (Y.fromSpecStalk (genericPoint Y)).normalization) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U), (U : Set Y).Nonempty ∧
      (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base z ∈ U := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y)
    (x := (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base z) (U := ⊤) trivial
  exact ⟨U, hU, ⟨_, hzU⟩, hzU⟩

include q in

theorem isIntegrallyClosed_stalk (z : (Y.fromSpecStalk (genericPoint Y)).normalization) :
    IsIntegrallyClosed ((Y.fromSpecStalk (genericPoint Y)).normalization.presheaf.stalk z) := by
  obtain ⟨U, hU, hUne, hzU⟩ := exists_affine_mem (Y := Y) z
  obtain ⟨cU, hcUopen, hrange, -⟩ := chart (Y := Y) U hU
  have hfacts := chart_facts q U hU hUne
  obtain ⟨-, -, hdom, hic⟩ := hfacts
  letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  have hz : z ∈ Set.range cU.base := by rw [← hrange]; exact hzU
  obtain ⟨t, rfl⟩ := hz
  haveI := hcUopen
  haveI := hdom
  haveI := hic
  obtain ⟨e⟩ := stalk_iso_of_isOpenImmersion cU t
  have h1 := isIntegrallyClosed_stalk_Spec _ t
  exact IsIntegrallyClosed.of_equiv e.symm.commRingCatIsoToRingEquiv

include q in

theorem finite_algebraMap_chart (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
    (algebraMap Γ(Y, U) (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U))).Finite := by
  letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  by_cases hUne : (U : Set Y).Nonempty
  · have hfacts := chart_facts q U hU hUne
    obtain ⟨-, hfin, -, -⟩ := hfacts
    rw [RingHom.Finite]
    convert hfin
  · have hbot : U = ⊥ := by
      ext1
      exact Set.not_nonempty_iff_eq_empty.mp hUne
    haveI : Subsingleton Γ(Y, U) := subsingleton_sections_of_eq_bot Y hbot
    rw [RingHom.Finite]
    letI := (algebraMap Γ(Y, U) (integralClosure Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
        (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U))).toAlgebra
    haveI : Subsingleton (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) := Module.subsingleton Γ(Y, U) _
    exact Module.Finite.of_finite

include q in

theorem isFinite_fromNormalization :
    IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  rw [(Y.fromSpecStalk (genericPoint Y)).fromNormalization_app hU]
  have hfin := finite_algebraMap_chart q U hU
  have hiso : ((Y.fromSpecStalk (genericPoint Y)).normalizationObjIso hU).inv.hom.Finite :=
    RingHom.Finite.of_surjective _
      ((Y.fromSpecStalk (genericPoint Y)).normalizationObjIso
        hU).symm.commRingCatIsoToRingEquiv.surjective
  exact hiso.comp hfin

omit [LocallyOfFiniteType q] in

theorem surjective_fromNormalization :
    Function.Surjective (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base := by
  intro y
  have hcl : IsClosed (Set.range (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base) :=
    (Y.fromSpecStalk (genericPoint Y)).fromNormalization.isClosedMap.isClosed_range
  have hη : genericPoint Y ∈ Set.range (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base := by
    refine ⟨((Y.fromSpecStalk (genericPoint Y)).toNormalization).base (IsLocalRing.closedPoint _), ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact Scheme.fromSpecStalk_closedPoint
  have hgen : closure ({genericPoint Y} : Set Y) = Set.univ := genericPoint_spec Y
  have hdense : Dense (Set.range (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base) := by
    rw [dense_iff_closure_eq, ← Set.univ_subset_iff, ← hgen]
    exact closure_mono (Set.singleton_subset_iff.mpr hη)
  have : Set.range (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base = Set.univ := by
    rw [← hcl.closure_eq, hdense.closure_eq]
  obtain ⟨z, hz⟩ := (Set.eq_univ_iff_forall.mp this) y
  exact ⟨z, hz⟩

include q in

theorem height_comap_chart (U : Y.Opens) (hU : IsAffineOpen U) (hUne : (U : Set Y).Nonempty)
    (t : letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
      Spec (CommRingCat.of (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)))) :
    letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
    t.asIdeal.height = (t.asIdeal.comap (algebraMap Γ(Y, U) (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)))).height := by
  letI algL := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  have hfacts := chart_facts q U hU hUne
  obtain ⟨hfr, hfin, hdom, -⟩ := hfacts
  haveI := hdom
  haveI := hfin
  haveI : Nonempty U := by obtain ⟨y, hy⟩ := hUne; exact ⟨⟨y, hy⟩⟩
  letI := chartAlgebra q U
  haveI := chart_finiteType q hU
  letI algAbar : Algebra k (integralClosure Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) :=
    ((algebraMap Γ(Y, U) (integralClosure Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U))).comp
        (algebraMap k Γ(Y, U))).toAlgebra
  haveI : IsScalarTower k Γ(Y, U) (integralClosure Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : FaithfulSMul Γ(Y, U) (integralClosure Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b hab => ?_
    have := congrArg (fun x : integralClosure Γ(Y, U)
      Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U) =>
        (x : Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U)))
      hab
    exact @IsFractionRing.injective _ _ _ _ _ hfr a b this
  haveI : t.asIdeal.IsPrime := t.2
  exact height_eq_height_comap k _

include q in

theorem ringKrullDim_stalk_eq (z : (Y.fromSpecStalk (genericPoint Y)).normalization) :
    ringKrullDim ((Y.fromSpecStalk (genericPoint Y)).normalization.presheaf.stalk z) =
      ringKrullDim (Y.presheaf.stalk ((Y.fromSpecStalk (genericPoint Y)).fromNormalization.base z)) := by
  obtain ⟨U, hU, hUne, hzU⟩ := exists_affine_mem (Y := Y) z
  obtain ⟨cU, hcUopen, hrange, hcomp⟩ := chart (Y := Y) U hU
  letI := ((Y.fromSpecStalk (genericPoint Y)).app U).hom.toAlgebra
  have hz : z ∈ Set.range cU.base := by rw [← hrange]; exact hzU
  obtain ⟨t, rfl⟩ := hz
  haveI := hcUopen

  obtain ⟨e⟩ := stalk_iso_of_isOpenImmersion cU t
  rw [ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv, ringKrullDim_stalk_Spec]

  have hνt : (Y.fromSpecStalk (genericPoint Y)).fromNormalization.base (cU.base t) =
      hU.fromSpec.base ((Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) (integralClosure Γ(Y, U)
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U))))).base t) := by
    rw [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply]
  have hmem := hνt ▸ hzU
  have hstep : ringKrullDim (Y.presheaf.stalk
      ((Y.fromSpecStalk (genericPoint Y)).fromNormalization.base (cU.base t))) =
      ringKrullDim (Y.presheaf.stalk (hU.fromSpec.base ((Spec.map (CommRingCat.ofHom (algebraMap
        Γ(Y, U) (integralClosure Γ(Y, U) Γ(Spec (Y.presheaf.stalk (genericPoint Y)),
          (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U))))).base t))) := by
    rw [hνt]
  rw [hstep, ringKrullDim_stalk_eq_height hU _ hmem, primeIdealOf_fromSpec hU _ hmem, Spec.map_apply,
    height_comap_chart q U hU hUne t]
  rfl

include q in

theorem isIso_morphismRestrict_fromNormalization (W : Y.Opens)
    (hW : ∀ z ∈ W, IsIntegrallyClosed (Y.presheaf.stalk z)) :
    IsIso ((Y.fromSpecStalk (genericPoint Y)).fromNormalization ∣_ W) := by

  suffices h : ∀ V : (W : Scheme.{u}).affineOpens,
      IsIso (((Y.fromSpecStalk (genericPoint Y)).fromNormalization ∣_ W) ∣_
        (V : (W : Scheme.{u}).Opens)) by
    have := (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (f := (Y.fromSpecStalk (genericPoint Y)).fromNormalization ∣_ W)
      (fun V : (W : Scheme.{u}).affineOpens => (V : (W : Scheme.{u}).Opens))
      (iSup_affineOpens_eq_top _)).mpr (fun V => (MorphismProperty.isomorphisms.iff _).mpr (h V))
    exact (MorphismProperty.isomorphisms.iff _).mp this
  intro V

  rw [← MorphismProperty.isomorphisms.iff,
    (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict (Y.fromSpecStalk (genericPoint Y)).fromNormalization W V),
    MorphismProperty.isomorphisms.iff]
  have hU' : IsAffineOpen (W.ι ''ᵁ (V : (W : Scheme.{u}).Opens)) := V.2.image_of_isOpenImmersion W.ι
  have hU'W : W.ι ''ᵁ (V : (W : Scheme.{u}).Opens) ≤ W := Scheme.Opens.ι_image_le _ _
  generalize W.ι ''ᵁ (V : (W : Scheme.{u}).Opens) = U' at hU' hU'W
  by_cases hU'ne : (U' : Set Y).Nonempty
  ·
    obtain ⟨cU, hcUopen, hrange, hcomp⟩ := chart (Y := Y) U' hU'
    have hfacts := chart_facts q U' hU' hU'ne
    obtain ⟨hfr, -, -, -⟩ := hfacts
    letI := ((Y.fromSpecStalk (genericPoint Y)).app U').hom.toAlgebra
    haveI := hcUopen
    haveI : Nonempty U' := by obtain ⟨y, hy⟩ := hU'ne; exact ⟨⟨y, hy⟩⟩
    haveI : IsIntegrallyClosed Γ(Y, U') := by
      refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
      let P : Spec Γ(Y, U') := ⟨p, hp.isPrime⟩
      have hmem : hU'.fromSpec.base P ∈ U' := by
        have : hU'.fromSpec.base P ∈ Set.range hU'.fromSpec.base := ⟨P, rfl⟩
        rwa [IsAffineOpen.range_fromSpec] at this
      exact isIntegrallyClosed_localization_of_stalk hU' P hmem (hW _ (hU'W hmem))
    haveI := hfr
    have hbij : Function.Bijective (algebraMap Γ(Y, U') (integralClosure Γ(Y, U')
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U'))) :=
      bijective_algebraMap_integralClosure
    haveI : IsIso (CommRingCat.ofHom (algebraMap Γ(Y, U') (integralClosure Γ(Y, U')
        Γ(Spec (Y.presheaf.stalk (genericPoint Y)), (Y.fromSpecStalk (genericPoint Y)) ⁻¹ᵁ U')))) :=
      (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
    exact isIso_morphismRestrict_of_chart _ hU' cU hrange (CommRingCat.ofHom _) hcomp
  ·
    have hempty : (U' : Set Y) = ∅ := Set.not_nonempty_iff_eq_empty.mp hU'ne
    haveI : IsEmpty (U' : Scheme.{u}) := ⟨fun x => by
      have hx : (x.1 : Y) ∈ (U' : Set Y) := x.2
      rw [hempty] at hx
      exact hx⟩
    infer_instance

include q in
theorem main :
    ∃ (Y' : Scheme.{u}) (ν : Y' ⟶ Y), IsIntegral Y' ∧
      (∀ z : Y', IsIntegrallyClosed (Y'.presheaf.stalk z)) ∧ IsFinite ν ∧
      Function.Surjective ν.base ∧
      (∀ z : Y', ringKrullDim (Y'.presheaf.stalk z) =
        ringKrullDim (Y.presheaf.stalk (ν.base z))) ∧
      ∀ U : Y.Opens, (∀ z ∈ U, IsIntegrallyClosed (Y.presheaf.stalk z)) → IsIso (ν ∣_ U) :=
  ⟨(Y.fromSpecStalk (genericPoint Y)).normalization, (Y.fromSpecStalk (genericPoint Y)).fromNormalization,
    inferInstance, isIntegrallyClosed_stalk q, isFinite_fromNormalization q,
    surjective_fromNormalization (Y := Y), ringKrullDim_stalk_eq q,
    isIso_morphismRestrict_fromNormalization q⟩

end Main

end AlgebraicGeometry.NormalizationOfVariety

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral.AlgebraicGeometry in

theorem solution
    (k : Type u) [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k))
    [IsIntegral Y] [LocallyOfFiniteType q] :
    ∃ (Y' : Scheme.{u}) (ν : Y' ⟶ Y), IsIntegral Y' ∧
      (∀ z : Y', IsIntegrallyClosed (Y'.presheaf.stalk z)) ∧ IsFinite ν ∧
      Function.Surjective ν.base ∧
      (∀ z : Y', ringKrullDim (Y'.presheaf.stalk z) =
        ringKrullDim (Y.presheaf.stalk (ν.base z))) ∧
      ∀ U : Y.Opens, (∀ z ∈ U, IsIntegrallyClosed (Y.presheaf.stalk z)) → IsIso (ν ∣_ U) :=
  AlgebraicGeometry.NormalizationOfVariety.main q

end S_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral (solution)
