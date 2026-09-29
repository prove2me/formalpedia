-- Prove2me | solution 1 for AlgebraicGeometry.isFinite_and_flat_and_surjective_of_locallyQuasiFinite_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ce33f2f8-6878-51fe-8a58-5cd7bd3d56a7

import Mathlib
import Theorems.Thm_Ideal_height_eq_height_under_of_finiteType_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_ringKrullDim_stalk_quotient_eq_zero
import Theorems.Thm_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isFinite_and_flat_and_surjective_of_locallyQuasiFinite_of_smoothOfRelativeDimension
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1600000

namespace QFFlatSurj

p2m_open "Algebra CategoryTheory.Algebra"

theorem height_eq_height_under_of_quasiFiniteAt
    (k A B : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B]
    (q : Ideal B) [q.IsPrime] [Algebra.QuasiFiniteAt A q] :
    q.height = (q.under A).height := by
  haveI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType k A B
  obtain ⟨S', hfg, r, hrq, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := A) q

  haveI : Module.Finite A S' := ⟨(Submodule.fg_top _).mpr hfg⟩
  haveI : Algebra.IsIntegral A S' := Algebra.IsIntegral.of_finite A S'
  haveI : IsDomain S' := inferInstance
  letI : Algebra k S' := inferInstance
  haveI : IsScalarTower k A S' := inferInstance
  haveI : Algebra.FiniteType k S' := Algebra.FiniteType.trans (S := A) inferInstance
    inferInstance
  haveI : FaithfulSMul A S' := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    apply (faithfulSMul_iff_algebraMap_injective A B).mp inferInstance
    have := congrArg (fun s : S' => (s : B)) hab
    simpa using this

  let q₁ : Ideal S' := q.under S'
  haveI : q₁.IsPrime := Ideal.IsPrime.under S' q

  have h1 : q₁.height = (q₁.under A).height :=
    Ideal.height_eq_height_under_of_finiteType_of_isIntegral k A S' q₁
  have h1' : q₁.under A = q.under A := by
    rw [Ideal.under_under]

  have hrB : ((r : B)) ∉ q := hrq
  let Br : Type u := Localization.Away (S'.val.toRingHom r)
  letI : Algebra S' Br := inferInstance
  haveI : IsScalarTower S' B Br := inferInstance

  let φ : Localization.Away r →ₐ[S'] Br :=
    { Localization.awayMap S'.val.toRingHom r with
      commutes' := fun s => by
        show Localization.awayMap S'.val.toRingHom r (algebraMap S' (Localization.Away r) s) =
          algebraMap B Br (S'.val.toRingHom s)
        simp only [Localization.awayMap, IsLocalization.Away.map]
        exact IsLocalization.map_eq _ s }
  let eφ : Localization.Away r ≃ₐ[S'] Br := AlgEquiv.ofBijective φ hbij
  haveI : IsLocalization (Submonoid.powers r) Br :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) eφ
  haveI : IsLocalization (Submonoid.powers (S'.val.toRingHom r)) Br := inferInstance

  let J : Ideal Br := q.map (algebraMap B Br)
  have hdisj : Disjoint (Submonoid.powers (S'.val.toRingHom r) : Set B) (q : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hmem
    exact hrB ((inferInstance : q.IsPrime).mem_of_pow_mem n hmem)
  haveI : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Br q inferInstance hdisj
  have hJB : J.under B = q := IsLocalization.comap_map_of_isPrime_disjoint _ Br inferInstance hdisj
  have hJS' : J.under S' = q₁ := by
    rw [← Ideal.under_under (B := B) J, hJB]
  have h2 : q.height = q₁.height := by
    rw [← hJB, IsLocalization.height_under (Submonoid.powers (S'.val.toRingHom r)) J, ← hJS',
      IsLocalization.height_under (Submonoid.powers r) J]
  rw [h2, h1, h1']

section Topology

open TopologicalSpace Topology Order

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def imageIC (f : X → Y) (hf : Continuous f) (hc : IsClosedMap f) (T : IrreducibleCloseds X) :
    IrreducibleCloseds Y where
  carrier := f '' (T : Set X)
  isIrreducible' := T.isIrreducible.image f hf.continuousOn
  isClosed' := hc _ T.isClosed

@[scoped simp] theorem coe_imageIC (f : X → Y) (hf : Continuous f) (hc : IsClosedMap f) (T : IrreducibleCloseds X) :
    (imageIC f hf hc T : Set Y) = f '' (T : Set X) := rfl

theorem imageIC_strictMono [QuasiSober X] [T0Space Y] (f : X → Y) (hf : Continuous f) (hc : IsClosedMap f)
    (hfib : ∀ y, IsDiscrete (f ⁻¹' {y})) : StrictMono (imageIC f hf hc) := by
  intro T T' hlt
  have hle : imageIC f hf hc T ≤ imageIC f hf hc T' := by
    change f '' (T : Set X) ⊆ f '' (T' : Set X)
    exact Set.image_mono hlt.le
  refine lt_of_le_of_ne hle ?_
  intro heq
  have heq' : f '' (T : Set X) = f '' (T' : Set X) := congrArg (fun Z : IrreducibleCloseds Y => (Z : Set Y)) heq
  have hη : IsGenericPoint T.isIrreducible.genericPoint (T : Set X) :=
    T.isIrreducible.isGenericPoint_genericPoint T.isClosed
  have hη' : IsGenericPoint T'.isIrreducible.genericPoint (T' : Set X) :=
    T'.isIrreducible.isGenericPoint_genericPoint T'.isClosed
  have hfη : IsGenericPoint (f T.isIrreducible.genericPoint) (f '' (T : Set X)) := by
    have := hη.image hf
    rwa [(hc _ T.isClosed).closure_eq] at this
  have hfη' : IsGenericPoint (f T'.isIrreducible.genericPoint) (f '' (T' : Set X)) := by
    have := hη'.image hf
    rwa [(hc _ T'.isClosed).closure_eq] at this
  rw [heq'] at hfη
  have hff : f T.isIrreducible.genericPoint = f T'.isIrreducible.genericPoint := hfη.eq hfη'

  have hmem : T.isIrreducible.genericPoint ∈ (T' : Set X) := hlt.le hη.mem
  have hspec : T'.isIrreducible.genericPoint ⤳ T.isIrreducible.genericPoint := hη'.specializes hmem
  let F : Set X := f ⁻¹' {f T'.isIrreducible.genericPoint}
  have hηF : T.isIrreducible.genericPoint ∈ F := by show f _ ∈ ({_} : Set Y); rw [hff]; rfl
  have hη'F : T'.isIrreducible.genericPoint ∈ F := rfl
  haveI : DiscreteTopology F := isDiscrete_iff_discreteTopology.mp (hfib _)
  have hspecF : (⟨_, hη'F⟩ : F) ⤳ (⟨_, hηF⟩ : F) := (subtype_specializes_iff _ _).mpr hspec
  have heqpt : T'.isIrreducible.genericPoint = T.isIrreducible.genericPoint :=
    congrArg Subtype.val (specializes_iff_eq.mp hspecF)
  apply hlt.ne
  apply IrreducibleCloseds.ext
  rw [← hη.def, ← hη'.def, heqpt]

theorem add_one_le_topologicalKrullDim [QuasiSober X] [T0Space Y] [IrreducibleSpace Y]
    (f : X → Y) (hf : Continuous f) (hc : IsClosedMap f) (hfib : ∀ y, IsDiscrete (f ⁻¹' {y}))
    (hns : ¬ Function.Surjective f) (n : ℕ) (hn : (n : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ((n + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim Y := by
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hn
  let top : IrreducibleCloseds Y := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  let l' : LTSeries (IrreducibleCloseds Y) := l.map (imageIC f hf hc) (imageIC_strictMono f hf hc hfib)
  have hlast : l'.last < top := by
    refine lt_of_le_of_ne (fun y _ => Set.mem_univ y) ?_
    intro h
    apply hns
    have h' : f '' ((l.last : IrreducibleCloseds X) : Set X) = Set.univ :=
      congrArg (fun Z : IrreducibleCloseds Y => (Z : Set Y)) h
    intro y
    obtain ⟨x, -, rfl⟩ := (h'.symm ▸ Set.mem_univ y : y ∈ f '' _)
    exact ⟨x, rfl⟩
  refine Order.le_krullDim_iff.mpr ⟨l'.snoc top hlast, ?_⟩
  simp [l', LTSeries.map, hl]

theorem surjective_of_topologicalKrullDim [QuasiSober X] [T0Space Y] [IrreducibleSpace Y]
    (f : X → Y) (hf : Continuous f) (hc : IsClosedMap f) (hfib : ∀ y, IsDiscrete (f ⁻¹' {y}))
    (n : ℕ) (hX : (n : WithBot ℕ∞) ≤ topologicalKrullDim X) (hY : topologicalKrullDim Y ≤ n) :
    Function.Surjective f := by
  by_contra hns
  have h := (add_one_le_topologicalKrullDim f hf hc hfib hns n hX).trans hY
  have : n + 1 ≤ n := by exact_mod_cast h
  omega

end Topology

section Schemes

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

noncomputable def secAlg (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem appLE_comp_secAlg (fY : Y ⟶ Spec (CommRingCat.of K)) (φ : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) :
    (φ.appLE U V e).hom.comp (secAlg fY U) = secAlg (φ ≫ fY) V := by
  unfold secAlg
  rw [← RingHom.comp_assoc]
  congr 1
  exact congrArg (fun g => g.hom) (Scheme.Hom.appLE_comp_appLE φ fY ⊤ U V le_top e)

theorem appLE_injective_of_surjective [IsIntegral X] [IsIntegral Y] (φ : X ⟶ Y) [Surjective φ]
    (U : Y.Opens) (V : X.Opens) [hV : Nonempty V] (e : V ≤ φ ⁻¹ᵁ U) :
    Function.Injective (φ.appLE U V e).hom := by

  have hξV : genericPoint X ∈ V := by
    obtain ⟨⟨v, hv⟩⟩ := hV
    exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨v, trivial, hv⟩
  have hφξ : φ.base (genericPoint X) = genericPoint Y := by
    have h1 := (genericPoint_spec X).image φ.continuous
    have h1' : IsGenericPoint (φ.base (genericPoint X)) (closure (Set.range φ.base)) := by
      simpa [Set.image_univ] using h1
    rw [φ.surjective.range_eq, closure_univ] at h1'
    exact h1'.eq (genericPoint_spec Y)

  have hunit : ∀ r : Y.presheaf.stalk (φ.base (genericPoint X)), r ≠ 0 → IsUnit r := by
    rw [hφξ]
    intro r hr
    exact isUnit_iff_ne_zero.mpr hr
  have hinj₂ : Function.Injective (φ.stalkMap (genericPoint X)).hom := by
    intro r s hrs
    by_contra hne
    have hu := hunit (r - s) (sub_ne_zero.mpr hne)
    have h0 : (φ.stalkMap (genericPoint X)).hom (r - s) = 0 := by rw [map_sub, hrs, sub_self]
    exact (hu.map (φ.stalkMap (genericPoint X)).hom).ne_zero h0
  have hinj₁ : Function.Injective (Y.presheaf.germ U (φ.base (genericPoint X)) (e hξV)).hom :=
    germ_injective_of_isIntegral Y (φ.base (genericPoint X)) (e hξV)

  have hcomp : φ.appLE U V e ≫ X.presheaf.germ V (genericPoint X) hξV =
      Y.presheaf.germ U (φ.base (genericPoint X)) (e hξV) ≫ φ.stalkMap (genericPoint X) := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res]
  have key : (X.presheaf.germ V (genericPoint X) hξV).hom.comp (φ.appLE U V e).hom =
      (φ.stalkMap (genericPoint X)).hom.comp (Y.presheaf.germ U (φ.base (genericPoint X)) (e hξV)).hom := by
    have := congrArg (fun g => g.hom) hcomp
    simpa only [CommRingCat.hom_comp] using this
  have hinj : Function.Injective
      ((X.presheaf.germ V (genericPoint X) hξV).hom.comp (φ.appLE U V e).hom) := by
    rw [key, RingHom.coe_comp]; exact hinj₂.comp hinj₁
  rw [RingHom.coe_comp] at hinj
  exact Function.Injective.of_comp hinj

theorem ringKrullDim_stalk_eq [IsIntegral X] [IsIntegral Y]
    (fY : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType fY]
    (φ : X ⟶ Y) [LocallyOfFiniteType (φ ≫ fY)] [LocallyQuasiFinite φ] [Surjective φ] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (φ.base x)) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := φ.base x) (U := ⊤) trivial
  have hxU' : x ∈ φ ⁻¹ᵁ U := hxU
  obtain ⟨V, hV, hxV, hVsub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := φ ⁻¹ᵁ U) hxU'
  have hVU : V ≤ φ ⁻¹ᵁ U := hVsub
  haveI : Nonempty U := ⟨⟨φ.base x, hxU⟩⟩
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let A : Type u := Γ(Y, U)
  let B : Type u := Γ(X, V)
  letI : Algebra K A := (secAlg fY U).toAlgebra
  letI : Algebra K B := (secAlg (φ ≫ fY) V).toAlgebra
  letI : Algebra A B := (φ.appLE U V hVU).hom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq' (appLE_comp_secAlg fY φ U V hVU).symm
  have hftA : (secAlg fY U).FiniteType :=
    (fY.finiteType_appLE (U := ⊤) (isAffineOpen_top _) hU le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  have hftB : (secAlg (φ ≫ fY) V).FiniteType :=
    ((φ ≫ fY).finiteType_appLE (U := ⊤) (isAffineOpen_top _) hV le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  haveI : Algebra.FiniteType K A := hftA
  haveI : Algebra.FiniteType K B := hftB
  let q : Ideal B := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let p : Ideal A := (hU.primeIdealOf ⟨φ.base x, hxU⟩).asIdeal
  haveI : Algebra.QuasiFiniteAt A q := (φ.quasiFiniteAt x).quasiFiniteAt hV hU hVU hxV
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (appLE_injective_of_surjective φ U V hVU)
  have hheight : q.height = (q.under A).height := height_eq_height_under_of_quasiFiniteAt K A B q
  have hpq : q.under A = p := by
    have hc := IsAffineOpen.comap_primeIdealOf_appLE (f := φ) U hU V hV hVU hxV
    exact congrArg PrimeSpectrum.asIdeal hc
  let xV : V := ⟨x, hxV⟩
  let yU : U := ⟨φ.base x, hxU⟩
  letI : Algebra B (X.presheaf.stalk (xV : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf xV
  letI : Algebra A (Y.presheaf.stalk (yU : Y)) := TopCat.Presheaf.algebra_section_stalk Y.presheaf yU
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (xV : X)) q := hV.isLocalization_stalk xV
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk (yU : Y)) p := hU.isLocalization_stalk yU
  show ringKrullDim (X.presheaf.stalk (xV : X)) = ringKrullDim (Y.presheaf.stalk (yU : Y))
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk (xV : X)),
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Y.presheaf.stalk (yU : Y)), hheight, hpq]

theorem flat [IsIntegral X] [IsIntegral Y]
    (fY : Y ⟶ Spec (CommRingCat.of K)) [Smooth fY]
    (φ : X ⟶ Y) [Smooth (φ ≫ fY)] [LocallyQuasiFinite φ] [Surjective φ] : Flat φ := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (φ ≫ fY)
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian fY
  refine Flat.of_stalkMap φ fun x => ?_
  haveI hx : IsRegularLocalRing (X.presheaf.stalk x) := Smooth.isRegularLocalRing_stalk (f := φ ≫ fY) x
  haveI hy : IsRegularLocalRing (Y.presheaf.stalk (φ.base x)) :=
    Smooth.isRegularLocalRing_stalk (f := fY) (φ.base x)
  letI alg : Algebra (Y.presheaf.stalk (φ.base x)) (X.presheaf.stalk x) := (φ.stalkMap x).hom.toAlgebra
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (φ.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap x).hom)
  have hfib : ringKrullDim ((X.presheaf.stalk x) ⧸
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (φ.base x))).map
        (algebraMap (Y.presheaf.stalk (φ.base x)) (X.presheaf.stalk x))) = 0 :=
    AlgebraicGeometry.LocallyQuasiFinite.ringKrullDim_stalk_quotient_eq_zero φ x
  have hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (φ.base x)) :=
    ringKrullDim_stalk_eq fY φ x
  exact Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
    (Y.presheaf.stalk (φ.base x)) (X.presheaf.stalk x) hfib hdim

theorem main (fX : X ⟶ Spec (CommRingCat.of K)) (fY : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y] [IsProper fX] [IsSeparated fY]
    (g : ℕ) [SmoothOfRelativeDimension g fX] [SmoothOfRelativeDimension g fY]
    (φ : X ⟶ Y) (hφ : φ ≫ fY = fX) [LocallyQuasiFinite φ] :
    IsFinite φ ∧ Flat φ ∧ Surjective φ := by
  subst hφ
  haveI : Smooth (φ ≫ fY) := SmoothOfRelativeDimension.smooth g _
  haveI : Smooth fY := SmoothOfRelativeDimension.smooth g _
  haveI : IsProper φ := IsProper.of_comp φ fY
  haveI : IsFinite φ := .of_isProper_of_locallyQuasiFinite φ
  have hX : ((g : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X :=
    SmoothOfRelativeDimension.le_topologicalKrullDim (φ ≫ fY) g
  have hY : topologicalKrullDim Y ≤ g := SmoothOfRelativeDimension.topologicalKrullDim_le fY g
  have hsurj : Function.Surjective φ :=
    surjective_of_topologicalKrullDim φ φ.continuous φ.isClosedMap
      (fun y => φ.isDiscrete_preimage_singleton y) g hX hY
  haveI : Surjective φ := ⟨hsurj⟩
  exact ⟨inferInstance, flat fY φ, inferInstance⟩

end Schemes

end QFFlatSurj
p2m_reactivate "P2MW.S_AlgebraicGeometry_isFinite_and_flat_and_surjective_of_locallyQuasiFinite_of_smoothOfRelativeDimension.QFFlatSurj"

theorem solution
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of K)) (fY : Y ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsIntegral Y] [IsProper fX] [IsSeparated fY]
    (g : ℕ) [SmoothOfRelativeDimension g fX] [SmoothOfRelativeDimension g fY]
    (φ : X ⟶ Y) (hφ : φ ≫ fY = fX) [LocallyQuasiFinite φ] :
    IsFinite φ ∧ Flat φ ∧ Surjective φ :=
  QFFlatSurj.main fX fY g φ hφ

end S_AlgebraicGeometry_isFinite_and_flat_and_surjective_of_locallyQuasiFinite_of_smoothOfRelativeDimension
end P2MW
export P2MW.S_AlgebraicGeometry_isFinite_and_flat_and_surjective_of_locallyQuasiFinite_of_smoothOfRelativeDimension (solution)
