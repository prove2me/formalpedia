-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/126e113d-422e-5a65-9d6c-b1b00dcb5066

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension CerednikDrinfeld.QM AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

noncomputable section

namespace PushAtUnit28

section Plumbing

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

theorem appLE_specMap_fromSpec {S : CommRingCat.{u}} (θ : Γ(X, U) ⟶ S)
    (h : ⊤ ≤ (Spec.map θ ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Spec.map θ ≫ hU.fromSpec).appLE U ⊤ h ≫ (Scheme.ΓSpecIso S).hom = θ := by
  have h1 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [IsAffineOpen.fromSpec_preimage_self]
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map θ) hU.fromSpec U ⊤ ⊤ h1 le_top]
  have h2 : hU.fromSpec.appLE U ⊤ h1 = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    rfl
  have h3 : (Spec.map θ).appLE ⊤ ⊤ le_top = (Spec.map θ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [h2, h3, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem eq_specMap_appLE_comp_fromSpec {R : CommRingCat.{u}} (p : Spec R ⟶ X) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    p = Spec.map (p.appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom) ≫ hU.fromSpec := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec p hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem specMap_comp_fromSpec_injective {R : CommRingCat.{u}} (θ θ' : Γ(X, U) ⟶ R)
    (h : Spec.map θ ≫ hU.fromSpec = Spec.map θ' ≫ hU.fromSpec) : θ = θ' := by
  apply Spec.map_injective
  rw [← IsAffineOpen.isoSpec_inv_ι] at h
  have h' : (Spec.map θ ≫ hU.isoSpec.inv) ≫ U.ι = (Spec.map θ' ≫ hU.isoSpec.inv) ≫ U.ι := by
    simpa only [Category.assoc] using h
  exact (cancel_mono hU.isoSpec.inv).1 ((cancel_mono U.ι).1 h')

end Plumbing

section OnePoint

variable (K : Type u) [Field K] (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]

theorem primeSpectrum_subsingleton : Subsingleton (PrimeSpectrum (TrivSqZeroExt K M)) := by
  refine ⟨fun P Q => ?_⟩
  have key : ∀ (P : PrimeSpectrum (TrivSqZeroExt K M)) (z : TrivSqZeroExt K M), z ∈ P.asIdeal ↔ z.fst = 0 := by
    intro P z
    constructor
    · intro hz
      by_contra hne
      have hu : IsUnit z := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz hu)
    · intro hz
      have hz' : z = TrivSqZeroExt.inr z.snd := by
        ext <;> simp [hz]
      have h2 : z * z ∈ P.asIdeal := by
        rw [hz', TrivSqZeroExt.inr_mul_inr]
        exact P.asIdeal.zero_mem
      exact (P.isPrime.mem_or_mem h2).elim id id
  ext z
  rw [key P z, key Q z]

end OnePoint

section RingMap

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A] (ev : A →+* K)
  (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
  (D : ↥(Algebra.PointDerivations K A ev M))

def chi : A →+* TrivSqZeroExt K M where
  toFun r := TrivSqZeroExt.inl (ev r) + TrivSqZeroExt.inr (D.1 r)
  map_one' := by
    apply TrivSqZeroExt.ext <;>
      simp [Algebra.PointDerivations.apply_one D.2]
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul]
      rw [Algebra.PointDerivations.apply_mul D.2 a b, op_smul_eq_smul, add_comm]
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext <;> simp [add_add_add_comm]

@[scoped simp] theorem chi_apply (r : A) : chi ev M D r = TrivSqZeroExt.inl (ev r) + TrivSqZeroExt.inr (D.1 r) := rfl

theorem fst_chi (r : A) : (chi ev M D r).fst = ev r := by simp

theorem snd_chi (r : A) : (chi ev M D r).snd = D.1 r := by simp

theorem fstHom_comp_chi : (TrivSqZeroExt.fstHom K K M).toRingHom.comp (chi ev M D) = ev := by
  ext r; exact fst_chi ev M D r

theorem eq_chi (χ : A →+* TrivSqZeroExt K M) (h1 : ∀ a, (χ a).fst = ev a) (h2 : ∀ a, (χ a).snd = D.1 a) :
    χ = chi ev M D := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · rw [h1, fst_chi]
  · rw [h2, snd_chi]

end RingMap

section Engine

variable {K : Type u} [Field K] {X : Scheme.{u}}

abbrev evP (U : X.Opens) (eP : Spec (CommRingCat.of K) ⟶ (U : Scheme.{u})) : Γ(X, U) →+* K :=
  (U.topIso.inv ≫ eP.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom

theorem eP_eq (U : X.Opens) (hU : IsAffineOpen U) (eP : Spec (CommRingCat.of K) ⟶ (U : Scheme.{u})) :
    eP ≫ U.ι = Spec.map (CommRingCat.ofHom (evP U eP)) ≫ hU.fromSpec := by
  have hι : ⊤ ≤ (eP ≫ U.ι) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
    exact le_top
  have hePι := eq_specMap_appLE_comp_fromSpec hU (eP ≫ U.ι) hι
  have happ : (eP ≫ U.ι).appLE U ⊤ hι = U.topIso.inv ≫ eP.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE eP U.ι U ⊤ ⊤ (by rw [Scheme.Opens.ι_preimage_self]) le_top]
    congr 1
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have hev_hom : CommRingCat.ofHom (evP U eP) = (eP ≫ U.ι).appLE U ⊤ hι ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [happ, Category.assoc]; rfl
  rw [hev_hom]; exact hePι

variable (U : X.Opens) (hU : IsAffineOpen U) (eP : Spec (CommRingCat.of K) ⟶ (U : Scheme.{u}))
  (ψ : X ⟶ X) (hψe : (eP ≫ U.ι) ≫ ψ = eP ≫ U.ι)
  (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
  (χ : Γ(X, U) →+* TrivSqZeroExt K M) (hχ : (TrivSqZeroExt.fstHom K K M).toRingHom.comp χ = evP U eP)

include hψe hχ

theorem fstSpec_comp_pushed :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom) ≫
        (Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec ≫ ψ) = eP ≫ U.ι := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hχ, ← Category.assoc,
    ← eP_eq U hU eP, hψe]

theorem le_preimage_pushed : ⊤ ≤ (Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec ≫ ψ) ⁻¹ᵁ U := by
  intro y _
  haveI : Subsingleton ↥(Spec (CommRingCat.of (TrivSqZeroExt K M))) := primeSpectrum_subsingleton K M
  let pt : ↥(Spec (CommRingCat.of K)) := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum K)
  have hy : y = (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom)).base pt :=
    Subsingleton.elim _ _
  show (Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec ≫ ψ).base y ∈ (U : Set X)
  rw [hy]
  have h := congrArg (fun φ : Spec (CommRingCat.of K) ⟶ X => φ.base pt)
    (fstSpec_comp_pushed U hU eP ψ hψe M χ hχ)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h ⊢
  rw [h, ← Scheme.Opens.range_ι U]
  exact ⟨_, rfl⟩

def chi' : Γ(X, U) →+* TrivSqZeroExt K M :=
  ((Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec ≫ ψ).appLE U ⊤ (le_preimage_pushed U hU eP ψ hψe M χ hχ) ≫
    (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K M))).hom).hom

theorem specMap_chi' :
    Spec.map (CommRingCat.ofHom (chi' U hU eP ψ hψe M χ hχ)) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec ≫ ψ := by
  change Spec.map ((Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec ≫ ψ).appLE U ⊤ _ ≫
    (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K M))).hom) ≫ hU.fromSpec = _
  exact (eq_specMap_appLE_comp_fromSpec hU _ _).symm

theorem fstHom_comp_chi' :
    (TrivSqZeroExt.fstHom K K M).toRingHom.comp (chi' U hU eP ψ hψe M χ hχ) = evP U eP := by
  have h : Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom K K M).toRingHom.comp (chi' U hU eP ψ hψe M χ hχ))) ≫
      hU.fromSpec = Spec.map (CommRingCat.ofHom (evP U eP)) ≫ hU.fromSpec := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, specMap_chi' U hU eP ψ hψe M χ hχ, ← eP_eq U hU eP]
    exact fstSpec_comp_pushed U hU eP ψ hψe M χ hχ
  exact congrArg (fun f => f.hom) (specMap_comp_fromSpec_injective hU _ _ h)

theorem chi'_unique (χ'' : Γ(X, U) →+* TrivSqZeroExt K M)
    (h : Spec.map (CommRingCat.ofHom χ'') ≫ hU.fromSpec = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec ≫ ψ) :
    χ'' = chi' U hU eP ψ hψe M χ hχ := by
  have := specMap_comp_fromSpec_injective hU (CommRingCat.ofHom χ'')
    (CommRingCat.ofHom (chi' U hU eP ψ hψe M χ hχ)) (by rw [h, specMap_chi' U hU eP ψ hψe M χ hχ])
  exact congrArg (fun f => f.hom) this

end Engine

end PushAtUnit28
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt.PushAtUnit28"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt.PushAtUnit28"

noncomputable section

namespace PushAtUnit28

section Deriv

variable {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
  (U : X.Opens) (hU : IsAffineOpen U) (eP : Spec (CommRingCat.of K) ⟶ (U : Scheme.{u}))
  (heP : eP ≫ U.ι ≫ x = 𝟙 _)
  (ψ : X ⟶ X) (hψ : ψ ≫ x = x) (hψe : (eP ≫ U.ι) ≫ ψ = eP ≫ U.ι)

theorem fromSpec_comp_base :
    letI := algebraOfHom x U
    hU.fromSpec ≫ x = Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U))) := by
  letI := algebraOfHom x U
  have := IsAffineOpen.SpecMap_appLE_fromSpec x (isAffineOpen_top _) hU (le_top : U ≤ x ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at this
  exact this.symm

include hU heP in

theorem evP_algebraMap (c : K) :
    letI := algebraOfHom x U
    evP U eP (algebraMap K Γ(X, U) c) = c := by
  letI := algebraOfHom x U
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U)) ≫ CommRingCat.ofHom (evP U eP)) = Spec.map (𝟙 _) := by
    rw [Spec.map_comp, Spec.map_id, ← fromSpec_comp_base x U hU, ← Category.assoc, ← eP_eq U hU eP,
      Category.assoc, heP]
  have h2 := Spec.map_injective h1
  have := congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f.hom c) h2
  simpa using this

variable (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]

include heP hψ hψe in

theorem chi'_comp_algebraMap (χ : Γ(X, U) →+* TrivSqZeroExt K M)
    (hχ : (TrivSqZeroExt.fstHom K K M).toRingHom.comp χ = evP U eP)
    (hχK : letI := algebraOfHom x U; χ.comp (algebraMap K Γ(X, U)) = algebraMap K (TrivSqZeroExt K M)) :
    letI := algebraOfHom x U
    (chi' U hU eP ψ hψe M χ hχ).comp (algebraMap K Γ(X, U)) = algebraMap K (TrivSqZeroExt K M) := by
  letI := algebraOfHom x U
  have h : Spec.map (CommRingCat.ofHom ((chi' U hU eP ψ hψe M χ hχ).comp (algebraMap K Γ(X, U)))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K M))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← fromSpec_comp_base x U hU, ← Category.assoc,
      specMap_chi' U hU eP ψ hψe M χ hχ, Category.assoc, Category.assoc, hψ, fromSpec_comp_base x U hU,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hχK]
  exact congrArg (fun f => f.hom) (Spec.map_injective h)

include heP hψ hψe in

def deriv (D : letI := algebraOfHom x U; ↥(Algebra.PointDerivations K Γ(X, U) (evP U eP) M)) :
    letI := algebraOfHom x U; ↥(Algebra.PointDerivations K Γ(X, U) (evP U eP) M) := by
  letI := algebraOfHom x U
  let χ' := chi' U hU eP ψ hψe M (chi (evP U eP) M D) (fstHom_comp_chi (evP U eP) M D)
  have hfst : ∀ a, (χ' a).fst = evP U eP a := fun a =>
    congrArg (fun f : Γ(X, U) →+* K => f a) (fstHom_comp_chi' U hU eP ψ hψe M (chi (evP U eP) M D) (fstHom_comp_chi (evP U eP) M D))
  have hK : ∀ c : K, χ' (algebraMap K Γ(X, U) c) = algebraMap K (TrivSqZeroExt K M) c := fun c =>
    congrArg (fun f : K →+* TrivSqZeroExt K M => f c)
      (chi'_comp_algebraMap x U hU eP heP ψ hψ hψe M (chi (evP U eP) M D) (fstHom_comp_chi (evP U eP) M D)
        (by
          refine RingHom.ext fun c => TrivSqZeroExt.ext ?_ ?_
          · rw [RingHom.comp_apply, fst_chi, evP_algebraMap x U hU eP heP, TrivSqZeroExt.algebraMap_eq_inl,
              TrivSqZeroExt.fst_inl]
          · simp [Algebra.PointDerivations.apply_algebraMap D.2, TrivSqZeroExt.algebraMap_eq_inl]))
  refine ⟨{ toFun := fun a => (χ' a).snd
            map_add' := fun a b => by simp only [map_add, TrivSqZeroExt.snd_add]
            map_smul' := fun c a => ?_ }, ?_⟩
  · simp only [RingHom.id_apply, Algebra.smul_def, map_mul, TrivSqZeroExt.snd_mul, hK, hfst,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, add_zero]
  · intro a b
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, TrivSqZeroExt.snd_mul, hfst, op_smul_eq_smul]

theorem deriv_apply (D : letI := algebraOfHom x U; ↥(Algebra.PointDerivations K Γ(X, U) (evP U eP) M)) (a : Γ(X, U)) :
    letI := algebraOfHom x U
    (deriv x U hU eP heP ψ hψ hψe M D).1 a =
      (chi' U hU eP ψ hψe M (chi (evP U eP) M D) (fstHom_comp_chi (evP U eP) M D) a).snd := rfl

variable (M' : Type u) [AddCommGroup M'] [Module K M'] [Module Kᵐᵒᵖ M'] [IsCentralScalar K M']

theorem chi_map (D : letI := algebraOfHom x U; ↥(Algebra.PointDerivations K Γ(X, U) (evP U eP) M)) (g : M →ₗ[K] M') :
    letI := algebraOfHom x U
    chi (evP U eP) M' (Algebra.PointDerivations.map (evP U eP) g D) =
      (TrivSqZeroExt.map (R' := K) g).toRingHom.comp (chi (evP U eP) M D) := by
  letI := algebraOfHom x U
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [TrivSqZeroExt.fst_map]
  · simp only [chi_apply, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
      RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_add,
      TrivSqZeroExt.snd_map, TrivSqZeroExt.map_inl, TrivSqZeroExt.map_inr]
    rfl

include heP hψ hψe in

theorem deriv_natural (D : letI := algebraOfHom x U; ↥(Algebra.PointDerivations K Γ(X, U) (evP U eP) M)) (g : M →ₗ[K] M') :
    letI := algebraOfHom x U
    deriv x U hU eP heP ψ hψ hψe M' (Algebra.PointDerivations.map (evP U eP) g D) =
      Algebra.PointDerivations.map (evP U eP) g (deriv x U hU eP heP ψ hψ hψe M D) := by
  letI := algebraOfHom x U

  have key : (TrivSqZeroExt.map (R' := K) g).toRingHom.comp
        (chi' U hU eP ψ hψe M (chi (evP U eP) M D) (fstHom_comp_chi (evP U eP) M D)) =
      chi' U hU eP ψ hψe M' (chi (evP U eP) M' (Algebra.PointDerivations.map (evP U eP) g D))
        (fstHom_comp_chi (evP U eP) M' _) := by
    apply chi'_unique
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, specMap_chi' U hU eP ψ hψe M, chi_map x U eP M M' D g,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  rw [deriv_apply, ← key]
  change (TrivSqZeroExt.map (R' := K) g
      (chi' U hU eP ψ hψe M (chi (evP U eP) M D) (fstHom_comp_chi (evP U eP) M D) a)).snd =
    g ((chi' U hU eP ψ hψe M (chi (evP U eP) M D) (fstHom_comp_chi (evP U eP) M D) a).snd)
  exact TrivSqZeroExt.snd_map _ _

end Deriv
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt.PushAtUnit28"

end PushAtUnit28
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt.PushAtUnit28"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt.PushAtUnit28"

noncomputable section

namespace PushAtUnit28

section Unit

theorem one_val_natural {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (φ : T' ⟶ T) :
    φ ≫ (L.one t).1 = (L.one (φ ≫ t)).1 :=
  congrArg Subtype.val (L.one_natural t (φ ≫ t) φ rfl)

theorem tangentZero_comp_tangentBase (K : Type u) [Field K] :
    tangentZero K ≫ tangentBase K (RingHom.id K) = 𝟙 _ := by
  rw [tangentZero, tangentBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (TrivSqZeroExt.fstHom K K K).toRingHom.comp ((algebraMap K (DualNumber K)).comp (RingHom.id K)) =
      RingHom.id K := by
    refine RingHom.ext fun a => ?_
    change (algebraMap K (DualNumber K) a).fst = a
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]
  rw [this, CommRingCat.ofHom_id, Spec.map_id]

end Unit
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt.PushAtUnit28"

section Eta

variable (K : Type u) [Field K]

def canMop (M : Type u) [AddCommGroup M] [Module K M] : Module Kᵐᵒᵖ M :=
  Module.compHom M (RingEquiv.toOpposite K).symm.toRingHom

theorem canCentral (M : Type u) [AddCommGroup M] [Module K M] : letI := canMop K M; IsCentralScalar K M := by
  letI := canMop K M
  exact ⟨fun r m => rfl⟩

variable {K}
variable {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
  (U : X.Opens) (hU : IsAffineOpen U) (eP : Spec (CommRingCat.of K) ⟶ (U : Scheme.{u}))
  (heP : eP ≫ U.ι ≫ x = 𝟙 _)
  (ψ : X ⟶ X) (hψ : ψ ≫ x = x) (hψe : (eP ≫ U.ι) ≫ ψ = eP ≫ U.ι)

theorem deriv_indep (M : Type u) [AddCommGroup M] [Module K M] (i₁ i₂ : Module Kᵐᵒᵖ M)
    (c₁ : letI := i₁; IsCentralScalar K M) (c₂ : letI := i₂; IsCentralScalar K M)
    (D : letI := algebraOfHom x U; ↥(Algebra.PointDerivations K Γ(X, U) (evP U eP) M)) :
    (letI := i₁; letI := c₁; deriv x U hU eP heP ψ hψ hψe M D) =
      (letI := i₂; letI := c₂; deriv x U hU eP heP ψ hψ hψe M D) := by
  obtain rfl : i₁ = i₂ := by
    refine Module.ext' i₁ i₂ fun r m => ?_
    rw [← MulOpposite.op_unop r]
    exact (c₁.op_smul_eq_smul _ _).trans (c₂.op_smul_eq_smul _ _).symm
  rfl

section prodD
variable {A : Type u} [CommRing A] [Algebra K A] (ev : A →+* K) {M : Type u} [AddCommGroup M] [Module K M]

def prodD (D₁ D₂ : ↥(Algebra.PointDerivations K A ev M)) : ↥(Algebra.PointDerivations K A ev (M × M)) :=
  ⟨LinearMap.prod D₁.1 D₂.1, fun a b => Prod.ext (by simp [D₁.2 a b]) (by simp [D₂.2 a b])⟩

theorem map_fst_prodD (D₁ D₂ : ↥(Algebra.PointDerivations K A ev M)) :
    Algebra.PointDerivations.map ev (LinearMap.fst K M M) (prodD ev D₁ D₂) = D₁ := by
  apply Subtype.ext; apply LinearMap.ext; intro a; rfl

theorem map_snd_prodD (D₁ D₂ : ↥(Algebra.PointDerivations K A ev M)) :
    Algebra.PointDerivations.map ev (LinearMap.snd K M M) (prodD ev D₁ D₂) = D₂ := by
  apply Subtype.ext; apply LinearMap.ext; intro a; rfl

theorem map_add_prodD (D₁ D₂ : ↥(Algebra.PointDerivations K A ev M)) :
    Algebra.PointDerivations.map ev (LinearMap.fst K M M + LinearMap.snd K M M) (prodD ev D₁ D₂) = D₁ + D₂ := by
  apply Subtype.ext; apply LinearMap.ext; intro a; rfl

theorem map_smul_id (c : K) (D : ↥(Algebra.PointDerivations K A ev M)) :
    Algebra.PointDerivations.map ev (c • (LinearMap.id : M →ₗ[K] M)) D = c • D := by
  apply Subtype.ext; apply LinearMap.ext; intro a; rfl

end prodD
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt.PushAtUnit28"

include heP hψ hψe in

def eta (M : Type u) [AddCommGroup M] [Module K M] :
    letI := algebraOfHom x U
    ↥(Algebra.PointDerivations K Γ(X, U) (evP U eP) M) →ₗ[K] ↥(Algebra.PointDerivations K Γ(X, U) (evP U eP) M) :=
  letI := algebraOfHom x U
  { toFun := fun D => letI := canMop K M; letI := canCentral K M; deriv x U hU eP heP ψ hψ hψe M D
    map_add' := fun D₁ D₂ => by
      letI := canMop K M; letI := canCentral K M
      letI := canMop K (M × M); letI := canCentral K (M × M)
      have hn := deriv_natural x U hU eP heP ψ hψ hψe (M × M) M (prodD (evP U eP) D₁ D₂)
      have e0 : deriv x U hU eP heP ψ hψ hψe M (D₁ + D₂) =
          Algebra.PointDerivations.map (evP U eP) (LinearMap.fst K M M + LinearMap.snd K M M)
            (deriv x U hU eP heP ψ hψ hψe (M × M) (prodD (evP U eP) D₁ D₂)) := by
        rw [← hn, map_add_prodD]
      have e1 : deriv x U hU eP heP ψ hψ hψe M D₁ =
          Algebra.PointDerivations.map (evP U eP) (LinearMap.fst K M M)
            (deriv x U hU eP heP ψ hψ hψe (M × M) (prodD (evP U eP) D₁ D₂)) := by
        rw [← hn, map_fst_prodD]
      have e2 : deriv x U hU eP heP ψ hψ hψe M D₂ =
          Algebra.PointDerivations.map (evP U eP) (LinearMap.snd K M M)
            (deriv x U hU eP heP ψ hψ hψe (M × M) (prodD (evP U eP) D₁ D₂)) := by
        rw [← hn, map_snd_prodD]
      rw [e0, e1, e2]
      apply Subtype.ext; apply LinearMap.ext; intro a; rfl
    map_smul' := fun c D => by
      letI := canMop K M; letI := canCentral K M
      have hn := deriv_natural x U hU eP heP ψ hψ hψe M M D (c • (LinearMap.id : M →ₗ[K] M))
      rw [RingHom.id_apply, ← map_smul_id (evP U eP) c D, hn, map_smul_id] }

theorem eta_apply (M : Type u) [AddCommGroup M] [Module K M]
    (D : letI := algebraOfHom x U; ↥(Algebra.PointDerivations K Γ(X, U) (evP U eP) M)) :
    letI := algebraOfHom x U
    eta x U hU eP heP ψ hψ hψe M D = (letI := canMop K M; letI := canCentral K M; deriv x U hU eP heP ψ hψ hψe M D) :=
  rfl

theorem rid_map_tmul_id {W : Type u} [AddCommGroup W] [Module K W] (θ : W →ₗ[K] W) (t : W ⊗[K] K) :
    TensorProduct.rid K W (TensorProduct.map θ (LinearMap.id : K →ₗ[K] K) t) = θ (TensorProduct.rid K W t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul w c => simp [TensorProduct.map_tmul]
  | add s t hs ht => simp [map_add, hs, ht]

end Eta
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt.PushAtUnit28"

end PushAtUnit28
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt.PushAtUnit28"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt.PushAtUnit28"

theorem solution
    (T' : Type u) [CommRing T'] [IsLocalRing T']

    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (W : Type u) [AddCommGroup W] [Module (ResidueField T') W]
    (τW : W → SchemeHomOver (tangentBase (ResidueField T') (RingHom.id (ResidueField T'))) xk)
    (hWinj : Function.Injective τW)
    (hWrange : ∀ P : SchemeHomOver (tangentBase (ResidueField T') (RingHom.id (ResidueField T'))) xk, P ∈ Set.range τW ↔ IsTangentVector Lk (ResidueField T') (RingHom.id (ResidueField T')) P)
    (hWadd : ∀ v w : W, τW (v + w) = Lk.mul (tangentBase (ResidueField T') (RingHom.id (ResidueField T'))) (τW v) (τW w))
    (hWsmul : ∀ (a : (ResidueField T')) (v : W), (τW (a • v)).1 = tangentScale (ResidueField T') a ≫ (τW v).1)

    (Φ : letI := algebraOfHom xk Ue
      ∀ (M : Type u) [AddCommGroup M] [Module (ResidueField T') M], ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M) ≃ₗ[(ResidueField T')] (W ⊗[(ResidueField T')] M))
    (hΦnat : letI := algebraOfHom xk Ue
      ∀ (M M' : Type u) [AddCommGroup M] [Module (ResidueField T') M] [AddCommGroup M'] [Module (ResidueField T') M'] (g : M →ₗ[(ResidueField T')] M') (δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M)),
        Φ M' (Algebra.PointDerivations.map ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) g δ) = TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField T')] W) g (Φ M δ))
    (hΦpin : letI := algebraOfHom xk Ue
      ∀ (δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) (ResidueField T'))) (χ : Γ(Ak, Ue) →+* DualNumber (ResidueField T')),
        (∀ a : Γ(Ak, Ue), TrivSqZeroExt.fst (χ a) = ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) a) →
        (∀ a : Γ(Ak, Ue), TrivSqZeroExt.snd (χ a) = (δ : Γ(Ak, Ue) →ₗ[(ResidueField T')] (ResidueField T')) a) →
        (τW (TensorProduct.rid (ResidueField T') W (Φ (ResidueField T') δ))).1 = Spec.map (CommRingCat.ofHom χ) ≫ hUe.fromSpec)

    (ψ : Ak ⟶ Ak) (hψ : ψ ≫ xk = xk)
    (θψ : W →ₗ[(ResidueField T')] W) (hθψ : ∀ w : W, τW (θψ w) = pushPt ψ hψ (τW w)) :
    letI := algebraOfHom xk Ue
    ∃ η : ∀ (M : Type u) [AddCommGroup M] [Module (ResidueField T') M], ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M) →ₗ[(ResidueField T')] ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M),

      (∀ (M M' : Type u) [AddCommGroup M] [Module (ResidueField T') M] [AddCommGroup M'] [Module (ResidueField T') M']
          (g : M →ₗ[(ResidueField T')] M') (δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M)),
        η M' (Algebra.PointDerivations.map ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) g δ) = Algebra.PointDerivations.map ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) g (η M δ)) ∧

      (∀ δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) (ResidueField T')),
        Φ (ResidueField T') (η (ResidueField T') δ) =
          TensorProduct.map θψ (LinearMap.id : (ResidueField T') →ₗ[(ResidueField T')] (ResidueField T')) (Φ (ResidueField T') δ)) ∧

      (∀ (M : Type u) [AddCommGroup M] [Module (ResidueField T') M] [Module (ResidueField T')ᵐᵒᵖ M] [IsCentralScalar (ResidueField T') M]
          (χ : Γ(Ak, Ue) →+* TrivSqZeroExt (ResidueField T') M) (δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M)),
        (∀ a : Γ(Ak, Ue), TrivSqZeroExt.fst (χ a) = ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) a) →
        (∀ a : Γ(Ak, Ue), TrivSqZeroExt.snd (χ a) = δ.1 a) →
        ∃ χ' : Γ(Ak, Ue) →+* TrivSqZeroExt (ResidueField T') M,
          (∀ a : Γ(Ak, Ue), TrivSqZeroExt.fst (χ' a) = ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) a) ∧
          (∀ a : Γ(Ak, Ue), TrivSqZeroExt.snd (χ' a) = (η M δ).1 a) ∧
          Spec.map (CommRingCat.ofHom χ') ≫ hUe.fromSpec = Spec.map (CommRingCat.ofHom χ) ≫ hUe.fromSpec ≫ ψ) := by
  letI instA := algebraOfHom xk Ue

  have h1 : τW 0 = Lk.one _ := by
    letI := Lk.pointGroup (tangentBase (ResidueField T') (RingHom.id (ResidueField T')))
    have h := hWadd 0 0
    rw [add_zero] at h
    have h2 : τW 0 * τW 0 = τW 0 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h2
  have heP : e₁ ≫ Ue.ι ≫ xk = 𝟙 _ := by rw [← Category.assoc, he₁]; exact (Lk.one _).2
  have hone : (Lk.one (𝟙 (Spec (CommRingCat.of (ResidueField T'))))).1 =
      tangentZero (ResidueField T') ≫ (Lk.one (tangentBase (ResidueField T') (RingHom.id (ResidueField T')))).1 := by
    rw [PushAtUnit28.one_val_natural, PushAtUnit28.tangentZero_comp_tangentBase]
  have hψe : (e₁ ≫ Ue.ι) ≫ ψ = e₁ ≫ Ue.ι := by
    have h := congrArg Subtype.val (hθψ 0)
    simp only [map_zero, h1, pushPt, mapPt_coe] at h
    rw [he₁, hone, Category.assoc, ← h]
  refine ⟨fun M _ _ => PushAtUnit28.eta xk Ue hUe e₁ heP ψ hψ hψe M, ?_, ?_, ?_⟩
  ·
    intro M M' _ _ _ _ g δ
    letI := PushAtUnit28.canMop (ResidueField T') M; letI := PushAtUnit28.canCentral (ResidueField T') M
    letI := PushAtUnit28.canMop (ResidueField T') M'; letI := PushAtUnit28.canCentral (ResidueField T') M'
    exact PushAtUnit28.deriv_natural xk Ue hUe e₁ heP ψ hψ hψe M M' δ g
  ·
    intro δ

    have hsw := PushAtUnit28.deriv_indep xk Ue hUe e₁ heP ψ hψ hψe (ResidueField T')
      (PushAtUnit28.canMop (ResidueField T') (ResidueField T')) inferInstance
      (PushAtUnit28.canCentral (ResidueField T') (ResidueField T')) inferInstance δ
    rw [PushAtUnit28.eta_apply, hsw]

    set χ := PushAtUnit28.chi (PushAtUnit28.evP Ue e₁) (ResidueField T') δ with hχdef
    have hχ := PushAtUnit28.fstHom_comp_chi (PushAtUnit28.evP Ue e₁) (ResidueField T') δ
    set δ' := PushAtUnit28.deriv xk Ue hUe e₁ heP ψ hψ hψe (ResidueField T') δ with hδ'def
    have hp1 := hΦpin δ χ (fun a => PushAtUnit28.fst_chi _ _ δ a) (fun a => PushAtUnit28.snd_chi _ _ δ a)
    have hp2 := hΦpin δ' (PushAtUnit28.chi' Ue hUe e₁ ψ hψe (ResidueField T') χ hχ)
      (fun a => congrArg (fun f : Γ(Ak, Ue) →+* ResidueField T' => f a)
        (PushAtUnit28.fstHom_comp_chi' Ue hUe e₁ ψ hψe (ResidueField T') χ hχ))
      (fun a => (PushAtUnit28.deriv_apply xk Ue hUe e₁ heP ψ hψ hψe (ResidueField T') δ a).symm)
    rw [PushAtUnit28.specMap_chi' Ue hUe e₁ ψ hψe (ResidueField T') χ hχ,
      ← Category.assoc (Spec.map (CommRingCat.ofHom χ)) hUe.fromSpec ψ, ← hp1] at hp2
    have h3 := congrArg Subtype.val (hθψ (TensorProduct.rid (ResidueField T') W (Φ (ResidueField T') δ)))
    simp only [pushPt, mapPt_coe] at h3
    rw [← h3] at hp2
    have h4 := hWinj (Subtype.ext hp2)

    apply (TensorProduct.rid (ResidueField T') W).injective
    rw [h4, PushAtUnit28.rid_map_tmul_id]
  ·
    intro M _ _ iMop iC χ δ hχ1 hχ2
    have hi : iMop = PushAtUnit28.canMop (ResidueField T') M := by
      refine Module.ext' _ _ fun r m => ?_
      rw [← MulOpposite.op_unop r]
      exact (iC.op_smul_eq_smul _ _).trans rfl
    subst hi
    letI := PushAtUnit28.canMop (ResidueField T') M
    have hχeq : χ = PushAtUnit28.chi (PushAtUnit28.evP Ue e₁) M δ := PushAtUnit28.eq_chi _ M δ χ hχ1 hχ2
    subst hχeq
    refine ⟨PushAtUnit28.chi' Ue hUe e₁ ψ hψe M _ (PushAtUnit28.fstHom_comp_chi _ M δ), fun a => ?_, fun a => ?_, ?_⟩
    · exact congrArg (fun f : Γ(Ak, Ue) →+* ResidueField T' => f a) (PushAtUnit28.fstHom_comp_chi' Ue hUe e₁ ψ hψe M _ _)
    · rw [PushAtUnit28.eta_apply]
      exact (PushAtUnit28.deriv_indep xk Ue hUe e₁ heP ψ hψ hψe M _ _ iC (PushAtUnit28.canCentral (ResidueField T') M) δ) ▸
        (PushAtUnit28.deriv_apply xk Ue hUe e₁ heP ψ hψ hψe M δ a).symm
    · exact PushAtUnit28.specMap_chi' Ue hUe e₁ ψ hψe M _ _

end S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt (solution)
