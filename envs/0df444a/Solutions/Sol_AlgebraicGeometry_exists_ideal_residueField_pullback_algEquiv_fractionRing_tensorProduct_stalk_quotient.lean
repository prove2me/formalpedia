-- Prove2me | solution 1 for AlgebraicGeometry.exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/550335f1-87e8-5c52-b235-d58c0e93e44f

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient.AlgebraicGeometry"
open scoped TensorProduct

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Surjective Scheme.Hom Scheme.Γ IsAffineOpen.fromSpec_top IsAffine.of_isIso IsAffine IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop pullbackSpecIso_inv_fst exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE IsAffineOpen IsAffineOpen.fromSpec_primeIdealOf pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.germ_stalkMap Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.map_appLE Opens.topIso_inv Hom mk Γ topIso_hom topIso ΓSpecIso_inv_naturality isoSpec_Spec_inv Opens.topIso_hom Hom.comp_appTop isoSpec residueField Opens residue Hom.appLE_map Hom.app_eq_appLE Hom.germ_stalkMap le_iff_specializes Opens.ι_appTop Hom.appLE ΓSpecIso Hom.appLE_eq_app TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap algebraOfHom algebraMap_algebraOfHom pullback mk"
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace AffineBaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
variable (A : Type u) [CommRing A] [Algebra R A]

abbrev XA : Scheme.{u} := Limits.pullback c (specMap R A)

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.fst : XA c A ⟶ X := Limits.pullback.fst c (specMap R A)
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange" "fst"

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.snd : XA c A ⟶ Spec (.of A) := Limits.pullback.snd c (specMap R A)

p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange" "snd"
variable (U : X.Opens) (hU : IsAffineOpen U)

theorem specMap_algebraMap_eq :
    letI := algebraOfHom c U
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) = hU.fromSpec ≫ c := by
  letI := algebraOfHom c U
  have halg : (algebraMap R Γ(X, U)) = ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom := rfl
  rw [halg, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top (Spec (.of R))) hU (le_top : U ≤ c ⁻¹ᵁ ⊤)]

def pullbackAffineOpenIsoSpecTensor :
    letI := algebraOfHom c U
    ((fst c A) ⁻¹ᵁ U).toScheme ≅ Spec (.of (Γ(X, U) ⊗[R] A)) :=
  letI := algebraOfHom c U
  (pullbackRestrictIsoRestrict (fst c A) U).symm
    ≪≫ pullbackSymmetry _ _
    ≪≫ pullbackRightPullbackFstIso c (specMap R A) U.ι
    ≪≫ asIso (pullback.map (U.ι ≫ c) (specMap R A)
        (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) (specMap R A)
        hU.isoSpec.hom (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, specMap_algebraMap_eq c U hU, ← hU.isoSpec_inv_ι_assoc, Iso.hom_inv_id_assoc])
        (by rw [Category.id_comp, Category.comp_id]))
    ≪≫ pullbackSpecIso R Γ(X, U) A

def sigma :
    letI := algebraOfHom c U
    (Γ(X, U) ⊗[R] A) ≃+* Γ(XA c A, (fst c A) ⁻¹ᵁ U) :=
  letI := algebraOfHom c U
  ((Scheme.ΓSpecIso (.of (Γ(X, U) ⊗[R] A))).symm
    ≪≫ Scheme.Γ.mapIso (pullbackAffineOpenIsoSpecTensor c A U hU).op
    ≪≫ ((fst c A) ⁻¹ᵁ U).topIso).commRingCatIsoToRingEquiv

theorem sigma_apply (x : letI := algebraOfHom c U; Γ(X, U) ⊗[R] A) :
    letI := algebraOfHom c U
    sigma c A U hU x = ((Scheme.ΓSpecIso (.of (Γ(X, U) ⊗[R] A))).inv
      ≫ (pullbackAffineOpenIsoSpecTensor c A U hU).hom.appTop ≫ ((fst c A) ⁻¹ᵁ U).topIso.hom).hom x :=
  rfl

theorem iso_hom_comp_sndLeg :
    letI := algebraOfHom c U
    ((fst c A) ⁻¹ᵁ U).ι ≫ snd c A
      = (pullbackAffineOpenIsoSpecTensor c A U hU).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[R] Γ(X, U) ⊗[R] A)) := by
  letI := algebraOfHom c U
  rw [pullbackAffineOpenIsoSpecTensor, ← pullbackSpecIso_inv_snd R Γ(X, U) A]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    pullback.lift_snd, Category.comp_id, pullbackRightPullbackFstIso_hom_snd,
    pullbackSymmetry_hom_comp_snd_assoc, pullbackRestrictIsoRestrict_inv_fst_assoc]

theorem iso_hom_comp_fstLeg :
    letI := algebraOfHom c U
    (pullbackAffineOpenIsoSpecTensor c A U hU).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(X, U) →+* Γ(X, U) ⊗[R] A))
      = ((fst c A) ∣_ U) ≫ hU.isoSpec.hom := by
  letI := algebraOfHom c U
  rw [pullbackAffineOpenIsoSpecTensor, ← pullbackSpecIso_inv_fst R Γ(X, U) A]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    pullback.lift_fst, pullbackRightPullbackFstIso_hom_fst_assoc, pullbackSymmetry_hom_comp_fst_assoc]
  rfl

omit [CommRing R] in
theorem opens_ι_appTop_topIso_hom {Y : Scheme.{u}} (V : Y.Opens) :
    V.ι.appTop ≫ V.topIso.hom = Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact (Y.presheaf.map_comp _ _).symm.trans (congrArg Y.presheaf.map (Subsingleton.elim _ _))

omit [CommRing R] in
theorem topIso_morphismRestrict_appTop_topIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) (W : Z.Opens) :
    W.topIso.inv ≫ (g ∣_ W).appTop ≫ (g ⁻¹ᵁ W).topIso.hom = g.app W := by
  simp only [Scheme.Opens.topIso_inv, eqToHom_op, TopologicalSpace.Opens.map_top,
    Scheme.Opens.topIso_hom, Scheme.Hom.app_eq_appLE, morphismRestrict_appLE]
  erw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem sigma_tmul_one (s : Γ(X, U)) :
    letI := algebraOfHom c U
    sigma c A U hU (s ⊗ₜ[R] (1 : A)) = ((fst c A).app U).hom s := by
  letI := algebraOfHom c U
  rw [sigma_apply]
  have hiL : s ⊗ₜ[R] (1 : A)
      = (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(X, U) →+* Γ(X, U) ⊗[R] A)).hom s := rfl
  rw [hiL, ← CommRingCat.comp_apply, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Category.assoc _ _ (((fst c A) ⁻¹ᵁ U).topIso.hom), ← Scheme.Hom.comp_appTop,
    iso_hom_comp_fstLeg c A U hU, Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
  have hΓ : (Scheme.ΓSpecIso (CommRingCat.of Γ(X, U))).inv ≫ (Scheme.ΓSpecIso Γ(X, U)).hom = 𝟙 _ :=
    Iso.inv_hom_id _
  simp only [← Category.assoc]
  rw [hΓ, Category.id_comp, Category.assoc, topIso_morphismRestrict_appTop_topIso]

theorem sigma_one_tmul (a : A) :
    letI := algebraOfHom c U
    sigma c A U hU ((1 : Γ(X, U)) ⊗ₜ[R] a)
      = ((XA c A).presheaf.map (homOfLE (le_top : (fst c A) ⁻¹ᵁ U ≤ ⊤)).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ (snd c A).appTop).hom a) := by
  letI := algebraOfHom c U
  rw [sigma_apply]
  have hiR : (1 : Γ(X, U)) ⊗ₜ[R] a
      = (CommRingCat.ofHom (R := A) (S := Γ(X, U) ⊗[R] A)
          (Algebra.TensorProduct.includeRight : A →ₐ[R] Γ(X, U) ⊗[R] A)).hom a := rfl
  rw [hiR, ← CommRingCat.comp_apply, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Category.assoc _ _ (((fst c A) ⁻¹ᵁ U).topIso.hom), ← Scheme.Hom.comp_appTop,
    ← iso_hom_comp_sndLeg c A U hU, Scheme.Hom.comp_appTop, Category.assoc,
    opens_ι_appTop_topIso_hom ((fst c A) ⁻¹ᵁ U)]
  rfl

theorem algebraMap_sndAlgebra (a : A) :
    (algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)).algebraMap a
      = ((XA c A).presheaf.map (homOfLE (le_top : (fst c A) ⁻¹ᵁ U ≤ ⊤)).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ (snd c A).appTop).hom a) := by
  rw [algebraMap_algebraOfHom, Scheme.Hom.appLE, CommRingCat.comp_apply, CommRingCat.comp_apply]
  rfl

private def _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.algEquiv :
    letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
    (A ⊗[R] Γ(X, U)) ≃ₐ[A] Γ(XA c A, (fst c A) ⁻¹ᵁ U) :=
  letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R A Γ(X, U)).toRingEquiv.trans (sigma c A U hU))
    (fun a => by
      show sigma c A U hU ((Algebra.TensorProduct.comm R A Γ(X, U)) (algebraMap A (A ⊗[R] Γ(X, U)) a)) = _
      rw [Algebra.TensorProduct.algebraMap_apply, show algebraMap A A a = a from rfl,
        Algebra.TensorProduct.comm_tmul, sigma_one_tmul, algebraMap_sndAlgebra])

p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange" "algEquiv"
theorem algEquiv_one_tmul (s : Γ(X, U)) :
    letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
    algEquiv c A U hU ((1 : A) ⊗ₜ[R] s) = ((fst c A).app U).hom s := by
  letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
  show sigma c A U hU ((Algebra.TensorProduct.comm R A Γ(X, U)) ((1 : A) ⊗ₜ[R] s)) = _
  rw [Algebra.TensorProduct.comm_tmul, sigma_tmul_one]

end AffineBaseChange

open AffineBaseChange in

theorem exists_algEquiv_sections_baseChange {R : Type u} [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (U : X.Opens) (hU : IsAffineOpen U) (A : Type u) [CommRing A] [Algebra R A] :
    letI := algebraOfHom c U
    letI := algebraOfHom (Limits.pullback.snd c (specMap R A)) ((Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ U)
    ∃ e : (A ⊗[R] Γ(X, U)) ≃ₐ[A]
        Γ(Limits.pullback c (specMap R A), (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ U),
      ∀ s : Γ(X, U), e ((1 : A) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R A)).app U).hom s :=
  ⟨algEquiv c A U hU, algEquiv_one_tmul c A U hU⟩

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd Surjective Scheme.Hom Scheme.Γ IsAffineOpen.fromSpec_top IsAffine.of_isIso IsAffine IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso Scheme.isoSpec_Spec_inv IsAffineOpen.isoSpec_hom_appTop pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Opens.topIso_hom Scheme.Hom.comp_appTop pullbackSpecIso_inv_fst exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE IsAffineOpen IsAffineOpen.fromSpec_primeIdealOf pullbackRestrictIsoRestrict Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.germ_stalkMap Scheme.Opens.ι_appTop Scheme.Hom.appLE morphismRestrict_appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom"
p2m_open "AlgebraicGeometry"

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover _root_.P2MW.S_AlgebraicGeometry_exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient.AlgebraicGeometry.Scheme.TwoAffineOpenCover in

theorem exists_algEquiv_tensorProduct_sections_preimage
    {K : Type u} [Field K] (K' : Type u) [Field K'] [Algebra K K']
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty (U : Scheme.{u})] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom x U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd x (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
      ((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U)
    ∃ e : K' ⊗[K] Γ(X, U) ≃ₐ[K']
        Γ(pullback x (Spec.map (CommRingCat.ofHom (algebraMap K K'))),
          (pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ⁻¹ᵁ U),
      ∀ s : Γ(X, U), e (1 ⊗ₜ s) = ((pullback.fst x (Spec.map (CommRingCat.ofHom (algebraMap K K')))).app U).hom s :=
  exists_algEquiv_sections_baseChange x U hU K'

end AlgebraicGeometry

end

namespace StalkBC

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient.AlgebraicGeometry"

theorem exists_residueField_equiv_of_isAffineOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : ↥U) :
    ∃ θ : X.residueField x.1 ≃+* (hU.primeIdealOf x).asIdeal.ResidueField,
      ∀ s : Γ(X, U), θ ((X.residue x.1).hom ((X.presheaf.germ U x.1 x.2).hom s)) =
        algebraMap Γ(X, U) (hU.primeIdealOf x).asIdeal.ResidueField s := by
  letI := X.presheaf.algebra_section_stalk x
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x.1) (hU.primeIdealOf x).asIdeal := hU.isLocalization_stalk x
  let e : X.presheaf.stalk x.1 ≃ₐ[Γ(X, U)] Localization.AtPrime (hU.primeIdealOf x).asIdeal :=
    IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl _ _
  refine ⟨IsLocalRing.ResidueField.mapEquiv e.toRingEquiv, fun s => ?_⟩
  have hgerm : (X.presheaf.germ U x.1 x.2).hom s = algebraMap Γ(X, U) (X.presheaf.stalk x.1) s := rfl
  rw [hgerm]
  change IsLocalRing.ResidueField.mapEquiv e.toRingEquiv
      (IsLocalRing.residue _ (algebraMap Γ(X, U) (X.presheaf.stalk x.1) s)) = _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  change IsLocalRing.residue _ (e (algebraMap Γ(X, U) (X.presheaf.stalk x.1) s)) = _
  rw [e.commutes s]
  rfl

end StalkBC

namespace StalkBC

theorem exists_fractionRing_equiv_of_injective_of_generates {T F : Type*} [CommRing T] [Field F]
    (𝔮 : Ideal T) [𝔮.IsPrime] (χ : T ⧸ 𝔮 →+* F) (hχ : Function.Injective χ)
    (hgen : ∀ x : F, ∃ a b : T, x = χ (Ideal.Quotient.mk 𝔮 a) / χ (Ideal.Quotient.mk 𝔮 b)) :
    ∃ ψ₀ : FractionRing (T ⧸ 𝔮) ≃+* F,
      ∀ t : T, ψ₀ (algebraMap (T ⧸ 𝔮) (FractionRing (T ⧸ 𝔮)) (Ideal.Quotient.mk 𝔮 t)) = χ (Ideal.Quotient.mk 𝔮 t) := by
  haveI : IsDomain (T ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  let ω : FractionRing (T ⧸ 𝔮) →+* F := IsFractionRing.lift hχ
  have hω : ∀ q, ω (algebraMap (T ⧸ 𝔮) (FractionRing (T ⧸ 𝔮)) q) = χ q := fun q => IsFractionRing.lift_algebraMap hχ q
  have hsurj : Function.Surjective ω := by
    intro x
    obtain ⟨a, b, rfl⟩ := hgen x
    exact ⟨algebraMap _ _ (Ideal.Quotient.mk 𝔮 a) / algebraMap _ _ (Ideal.Quotient.mk 𝔮 b), by rw [map_div₀, hω, hω]⟩
  exact ⟨RingEquiv.ofBijective ω ⟨ω.injective, hsurj⟩, fun t => hω _⟩

end StalkBC

namespace StalkBC

open scoped TensorProduct

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem core {R k B S B' : Type*} [CommRing R] [Field k] [CommRing B] [CommRing S] [CommRing B']
    [Algebra R k] [Algebra R B] [Algebra B S] [Algebra R S] [IsScalarTower R B S]
    (𝔭 : Ideal B) [𝔭.IsPrime] [IsLocalization.AtPrime S 𝔭]
    [Algebra k B'] (ρ : B →+* B') (hρR : ∀ r : R, ρ (algebraMap R B r) = algebraMap k B' (algebraMap R k r))
    (eV : k ⊗[R] B ≃ₐ[k] B') (heV : ∀ b : B, eV ((1 : k) ⊗ₜ[R] b) = ρ b)
    (𝔓 : Ideal B') [𝔓.IsPrime] (hcomap : 𝔓.comap ρ = 𝔭) :
    letI : Algebra k 𝔓.ResidueField := ((algebraMap B' 𝔓.ResidueField).comp (algebraMap k B')).toAlgebra
    ∃ (σ : S →+* 𝔓.ResidueField) (_ : ∀ b : B, σ (algebraMap B S b) = algebraMap B' 𝔓.ResidueField (ρ b))
      (𝔮 : Ideal (k ⊗[R] S)) (_ : 𝔮.IsPrime) (ψ₁ : 𝔓.ResidueField ≃+* FractionRing ((k ⊗[R] S) ⧸ 𝔮)),
      (∀ s : S, ψ₁ (σ s) = (Localization.mk (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[R] s)) 1 : FractionRing ((k ⊗[R] S) ⧸ 𝔮))) ∧
      (∀ c : k, ψ₁ (algebraMap k 𝔓.ResidueField c) =
        (Localization.mk (Ideal.Quotient.mk 𝔮 (c ⊗ₜ[R] (1 : S))) 1 : FractionRing ((k ⊗[R] S) ⧸ 𝔮))) ∧
      (∀ x : k ⊗[R] B, (Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom R B S)) x ∈ 𝔮 ↔ eV x ∈ 𝔓) := by
  letI algkκ : Algebra k 𝔓.ResidueField := ((algebraMap B' 𝔓.ResidueField).comp (algebraMap k B')).toAlgebra
  have hkκ : ∀ c : k, algebraMap k 𝔓.ResidueField c = algebraMap B' 𝔓.ResidueField (algebraMap k B' c) := fun c => rfl
  haveI : IsScalarTower k B' 𝔓.ResidueField := IsScalarTower.of_algebraMap_eq (fun c => rfl)

  let gκ : B →+* 𝔓.ResidueField := (algebraMap B' 𝔓.ResidueField).comp ρ
  have hgκ : ∀ y : 𝔭.primeCompl, IsUnit (gκ y) := by
    intro y
    rw [isUnit_iff_ne_zero, ne_eq]
    change ¬ algebraMap B' 𝔓.ResidueField (ρ y) = 0
    rw [Ideal.algebraMap_residueField_eq_zero]
    intro hmem
    apply y.2
    have : (y : B) ∈ 𝔓.comap ρ := Ideal.mem_comap.mpr hmem
    rwa [hcomap] at this
  let σ : S →+* 𝔓.ResidueField := IsLocalization.lift (M := 𝔭.primeCompl) hgκ
  have hσ : ∀ b : B, σ (algebraMap B S b) = algebraMap B' 𝔓.ResidueField (ρ b) :=
    fun b => IsLocalization.lift_eq (M := 𝔭.primeCompl) hgκ b

  letI algRκ : Algebra R 𝔓.ResidueField := ((algebraMap k 𝔓.ResidueField).comp (algebraMap R k)).toAlgebra
  haveI : IsScalarTower R k 𝔓.ResidueField := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  let σ' : S →ₐ[R] 𝔓.ResidueField :=
    { toRingHom := σ
      commutes' := fun r => by
        change σ (algebraMap R S r) = algebraMap k 𝔓.ResidueField (algebraMap R k r)
        rw [IsScalarTower.algebraMap_apply R B S, hσ, hρR, hkκ] }
  let Φ : k ⊗[R] S →ₐ[k] 𝔓.ResidueField :=
    Algebra.TensorProduct.lift (Algebra.ofId k 𝔓.ResidueField) σ' (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (c : k) (s : S), Φ (c ⊗ₜ[R] s) = algebraMap k 𝔓.ResidueField c * σ s :=
    fun c s => Algebra.TensorProduct.lift_tmul _ _ _ c s

  obtain ⟨𝔮, h𝔮def⟩ : ∃ 𝔮 : Ideal (k ⊗[R] S), 𝔮 = RingHom.ker Φ.toRingHom := ⟨_, rfl⟩
  haveI h𝔮 : 𝔮.IsPrime := h𝔮def ▸ RingHom.ker_isPrime Φ.toRingHom
  let χ : (k ⊗[R] S) ⧸ 𝔮 →+* 𝔓.ResidueField := Ideal.Quotient.lift 𝔮 Φ.toRingHom (fun a ha => by rwa [h𝔮def] at ha)
  have hχ : ∀ t, χ (Ideal.Quotient.mk 𝔮 t) = Φ t := fun t => Ideal.Quotient.lift_mk _ _ _
  have hχinj : Function.Injective χ :=
    RingHom.lift_injective_of_ker_le_ideal 𝔮 (fun a ha => by rwa [h𝔮def] at ha) (by rw [h𝔮def])

  let ιB : B →ₐ[R] S := IsScalarTower.toAlgHom R B S
  let ι : B' →+* k ⊗[R] S :=
    (Algebra.TensorProduct.map (AlgHom.id k k) ιB).toRingHom.comp eV.symm.toAlgHom.toRingHom
  have hΦι : ∀ b' : B', Φ (ι b') = algebraMap B' 𝔓.ResidueField b' := by
    have key : (Φ.comp (Algebra.TensorProduct.map (AlgHom.id k k) ιB)) =
        ((Algebra.ofId B' 𝔓.ResidueField).restrictScalars k).comp eV.toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro c b
      change Φ (c ⊗ₜ[R] (IsScalarTower.toAlgHom R B S) b) = algebraMap B' 𝔓.ResidueField (eV (c ⊗ₜ[R] b))
      rw [IsScalarTower.toAlgHom_apply]
      have htm : c ⊗ₜ[R] b = c • ((1 : k) ⊗ₜ[R] b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hΦ, hσ, htm, map_smul, heV, Algebra.smul_def, map_mul, ← hkκ]
    intro b'
    have := congrArg (fun F => F (eV.symm b')) key
    simp at this
    exact this

  have hgen : ∀ x : 𝔓.ResidueField, ∃ a b : k ⊗[R] S, x = χ (Ideal.Quotient.mk 𝔮 a) / χ (Ideal.Quotient.mk 𝔮 b) := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B' ⧸ 𝔓) x
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨ι a', ι b', ?_⟩
    rw [hχ, hχ, hΦι, hΦι, Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk]
  obtain ⟨ψ₀, hψ₀⟩ := exists_fractionRing_equiv_of_injective_of_generates 𝔮 χ hχinj hgen
  refine ⟨σ, hσ, 𝔮, h𝔮, ψ₀.symm, fun s => ?_, fun c => ?_, fun x => ?_⟩
  · apply ψ₀.injective
    rw [RingEquiv.apply_symm_apply, Localization.mk_one_eq_algebraMap, hψ₀, hχ, hΦ, map_one, one_mul]
  · apply ψ₀.injective
    rw [RingEquiv.apply_symm_apply, Localization.mk_one_eq_algebraMap, hψ₀, hχ, hΦ, map_one, mul_one]
  · rw [h𝔮def, RingHom.mem_ker, ← Ideal.algebraMap_residueField_eq_zero (I := 𝔓)]
    change Φ ((Algebra.TensorProduct.map (AlgHom.id k k) ιB) x) = 0 ↔ _

    have h1 : ι (eV x) = (Algebra.TensorProduct.map (AlgHom.id k k) ιB) x := by
      change (Algebra.TensorProduct.map (AlgHom.id k k) ιB) (eV.symm (eV x)) = _
      rw [AlgEquiv.symm_apply_apply]
    rw [← h1, hΦι]

end StalkBC

namespace StalkBC

variable (R k B S : Type*) [CommRing R] [CommRing k] [Algebra R k] [CommRing B] [Algebra R B]
  [CommRing S] [Algebra B S] [Algebra R S] [IsScalarTower R B S] (M : Submonoid B) [IsLocalization M S]

noncomputable def ιT : B ⊗[R] k →ₐ[B] S ⊗[R] k :=
  Algebra.TensorProduct.map (Algebra.ofId B S) (AlgHom.id R k)

theorem ιT_tmul (b : B) (a : k) : ιT R k B S (b ⊗ₜ[R] a) = algebraMap B S b ⊗ₜ[R] a := rfl

theorem isLocalization_baseChange :
    @IsLocalization _ _ (M.map (Algebra.TensorProduct.includeLeft : B →ₐ[B] B ⊗[R] k)) (S ⊗[R] k) _
      (ιT R k B S).toRingHom.toAlgebra := by
  letI alg : Algebra (B ⊗[R] k) (S ⊗[R] k) := (ιT R k B S).toRingHom.toAlgebra

  have h0 : IsLocalization (Algebra.algebraMapSubmonoid (B ⊗[R] k) M) ((B ⊗[R] k) ⊗[B] S) :=
    IsLocalization.tensor (R := B) (S := B ⊗[R] k) S M
  have hM : Algebra.algebraMapSubmonoid (B ⊗[R] k) M
      = M.map (Algebra.TensorProduct.includeLeft : B →ₐ[B] B ⊗[R] k) := by
    ext x; simp [Algebra.algebraMapSubmonoid, Submonoid.mem_map, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.includeLeft_apply]
  rw [← hM]

  let e₁ : (B ⊗[R] k) ⊗[B] S ≃ₐ[B] S ⊗[B] (B ⊗[R] k) := Algebra.TensorProduct.comm B (B ⊗[R] k) S
  let e₂ : S ⊗[B] (B ⊗[R] k) ≃ₐ[B] S ⊗[R] k := Algebra.TensorProduct.cancelBaseChange R B B S k
  have hcomp : (ιT R k B S).toRingHom
      = (e₁.trans e₂).toRingEquiv.toRingHom.comp (algebraMap (B ⊗[R] k) ((B ⊗[R] k) ⊗[B] S)) := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b a =>
      show ιT R k B S (b ⊗ₜ[R] a) = e₂ (e₁ ((b ⊗ₜ[R] a) ⊗ₜ[B] (1 : S)))
      rw [ιT_tmul]
      show _ = e₂ (Algebra.TensorProduct.comm B (B ⊗[R] k) S ((b ⊗ₜ[R] a) ⊗ₜ[B] (1 : S)))
      rw [Algebra.TensorProduct.comm_tmul]
      show _ = Algebra.TensorProduct.cancelBaseChange R B B S k ((1 : S) ⊗ₜ[B] (b ⊗ₜ[R] a))
      rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hcomp]
  exact (IsLocalization.isLocalization_iff_of_ringEquiv _ (e₁.trans e₂).toRingEquiv).mp h0

theorem presentation :
    @IsLocalization _ _ (M.map (Algebra.TensorProduct.includeRight : B →ₐ[R] k ⊗[R] B)) (k ⊗[R] S) _
      (Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom R B S)).toRingHom.toAlgebra := by

  have h0 := isLocalization_baseChange R k B S M
  letI algBk : Algebra (B ⊗[R] k) (S ⊗[R] k) := (ιT R k B S).toRingHom.toAlgebra

  let eS : S ⊗[R] k ≃ₐ[R] k ⊗[R] S := Algebra.TensorProduct.comm R S k
  have h1 := (IsLocalization.isLocalization_iff_of_ringEquiv
    (M.map (Algebra.TensorProduct.includeLeft : B →ₐ[B] B ⊗[R] k)) eS.toRingEquiv).mp h0

  let eB : B ⊗[R] k ≃ₐ[R] k ⊗[R] B := Algebra.TensorProduct.comm R B k
  letI algBk' : Algebra (B ⊗[R] k) (k ⊗[R] S) :=
    (eS.toRingEquiv.toRingHom.comp (algebraMap (B ⊗[R] k) (S ⊗[R] k))).toAlgebra
  haveI := h1
  have h2 := IsLocalization.isLocalization_of_base_ringEquiv
    (M.map (Algebra.TensorProduct.includeLeft : B →ₐ[B] B ⊗[R] k)) (k ⊗[R] S) eB.toRingEquiv

  have hM : (M.map (Algebra.TensorProduct.includeLeft : B →ₐ[B] B ⊗[R] k)).map eB.toRingEquiv.toMonoidHom
      = M.map (Algebra.TensorProduct.includeRight : B →ₐ[R] k ⊗[R] B) := by
    ext x
    constructor
    · rintro ⟨y, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b, hb, (Algebra.TensorProduct.comm_tmul R b (1 : k)).symm⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨_, ⟨b, hb, rfl⟩, Algebra.TensorProduct.comm_tmul R b (1 : k)⟩
  have halg : (Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom R B S)).toRingHom
      = ((eS.toRingEquiv.toRingHom.comp (algebraMap (B ⊗[R] k) (S ⊗[R] k))).comp eB.symm.toRingEquiv.toRingHom) := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      show Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom R B S) (a ⊗ₜ[R] b)
        = eS (ιT R k B S (eB.symm (a ⊗ₜ[R] b)))
      rw [Algebra.TensorProduct.map_tmul]
      show a ⊗ₜ[R] algebraMap B S b = eS (ιT R k B S ((Algebra.TensorProduct.comm R B k).symm (a ⊗ₜ[R] b)))
      rw [Algebra.TensorProduct.comm_symm_tmul, ιT_tmul]
      exact (Algebra.TensorProduct.comm_tmul R (algebraMap B S b) a).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [halg, ← hM]
  exact h2

end StalkBC

namespace StalkBC

theorem minimal {B' L : Type*} [CommRing B'] [CommRing L] [Algebra B' L] (M : Submonoid B') [IsLocalization M L]
    (𝔓 : Ideal B') (hmin : ∀ 𝔓' : Ideal B', 𝔓'.IsPrime → 𝔓' ≤ 𝔓 → 𝔓' = 𝔓)
    (𝔮 : Ideal L) [h𝔮 : 𝔮.IsPrime] (hcomap : 𝔮.comap (algebraMap B' L) = 𝔓) :
    𝔮 ∈ minimalPrimes L := by
  refine ⟨⟨h𝔮, bot_le⟩, ?_⟩
  rintro 𝔮' ⟨h𝔮', -⟩ hle
  have h1 : 𝔮'.comap (algebraMap B' L) = 𝔓 :=
    hmin _ (Ideal.comap_isPrime _ _) (hcomap ▸ Ideal.comap_mono hle)
  rw [← IsLocalization.map_comap M L 𝔮, ← IsLocalization.map_comap M L 𝔮']
  show Ideal.map (algebraMap B' L) (𝔮.comap (algebraMap B' L)) ≤ Ideal.map (algebraMap B' L) (𝔮'.comap (algebraMap B' L))
  rw [h1, hcomap]

end StalkBC

set_option maxHeartbeats 24000000 in
set_option synthInstance.maxHeartbeats 1600000 in
open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient.AlgebraicGeometry in
theorem solution
    {X : Scheme.{u}} (R : Type u) [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    (k : Type u) [Field k] [Algebra R k]
    (η : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k))))) :
    letI : Algebra R (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η)) :=
      RingHom.toAlgebra ((X.presheaf.germ ⊤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η) trivial).hom.comp
        ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))
    letI : Algebra k ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).residueField η) :=
      RingHom.toAlgebra (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).residue η).hom.comp
        (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).presheaf.germ ⊤ η trivial).hom.comp
          (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).appTop).hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)))
    ∃ (𝔮 : Ideal (k ⊗[R] (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η)))) (_ : 𝔮.IsPrime)
      (ψ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).residueField η ≃ₐ[k] FractionRing ((k ⊗[R] (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η))) ⧸ 𝔮)),
      (∀ s : (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η)),
        ψ (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).residue η).hom
            (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).stalkMap η).hom s)) =
          (Localization.mk (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[R] s)) 1 : FractionRing ((k ⊗[R] (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η))) ⧸ 𝔮))) ∧
      ((∀ η' : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k)))), η' ⤳ η → η' = η) → 𝔮 ∈ minimalPrimes (k ⊗[R] (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η)))) := by
  classical

  let g : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let Xk := pullback f g
  let p₁ : Xk ⟶ X := pullback.fst f g
  let p₂ : Xk ⟶ Spec (CommRingCat.of k) := pullback.snd f g
  let zz : ↥X := p₁.base η
  letI algS : Algebra R (X.presheaf.stalk zz) :=
    RingHom.toAlgebra ((X.presheaf.germ ⊤ zz trivial).hom.comp ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))
  letI algκ : Algebra k (Xk.residueField η) :=
    RingHom.toAlgebra ((Xk.residue η).hom.comp ((Xk.presheaf.germ ⊤ η trivial).hom.comp
      ((p₂.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)))

  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := zz) (U := ⊤) trivial

  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom p₂ (p₁ ⁻¹ᵁ U)
  obtain ⟨eV, heV⟩ := Scheme.TwoAffineOpenCover.exists_algEquiv_sections_baseChange f U hU k
  have hηV : η ∈ p₁ ⁻¹ᵁ U := hzU
  have hV : IsAffineOpen (p₁ ⁻¹ᵁ U) :=
    IsAffine.of_isIso (Scheme.TwoAffineOpenCover.AffineBaseChange.pullbackAffineOpenIsoSpecTensor f k U hU).hom

  let 𝔓 : Ideal Γ(Xk, p₁ ⁻¹ᵁ U) := (hV.primeIdealOf ⟨η, hηV⟩).asIdeal
  obtain ⟨θ, hθ⟩ := StalkBC.exists_residueField_equiv_of_isAffineOpen hV ⟨η, hηV⟩

  have hloc : @IsLocalization.AtPrime _ _ (X.presheaf.stalk zz) _ (X.presheaf.algebra_section_stalk ⟨zz, hzU⟩)
      (hU.primeIdealOf ⟨zz, hzU⟩).asIdeal _ := hU.isLocalization_stalk ⟨zz, hzU⟩

  let B' := Γ(Xk, p₁ ⁻¹ᵁ U)
  let ρ : Γ(X, U) →+* B' := (p₁.app U).hom
  have hρ : ρ = (p₁.appLE U (p₁ ⁻¹ᵁ U) le_rfl).hom := by
    simp only [ρ, Scheme.Hom.appLE_eq_app]
  have hcomap : (hV.primeIdealOf ⟨η, hηV⟩).comap (p₁.appLE U (p₁ ⁻¹ᵁ U) le_rfl).hom = hU.primeIdealOf ⟨zz, hzU⟩ :=
    IsAffineOpen.comap_primeIdealOf_appLE U hU (p₁ ⁻¹ᵁ U) hV le_rfl hηV

  letI := X.presheaf.algebra_section_stalk (⟨zz, hzU⟩ : ↥U)

  have T1 : ∀ r : R, algebraMap R (X.presheaf.stalk zz) r =
      algebraMap Γ(X, U) (X.presheaf.stalk zz) (algebraMap R Γ(X, U) r) := by
    intro r
    change (X.presheaf.germ ⊤ zz trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (X.presheaf.germ U zz hzU).hom ((f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    change _ = (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.germ U zz hzU).hom (f.appTop.hom _)
    rw [TopCat.Presheaf.germ_res]

  have T2 : ∀ r : R, ρ (algebraMap R Γ(X, U) r) = algebraMap k B' (algebraMap R k r) := by
    intro r
    have L : ρ (algebraMap R Γ(X, U) r) =
        (Xk.presheaf.map (homOfLE (le_top : p₁ ⁻¹ᵁ U ≤ ⊤)).op).hom ((p₁ ≫ f).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
      change (p₁.app U).hom ((f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.appLE]
      change ((f.app ⊤ ≫ X.presheaf.map (homOfLE le_top).op) ≫ p₁.app U).hom _ = _
      rw [Category.assoc]
      first
        | rw [p₁.naturality ((homOfLE (le_top : U ≤ ⊤)).op)]
        | erw [p₁.naturality ((homOfLE (le_top : U ≤ ⊤)).op)]
      rfl
    have Rt : algebraMap k B' (algebraMap R k r) =
        (Xk.presheaf.map (homOfLE (le_top : p₁ ⁻¹ᵁ U ≤ ⊤)).op).hom ((p₂ ≫ g).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
      change (p₂.appLE ⊤ (p₁ ⁻¹ᵁ U) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (algebraMap R k r)) = _
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.appLE]
      have hn := congrArg (fun φ : CommRingCat.of R ⟶ _ => φ.hom r)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R k)))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
      rw [hn]
      rfl
    rw [L, Rt, pullback.condition]

  haveI : 𝔓.IsPrime := (hV.primeIdealOf ⟨η, hηV⟩).isPrime
  haveI : IsScalarTower R Γ(X, U) (X.presheaf.stalk zz) := IsScalarTower.of_algebraMap_eq T1
  haveI : IsLocalization.AtPrime (X.presheaf.stalk zz) (hU.primeIdealOf ⟨zz, hzU⟩).asIdeal := hloc
  have hcomap' : 𝔓.comap ρ = (hU.primeIdealOf ⟨zz, hzU⟩).asIdeal := by
    have := congrArg PrimeSpectrum.asIdeal hcomap
    rw [PrimeSpectrum.comap_asIdeal, ← hρ] at this
    exact this
  obtain ⟨σ, hσ, 𝔮, h𝔮, ψ₁, hψσ, hψc, hmemq⟩ :=
    StalkBC.core (R := R) (k := k) (B := Γ(X, U)) (S := X.presheaf.stalk zz) (B' := B')
      (hU.primeIdealOf ⟨zz, hzU⟩).asIdeal ρ T2 eV heV 𝔓 hcomap'

  have hθσ : ∀ s : X.presheaf.stalk zz, θ ((Xk.residue η).hom ((p₁.stalkMap η).hom s)) = σ s := by
    have hg : ∀ b : Γ(X, U), (p₁.stalkMap η).hom ((X.presheaf.germ U zz hzU).hom b) =
        (Xk.presheaf.germ (p₁ ⁻¹ᵁ U) η hηV).hom (ρ b) := fun b => by
      have := Scheme.Hom.germ_stalkMap p₁ U η hzU
      exact congrArg (fun φ => φ.hom b) this
    have key : ∀ b : Γ(X, U), θ ((Xk.residue η).hom ((p₁.stalkMap η).hom ((X.presheaf.germ U zz hzU).hom b))) =
        σ ((X.presheaf.germ U zz hzU).hom b) := fun b => by
      rw [hg, hθ]
      exact (hσ b).symm
    let Lh : X.presheaf.stalk zz →+* 𝔓.ResidueField :=
      θ.toRingHom.comp ((Xk.residue η).hom.comp (p₁.stalkMap η).hom)
    have hext : Lh = σ :=
      IsLocalization.ringHom_ext (hU.primeIdealOf ⟨zz, hzU⟩).asIdeal.primeCompl (RingHom.ext fun b => key b)
    intro s
    exact congrArg (fun F : X.presheaf.stalk zz →+* 𝔓.ResidueField => F s) hext

  letI algkκ : Algebra k 𝔓.ResidueField := ((algebraMap B' 𝔓.ResidueField).comp (algebraMap k B')).toAlgebra
  have hkκ : ∀ c : k, algebraMap k 𝔓.ResidueField c = algebraMap B' 𝔓.ResidueField (algebraMap k B' c) := fun c => rfl
  let ψr : Xk.residueField η ≃+* FractionRing ((k ⊗[R] X.presheaf.stalk zz) ⧸ 𝔮) := θ.trans ψ₁
  have hψr : ∀ x, ψr x = ψ₁ (θ x) := fun x => rfl

  have hconst : ∀ c : k, algebraMap k (Xk.residueField η) c =
      (Xk.residue η).hom ((Xk.presheaf.germ (p₁ ⁻¹ᵁ U) η hηV).hom (algebraMap k B' c)) := by
    intro c
    change (Xk.residue η).hom ((Xk.presheaf.germ ⊤ η trivial).hom (p₂.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))) =
      (Xk.residue η).hom ((Xk.presheaf.germ (p₁ ⁻¹ᵁ U) η hηV).hom ((p₂.appLE ⊤ (p₁ ⁻¹ᵁ U) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)))
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    change _ = (Xk.residue η).hom ((Xk.presheaf.map (homOfLE le_top).op ≫ Xk.presheaf.germ (p₁ ⁻¹ᵁ U) η hηV).hom _)
    rw [TopCat.Presheaf.germ_res]
    rfl
  have hψk : ∀ c : k, ψr (algebraMap k (Xk.residueField η) c) =
      algebraMap k (FractionRing ((k ⊗[R] X.presheaf.stalk zz) ⧸ 𝔮)) c := by
    intro c
    have hR : algebraMap k (FractionRing ((k ⊗[R] X.presheaf.stalk zz) ⧸ 𝔮)) c =
        Localization.mk (Ideal.Quotient.mk 𝔮 (c ⊗ₜ[R] (1 : X.presheaf.stalk zz))) 1 := by
      rw [Localization.mk_one_eq_algebraMap,
        IsScalarTower.algebraMap_apply k ((k ⊗[R] X.presheaf.stalk zz) ⧸ 𝔮) (FractionRing ((k ⊗[R] X.presheaf.stalk zz) ⧸ 𝔮)) c,
        IsScalarTower.algebraMap_apply k (k ⊗[R] X.presheaf.stalk zz) ((k ⊗[R] X.presheaf.stalk zz) ⧸ 𝔮) c,
        Ideal.Quotient.algebraMap_eq, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [hψr, hconst, hθ, ← hkκ, hψc, hR]
  let ψ : Xk.residueField η ≃ₐ[k] FractionRing ((k ⊗[R] X.presheaf.stalk zz) ⧸ 𝔮) := AlgEquiv.ofRingEquiv (f := ψr) hψk
  have hψ : ∀ x, ψ x = ψ₁ (θ x) := fun x => rfl
  refine ⟨𝔮, h𝔮, ψ, fun s => ?_, fun hgenpt => ?_⟩
  · rw [hψ, hθσ, hψσ]
  ·
    have hmin : ∀ 𝔓' : Ideal B', 𝔓'.IsPrime → 𝔓' ≤ 𝔓 → 𝔓' = 𝔓 := by
      intro 𝔓' hP' hle
      let P' : PrimeSpectrum B' := ⟨𝔓', hP'⟩
      have hsp : P' ⤳ hV.primeIdealOf ⟨η, hηV⟩ := (PrimeSpectrum.le_iff_specializes P' _).mp hle
      have hsp' : hV.fromSpec.base P' ⤳ hV.fromSpec.base (hV.primeIdealOf ⟨η, hηV⟩) :=
        hsp.map hV.fromSpec.continuous
      rw [IsAffineOpen.fromSpec_primeIdealOf] at hsp'
      have heq : hV.fromSpec.base P' = η := hgenpt _ hsp'
      have hinj : Function.Injective hV.fromSpec.base := hV.fromSpec.isOpenEmbedding.injective
      have hP : P' = hV.primeIdealOf ⟨η, hηV⟩ :=
        hinj (heq.trans (IsAffineOpen.fromSpec_primeIdealOf hV ⟨η, hηV⟩).symm)
      exact congrArg PrimeSpectrum.asIdeal hP

    let 𝔓₀ : Ideal (k ⊗[R] Γ(X, U)) := 𝔓.comap eV.toRingEquiv.toRingHom
    have hmem₀ : ∀ x, x ∈ 𝔓₀ ↔ eV x ∈ 𝔓 := fun x => Ideal.mem_comap
    have hmin₀ : ∀ Q : Ideal (k ⊗[R] Γ(X, U)), Q.IsPrime → Q ≤ 𝔓₀ → Q = 𝔓₀ := by
      intro Q hQ hQle
      have h1 : Q.comap eV.symm.toRingEquiv.toRingHom = 𝔓 := by
        apply hmin _ (Ideal.comap_isPrime _ _)
        intro y hy
        have hy' : eV.symm y ∈ Q := Ideal.mem_comap.mp hy
        have := (hmem₀ _).mp (hQle hy')
        rwa [AlgEquiv.apply_symm_apply] at this
      ext x
      rw [hmem₀, ← h1, Ideal.mem_comap]
      change x ∈ Q ↔ eV.symm (eV x) ∈ Q
      rw [AlgEquiv.symm_apply_apply]

    letI algL : Algebra (k ⊗[R] Γ(X, U)) (k ⊗[R] X.presheaf.stalk zz) :=
      (Algebra.TensorProduct.map (AlgHom.id k k) (IsScalarTower.toAlgHom R Γ(X, U) (X.presheaf.stalk zz))).toRingHom.toAlgebra
    haveI := StalkBC.presentation R k Γ(X, U) (X.presheaf.stalk zz) (hU.primeIdealOf ⟨zz, hzU⟩).asIdeal.primeCompl
    haveI := h𝔮
    have hcomapq : 𝔮.comap (algebraMap (k ⊗[R] Γ(X, U)) (k ⊗[R] X.presheaf.stalk zz)) = 𝔓₀ := by
      ext x
      rw [Ideal.mem_comap, hmem₀]
      exact hmemq x
    exact StalkBC.minimal ((hU.primeIdealOf ⟨zz, hzU⟩).asIdeal.primeCompl.map
      (Algebra.TensorProduct.includeRight : Γ(X, U) →ₐ[R] k ⊗[R] Γ(X, U))) 𝔓₀ hmin₀ 𝔮 hcomapq

#print axioms solution

end S_AlgebraicGeometry_exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient (solution)
