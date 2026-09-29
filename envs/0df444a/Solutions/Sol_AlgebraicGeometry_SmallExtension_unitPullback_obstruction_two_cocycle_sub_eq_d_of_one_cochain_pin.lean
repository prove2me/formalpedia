-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.unitPullback_obstruction_two_cocycle_sub_eq_d_of_one_cochain_pin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/88b87482-45f7-54a8-bf78-b4e79d63fb6a

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_add
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_of_isPullback_of_comp_mono
import Theorems.Thm_AlgebraicGeometry_exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_mul_comp_eq
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_map_app_of_specMap_comp_fromSpec_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_defect_eq_sign_smul_of_pin
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_unitPullback_obstruction_two_cocycle_sub_eq_d_of_one_cochain_pin
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 256000000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

p2m_open "AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

namespace N2GAux

p2m_open "AlgebraicGeometry.Scheme.OrderedAffineCover"

theorem spec_map_comp_isoSpec_inv {Y : Scheme.{u}} {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ U) :
    Spec.map (Y.presheaf.map (homOfLE e).op) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ Y.homOfLE e := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι]
  exact hU.map_fromSpec hV (homOfLE e).op

theorem specMap_mk_comp_eq_of_isTangentCoordsOfPairAtVia
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]
    {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Y) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hc : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue c) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v := by
  obtain ⟨w₀, hw₀, w₁, ⟨ϑ, hϑ, φ, hu, hv, hw⟩, -, -⟩ := hc
  have key : (Ideal.Quotient.mk (I.map (algebraMap T' C))).comp (pairFst I C) =
      (Ideal.Quotient.mk (I.map (algebraMap T' C))).comp (pairSnd I C) :=
    RingHom.ext fun x => (mem_pairRing I C).mp x.2
  rw [← hu, ← hv, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, key]

end N2GAux

namespace OB4aGlue

noncomputable def rmap {X Y : Scheme.{u}} (U : X.Opens) (V : Y.Opens) (θ : (U : Scheme.{u}) ⟶ V) :
    Γ(Y, V) ⟶ Γ(X, U) :=
  V.topIso.inv ≫ θ.appTop ≫ U.topIso.hom

theorem toSpecΓ_rmap {X Y : Scheme.{u}} (U : X.Opens) (V : Y.Opens) (θ : (U : Scheme.{u}) ⟶ V) :
    θ ≫ V.toSpecΓ = U.toSpecΓ ≫ Spec.map (rmap U V θ) := by
  simp only [Scheme.Opens.toSpecΓ, rmap, Spec.map_comp, Category.assoc]
  rw [reassoc_of% (Scheme.toSpecΓ_naturality θ), ← Spec.map_comp_assoc, Iso.hom_inv_id]
  erw [Spec.map_id, Category.id_comp]

theorem isoSpec_rmap {X Y : Scheme.{u}} {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (θ : (U : Scheme.{u}) ⟶ V) : θ ≫ hV.isoSpec.hom = hU.isoSpec.hom ≫ Spec.map (rmap U V θ) := by
  rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]; exact toSpecΓ_rmap U V θ

@[reassoc]
theorem specMap_rmap_isoSpec_inv {X Y : Scheme.{u}} {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (θ : (U : Scheme.{u}) ⟶ V) :
    Spec.map (rmap U V θ) ≫ hV.isoSpec.inv = hU.isoSpec.inv ≫ θ := by
  rw [Iso.comp_inv_eq, Category.assoc, isoSpec_rmap hU hV, Iso.inv_hom_id_assoc]

end OB4aGlue

namespace ViaTorsor

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Y)
    (haW : IsPullback aW (W.ι ≫ xk) qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

include hI hsmall hι hιI haW hUe e₁ he₁

theorem via_self (u : Spec (CommRingCat.of C) ⟶ Y) (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C))) :
    IsTangentCoordsOfPairAtVia I V ι C u u xk Lk W aW Ue 0 := by
  obtain ⟨c, hc⟩ := exists_isTangentCoordsOfPairAtVia I hI hsmall V ι hι hιI C qY u hu xk Lk W aW haW Ue hUe e₁ he₁ u hu rfl
  have h := isTangentCoordsOfPairAtVia_add I hI hsmall V ι hι hιI C qY u u u hu hu hu rfl rfl xk Lk W aW haW Ue hUe e₁ he₁ c c c hc hc hc
  have hc0 : c = 0 := by
    funext a
    have := congrFun h a
    rw [Pi.add_apply] at this
    rw [Pi.zero_apply]
    exact left_eq_add.mp this
  rwa [hc0] at hc

theorem via_unique (u v : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    {D D' : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))}
    (hD : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue D)
    (hD' : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue D') : D = D' := by
  have h0 := via_self I hI hsmall V ι hι hιI C qY xk Lk W aW haW Ue hUe e₁ he₁ v hv
  have h := isTangentCoordsOfPairAtVia_add I hI hsmall V ι hι hιI C qY u v v hu hv hv huv rfl xk Lk W aW haW Ue hUe e₁ he₁ D 0 D' hD h0 hD'
  rw [add_zero] at h
  exact h.symm

theorem via_symm (u v : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    {D : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))}
    (hD : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue D) :
    IsTangentCoordsOfPairAtVia I V ι C v u xk Lk W aW Ue (-D) := by
  obtain ⟨c, hc⟩ := exists_isTangentCoordsOfPairAtVia I hI hsmall V ι hι hιI C qY v hv xk Lk W aW haW Ue hUe e₁ he₁ u hu huv.symm
  have h0 := via_self I hI hsmall V ι hι hιI C qY xk Lk W aW haW Ue hUe e₁ he₁ u hu
  have h := isTangentCoordsOfPairAtVia_add I hI hsmall V ι hι hιI C qY u v u hu hv hu huv huv.symm xk Lk W aW haW Ue hUe e₁ he₁ D c 0 hD hc h0
  have : c = -D := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h.symm
  rwa [this] at hc

theorem via_trans (u v w : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hw : w ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    (hvw : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ w)
    {D₁ D₂ : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))}
    (h₁ : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue D₁)
    (h₂ : IsTangentCoordsOfPairAtVia I V ι C v w xk Lk W aW Ue D₂) :
    IsTangentCoordsOfPairAtVia I V ι C u w xk Lk W aW Ue (D₁ + D₂) := by
  obtain ⟨c, hc⟩ := exists_isTangentCoordsOfPairAtVia I hI hsmall V ι hι hιI C qY u hu xk Lk W aW haW Ue hUe e₁ he₁ w hw (huv.trans hvw)
  have h := isTangentCoordsOfPairAtVia_add I hI hsmall V ι hι hιI C qY u v w hu hv hw huv hvw xk Lk W aW haW Ue hUe e₁ he₁ D₁ D₂ c h₁ h₂ hc
  rwa [h] at hc

end ViaTorsor

open N2GAux OB4aGlue

namespace N2Aux

theorem fromSpec_comp_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := algebraOfHom f U
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU
    (show U ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem flat_sections {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [hf : Flat f] {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    Module.Flat R Γ(X, U) := by
  have h := HasRingHomProperty.appLE @Flat f hf ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  have h' : RingHom.Flat ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact h'

theorem exists_gamma {A₀ Ya : Scheme.{u}} (U : A₀.Opens) (g : (↑U : Scheme.{u}) ⟶ Ya) (O : A₀.Opens → Ya.Opens)
    (hO : ∀ W : A₀.Opens, g ⁻¹ᵁ O W = U.ι ⁻¹ᵁ W) (W : A₀.Opens) (hW : W ≤ U) :
    ∃ γ : (↑W : Scheme.{u}) ⟶ ↑(O W), γ ≫ (O W).ι = A₀.homOfLE hW ≫ g := by
  have hrange : Set.range (A₀.homOfLE hW ≫ g).base ⊆ Set.range (O W).ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (A₀.homOfLE hW ≫ g).base p ∈ (O W : Set Ya)
    have : (A₀.homOfLE hW).base p ∈ (g ⁻¹ᵁ O W : Set U) := by
      rw [hO]
      change ((A₀.homOfLE hW ≫ U.ι).base p) ∈ (W : Set A₀)
      rw [Scheme.homOfLE_ι]
      exact p.2
    exact this
  exact ⟨IsOpenImmersion.lift (O W).ι (A₀.homOfLE hW ≫ g) hrange, IsOpenImmersion.lift_fac _ _ _⟩

end N2Aux

open N2Aux

theorem N2G.xread
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))

    (σ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      ((ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))) ≃+* Γ(Ak, (𝒰.comap i₀).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σ s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))).toRingHom) ≫
          (hOaff (s.1 0) (𝒰.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 s) (𝒰.inter_le s 0)).fromSpec =
        Ak.homOfLE (𝒰.comap_inter_le i₀ s) ≫ (i₀ ∣_ 𝒰.inter s) ≫ A₀.homOfLE (𝒰.inter_le s 0) ≫ g (s.1 0))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒰.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
      σ s (x ⊗ₜ[T'] (1 : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)))) = algebraMap (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter s) x)

    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)

    (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
    (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (hρab : ∀ r : 𝒰.Idx 2,
      (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
          (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρbc : ∀ r : 𝒰.Idx 2,
      (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
        (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
          (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρac : ∀ r : 𝒰.Idx 2,
      (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
          (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ω : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2)))
    (hω : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      letI := algebraOfHom fk Ue
      ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs ∧
        ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ r (cs a ξ) = ω.1 a ξ r)
    (hωZ : letI := algebraOfHom fk Ue
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fk).d (𝒰.comap i₀) 2 (ω.1 a ξ) = 0)
    {X₀ : Scheme.{u}} (fX₀ : X₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated fX₀] [Smooth fX₀]

    (𝒱 : X₀.OrderedAffineCover)
    (Z : 𝒱.ι → Scheme.{u}) (qZ : ∀ a, Z a ⟶ Spec (CommRingCat.of T')) (hqZ : ∀ a, Smooth (qZ a))
    (gZ : ∀ a, (↑(𝒱.U a) : Scheme.{u}) ⟶ Z a)
    (hgZ : ∀ a, IsPullback (gZ a) ((𝒱.U a).ι ≫ fX₀) (qZ a) (Spec.map (CommRingCat.ofHom π)))

    {Xk : Scheme.{u}} (fXk : Xk ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fXk]
    (LX : RelativeGroupLaw (ResidueField T') fXk)
    (j₀ : Xk ⟶ X₀) [IsAffineHom j₀] (hj₀ : IsPullback j₀ fXk fX₀ (Spec.map (CommRingCat.ofHom ρ)))
    (UXe : Xk.Opens) (hUXe : IsAffineOpen UXe)
    (eX₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (UXe : Scheme.{u})) (heX₁ : eX₁ ≫ UXe.ι = (LX.one (𝟙 _)).1)

    (OX : ∀ a, X₀.Opens → (Z a).Opens)
    (hOX : ∀ (a : 𝒱.ι) (W : X₀.Opens), gZ a ⁻¹ᵁ OX a W = (𝒱.U a).ι ⁻¹ᵁ W)
    (hOXm : ∀ a, Monotone (OX a))
    (hOXtop : ∀ a, OX a (𝒱.U a) = ⊤)
    (hOXinf : ∀ (a : 𝒱.ι) (W W' : X₀.Opens), OX a W ⊓ OX a W' ≤ OX a (W ⊓ W'))
    (hOXaff : ∀ (a : 𝒱.ι) (W : X₀.Opens), IsAffineOpen W → W ≤ 𝒱.U a → IsAffineOpen (OX a W))

    (σX : ∀ {n : ℕ} (s : 𝒱.Idx n),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      ((ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))) ≃+* Γ(Xk, (𝒱.comap j₀).inter s))
    (hσX₁ : ∀ {n : ℕ} (s : 𝒱.Idx n),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σX s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))).toRingHom) ≫
          (hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).fromSpec =
        Xk.homOfLE (𝒱.comap_inter_le j₀ s) ≫ (j₀ ∣_ 𝒱.inter s) ≫ X₀.homOfLE (𝒱.inter_le s 0) ≫ gZ (s.1 0))
    (hσX₂ : ∀ {n : ℕ} (s : 𝒱.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      letI := algebraOfHom fXk ((𝒱.comap j₀).inter s)
      σX s (x ⊗ₜ[T'] (1 : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) = algebraMap (ResidueField T') Γ(Xk, (𝒱.comap j₀).inter s) x)

    (φX : ∀ (a b : 𝒱.ι), a < b → ((↑(OX a (𝒱.U a ⊓ 𝒱.U b)) : Scheme.{u}) ≅ ↑(OX b (𝒱.U a ⊓ 𝒱.U b))))
    (hφXq : ∀ (a b : 𝒱.ι) (h : a < b),
      (φX a b h).hom ≫ (OX b (𝒱.U a ⊓ 𝒱.U b)).ι ≫ qZ b = (OX a (𝒱.U a ⊓ 𝒱.U b)).ι ≫ qZ a)
    (hφXg : ∀ (a b : 𝒱.ι) (h : a < b),
      ∃ (γ : (↑(𝒱.U a ⊓ 𝒱.U b) : Scheme.{u}) ⟶ ↑(OX a (𝒱.U a ⊓ 𝒱.U b)))
        (γ' : (↑(𝒱.U a ⊓ 𝒱.U b) : Scheme.{u}) ⟶ ↑(OX b (𝒱.U a ⊓ 𝒱.U b))),
        γ ≫ (OX a (𝒱.U a ⊓ 𝒱.U b)).ι = X₀.homOfLE inf_le_left ≫ gZ a ∧
        γ' ≫ (OX b (𝒱.U a ⊓ 𝒱.U b)).ι = X₀.homOfLE inf_le_right ≫ gZ b ∧
        γ ≫ (φX a b h).hom = γ')
    (hφXO : ∀ (a b : 𝒱.ι) (h : a < b) (W : X₀.Opens),
      (φX a b h).hom ⁻¹ᵁ ((OX b (𝒱.U a ⊓ 𝒱.U b)).ι ⁻¹ᵁ OX b W) = (OX a (𝒱.U a ⊓ 𝒱.U b)).ι ⁻¹ᵁ OX a W)

    (ρXab : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 0) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 1) (𝒱.inter r))))
    (ρXbc : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 1) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 2) (𝒱.inter r))))
    (ρXac : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 0) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 2) (𝒱.inter r))))
    (hρXab : ∀ r : 𝒱.Idx 2,
      (ρXab r).hom ≫ (Z (r.1 1)).homOfLE (hOXm (r.1 1) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 1))) =
        (Z (r.1 0)).homOfLE (hOXm (r.1 0) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 1))) ≫
          (φX (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρXbc : ∀ r : 𝒱.Idx 2,
      (ρXbc r).hom ≫ (Z (r.1 2)).homOfLE (hOXm (r.1 2) (le_inf (𝒱.inter_le r 1) (𝒱.inter_le r 2))) =
        (Z (r.1 1)).homOfLE (hOXm (r.1 1) (le_inf (𝒱.inter_le r 1) (𝒱.inter_le r 2))) ≫
          (φX (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρXac : ∀ r : 𝒱.Idx 2,
      (ρXac r).hom ≫ (Z (r.1 2)).homOfLE (hOXm (r.1 2) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 2))) =
        (Z (r.1 0)).homOfLE (hOXm (r.1 0) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 2))) ≫
          (φX (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ωX : letI := algebraOfHom fXk UXe
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Xk, UXe)
          ((UXe.topIso.inv ≫ eX₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fXk).cochain (𝒱.comap j₀) 2)))
    (hωX : ∀ r : 𝒱.Idx 2,
      letI := algebraOfHom (qZ (r.1 0)) (OX (r.1 0) (𝒱.inter r))
      letI := algebraOfHom fXk UXe
      ∃ cs : Γ(Xk, UXe) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Z (r.1 0), OX (r.1 0) (𝒱.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (r.1 0), OX (r.1 0) (𝒱.inter r))
          ((hOXaff (r.1 0) (𝒱.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 r) (𝒱.inter_le r 0)).isoSpec.inv ≫
              (ρXac r).hom ≫ (OX (r.1 2) (𝒱.inter r)).ι)
          ((hOXaff (r.1 0) (𝒱.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 r) (𝒱.inter_le r 0)).isoSpec.inv ≫
              (ρXab r).hom ≫ (ρXbc r).hom ≫ (OX (r.1 2) (𝒱.inter r)).ι)
          fXk LX (j₀ ⁻¹ᵁ 𝒱.U (r.1 2)) ((j₀ ∣_ 𝒱.U (r.1 2)) ≫ gZ (r.1 2)) UXe cs ∧
        ∀ (a : Γ(Xk, UXe)) (ξ : Module.Dual (ResidueField T') V), σX r (cs a ξ) = ωX.1 a ξ r)
    (hωXZ : letI := algebraOfHom fXk UXe
      ∀ (a : Γ(Xk, UXe)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fXk).d (𝒱.comap j₀) 2 (ωX.1 a ξ) = 0)

    (h₀ : X₀ ⟶ A₀) (hh₀ : h₀ ≫ f₀ = fX₀)
    (lam : 𝒱.ι → 𝒰.ι) (hlam₀ : ∀ w, 𝒱.U w ≤ h₀ ⁻¹ᵁ 𝒰.U (lam w))
    (hk : Xk ⟶ Ak) (hhk : hk ≫ i₀ = j₀ ≫ h₀) (hhkf : hk ≫ fk = fXk)
    (hhom : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fXk),
      (LX.mul t P Q).1 ≫ hk =
        (Lk.mul t ⟨P.1 ≫ hk, by rw [Category.assoc, hhkf, P.2]⟩ ⟨Q.1 ≫ hk, by rw [Category.assoc, hhkf, Q.2]⟩).1)
    (hUX : UXe ≤ hk ⁻¹ᵁ Ue)
    (hlamk : ∀ w, (𝒱.comap j₀).U w ≤ hk ⁻¹ᵁ (𝒰.comap i₀).U (lam w))
    (hZ : ∀ w, Z w ⟶ Y (lam w)) (hhZq : ∀ w, hZ w ≫ q (lam w) = qZ w)
    (hhZg : ∀ w, gZ w ≫ hZ w = X₀.homOfLE (hlam₀ w) ≫ (h₀ ∣_ 𝒰.U (lam w)) ≫ g (lam w))

    (Φ : ∀ (a b : 𝒰.ι) (W : A₀.Opens), W ≤ 𝒰.U a → W ≤ 𝒰.U b → ((↑(O a W) : Scheme.{u}) ≅ ↑(O b W)))
    (hΦq : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (O b W).ι ≫ q b = (O a W).ι ≫ q a)
    (hΦg : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b)
      (γ : (↑W : Scheme.{u}) ⟶ ↑(O a W)) (γ' : (↑W : Scheme.{u}) ⟶ ↑(O b W)),
      γ ≫ (O a W).ι = A₀.homOfLE ha ≫ g a → γ' ≫ (O b W).ι = A₀.homOfLE hb ≫ g b → γ ≫ (Φ a b W ha hb).hom = γ')
    (hΦres : ∀ (a b : 𝒰.ι) (W W' : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (ha' : W' ≤ 𝒰.U a) (hb' : W' ≤ 𝒰.U b)
      (hWW : W' ≤ W),
      (Φ a b W' ha' hb').hom ≫ (Y b).homOfLE (hOm b hWW) = (Y a).homOfLE (hOm a hWW) ≫ (Φ a b W ha hb).hom)
    (hΦrefl : ∀ (a : 𝒰.ι) (W : A₀.Opens) (ha ha' : W ≤ 𝒰.U a), (Φ a a W ha ha').hom = 𝟙 _)
    (hΦsymm : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (Φ b a W hb ha).hom = 𝟙 _)
    (hΦφ : ∀ (a b : 𝒰.ι) (h : a < b), (Φ a b (𝒰.U a ⊓ 𝒰.U b) inf_le_left inf_le_right).hom = (φ a b h).hom)

    (ΦX : ∀ (x y : 𝒱.ι), x < y → ∀ (W : X₀.Opens), W ≤ 𝒱.U x ⊓ 𝒱.U y → ((↑(OX x W) : Scheme.{u}) ≅ ↑(OX y W)))
    (hΦX : ∀ (x y : 𝒱.ι) (h : x < y) (W : X₀.Opens) (hW : W ≤ 𝒱.U x ⊓ 𝒱.U y),
      (ΦX x y h W hW).hom ≫ (Z y).homOfLE (hOXm y hW) = (Z x).homOfLE (hOXm x hW) ≫ (φX x y h).hom)

    (ℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens), WX ≤ h₀ ⁻¹ᵁ WA → ((↑(OX x WX) : Scheme.{u}) ⟶ ↑(O (lam x) WA)))
    (hℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens) (h : WX ≤ h₀ ⁻¹ᵁ WA),
      ℓ x WX WA h ≫ (O (lam x) WA).ι = (OX x WX).ι ≫ hZ x)
    (s : 𝒱.Idx 2)
    (csX : letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      letI := algebraOfHom fXk UXe
      Γ(Xk, UXe) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))))
    (hcsX : letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      letI := algebraOfHom fXk UXe
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))
        ((hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).isoSpec.inv ≫ (ρXac s).hom ≫ (OX (s.1 2) (𝒱.inter s)).ι)
        ((hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).isoSpec.inv ≫ (ρXab s).hom ≫ (ρXbc s).hom ≫ (OX (s.1 2) (𝒱.inter s)).ι)
        fXk LX (j₀ ⁻¹ᵁ 𝒱.U (s.1 2)) ((j₀ ∣_ 𝒱.U (s.1 2)) ≫ gZ (s.1 2)) UXe csX) :
    letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
    letI := algebraOfHom fk Ue
    letI := algebraOfHom fXk UXe
    IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))
      ((hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).isoSpec.inv ≫ (ΦX (s.1 0) (s.1 2) (s.2 (by decide)) (𝒱.inter s) (le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 2))).hom ≫ ℓ (s.1 2) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) (by rw [Scheme.OrderedAffineCover.preimage_iInf_fin]; exact le_iInf fun j => (𝒱.inter_le s j).trans (hlam₀ (s.1 j))) ≫ (O (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι)
      ((hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).isoSpec.inv ≫ (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter s) (le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1))).hom ≫ (ΦX (s.1 1) (s.1 2) (s.2 (by decide)) (𝒱.inter s) (le_inf (𝒱.inter_le s 1) (𝒱.inter_le s 2))).hom ≫ ℓ (s.1 2) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) (by rw [Scheme.OrderedAffineCover.preimage_iInf_fin]; exact le_iInf fun j => (𝒱.inter_le s j).trans (hlam₀ (s.1 j))) ≫ (O (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι)
      fk Lk (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))) ((i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))) Ue
      (fun a => csX ((Xk.presheaf.map (homOfLE hUX).op).hom ((hk.app Ue).hom a))) := by
  classical
  letI instC : Algebra T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
  letI instA : Algebra (ResidueField T') Γ(Ak, Ue) := algebraOfHom fk Ue
  letI instX : Algebra (ResidueField T') Γ(Xk, UXe) := algebraOfHom fXk UXe
  have hs01 : 𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1) := le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1)
  have hs02 : 𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 2) := le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 2)
  have hs12 : 𝒱.inter s ≤ 𝒱.U (s.1 1) ⊓ 𝒱.U (s.1 2) := le_inf (𝒱.inter_le s 1) (𝒱.inter_le s 2)
  have hVW : 𝒱.inter s ≤ h₀ ⁻¹ᵁ (⨅ j, 𝒰.U (lam (s.1 j))) := by
    rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
    exact le_iInf fun j => (𝒱.inter_le s j).trans (hlam₀ (s.1 j))

  have eac : (ρXac s).hom = (ΦX (s.1 0) (s.1 2) (s.2 (by decide)) (𝒱.inter s) hs02).hom := by
    rw [← cancel_mono ((Z (s.1 2)).homOfLE (hOXm (s.1 2) hs02)), hΦX]
    exact hρXac s
  have eab : (ρXab s).hom = (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter s) hs01).hom := by
    rw [← cancel_mono ((Z (s.1 1)).homOfLE (hOXm (s.1 1) hs01)), hΦX]
    exact hρXab s
  have ebc : (ρXbc s).hom = (ΦX (s.1 1) (s.1 2) (s.2 (by decide)) (𝒱.inter s) hs12).hom := by
    rw [← cancel_mono ((Z (s.1 2)).homOfLE (hOXm (s.1 2) hs12)), hΦX]
    exact hρXbc s

  have hW2 : j₀ ⁻¹ᵁ 𝒱.U (s.1 2) ≤ hk ⁻¹ᵁ (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))) := hlamk (s.1 2)
  have hcompat : Xk.homOfLE hW2 ≫ (hk ∣_ (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2)))) ≫
      (i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2)) = ((j₀ ∣_ 𝒱.U (s.1 2)) ≫ gZ (s.1 2)) ≫ hZ (s.1 2) := by
    have H1 : (Xk.homOfLE hW2 ≫ (hk ∣_ (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2)))) ≫ (i₀ ∣_ 𝒰.U (lam (s.1 2)))) ≫
        (𝒰.U (lam (s.1 2))).ι = (j₀ ⁻¹ᵁ 𝒱.U (s.1 2)).ι ≫ hk ≫ i₀ := by
      rw [Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc]
    have H2 : ((j₀ ∣_ 𝒱.U (s.1 2)) ≫ X₀.homOfLE (hlam₀ (s.1 2)) ≫ (h₀ ∣_ 𝒰.U (lam (s.1 2)))) ≫
        (𝒰.U (lam (s.1 2))).ι = (j₀ ⁻¹ᵁ 𝒱.U (s.1 2)).ι ≫ j₀ ≫ h₀ := by
      rw [Category.assoc, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc, morphismRestrict_ι_assoc]
    have H : Xk.homOfLE hW2 ≫ (hk ∣_ (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2)))) ≫ (i₀ ∣_ 𝒰.U (lam (s.1 2))) =
        (j₀ ∣_ 𝒱.U (s.1 2)) ≫ X₀.homOfLE (hlam₀ (s.1 2)) ≫ (h₀ ∣_ 𝒰.U (lam (s.1 2))) := by
      rw [← cancel_mono (𝒰.U (lam (s.1 2))).ι, H1, H2, hhk]
    calc Xk.homOfLE hW2 ≫ (hk ∣_ (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2)))) ≫ (i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))
        = (Xk.homOfLE hW2 ≫ (hk ∣_ (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2)))) ≫ (i₀ ∣_ 𝒰.U (lam (s.1 2)))) ≫ g (lam (s.1 2)) := by
          simp only [Category.assoc]
      _ = ((j₀ ∣_ 𝒱.U (s.1 2)) ≫ X₀.homOfLE (hlam₀ (s.1 2)) ≫ (h₀ ∣_ 𝒰.U (lam (s.1 2)))) ≫ g (lam (s.1 2)) := by rw [H]
      _ = ((j₀ ∣_ 𝒱.U (s.1 2)) ≫ gZ (s.1 2)) ≫ hZ (s.1 2) := by
          simp only [Category.assoc]; rw [hhZg]
  have key := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_mul_comp_eq (RingHom.ker π) V ι
    Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) _ _ fXk LX (j₀ ⁻¹ᵁ 𝒱.U (s.1 2)) ((j₀ ∣_ 𝒱.U (s.1 2)) ≫ gZ (s.1 2)) UXe
    fk Lk (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))) ((i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))) Ue (hZ (s.1 2)) hk hhkf
    hhom hUX hW2 hcompat csX hcsX
  have hl := hℓ (s.1 2) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) hVW
  rw [eac, eab, ebc] at key
  simp only [Category.assoc, ← hl] at key
  exact key

theorem N2G.aread
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))

    (σ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      ((ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))) ≃+* Γ(Ak, (𝒰.comap i₀).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σ s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))).toRingHom) ≫
          (hOaff (s.1 0) (𝒰.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 s) (𝒰.inter_le s 0)).fromSpec =
        Ak.homOfLE (𝒰.comap_inter_le i₀ s) ≫ (i₀ ∣_ 𝒰.inter s) ≫ A₀.homOfLE (𝒰.inter_le s 0) ≫ g (s.1 0))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒰.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
      σ s (x ⊗ₜ[T'] (1 : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)))) = algebraMap (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter s) x)

    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)

    (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
    (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (hρab : ∀ r : 𝒰.Idx 2,
      (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
          (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρbc : ∀ r : 𝒰.Idx 2,
      (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
        (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
          (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρac : ∀ r : 𝒰.Idx 2,
      (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
          (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ω : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2)))
    (hω : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      letI := algebraOfHom fk Ue
      ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs ∧
        ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ r (cs a ξ) = ω.1 a ξ r)
    (hωZ : letI := algebraOfHom fk Ue
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fk).d (𝒰.comap i₀) 2 (ω.1 a ξ) = 0)
    {X₀ : Scheme.{u}} (fX₀ : X₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated fX₀] [Smooth fX₀]

    (𝒱 : X₀.OrderedAffineCover)
    (Z : 𝒱.ι → Scheme.{u}) (qZ : ∀ a, Z a ⟶ Spec (CommRingCat.of T')) (hqZ : ∀ a, Smooth (qZ a))
    (gZ : ∀ a, (↑(𝒱.U a) : Scheme.{u}) ⟶ Z a)
    (hgZ : ∀ a, IsPullback (gZ a) ((𝒱.U a).ι ≫ fX₀) (qZ a) (Spec.map (CommRingCat.ofHom π)))

    {Xk : Scheme.{u}} (fXk : Xk ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fXk]
    (LX : RelativeGroupLaw (ResidueField T') fXk)
    (j₀ : Xk ⟶ X₀) [IsAffineHom j₀] (hj₀ : IsPullback j₀ fXk fX₀ (Spec.map (CommRingCat.ofHom ρ)))
    (UXe : Xk.Opens) (hUXe : IsAffineOpen UXe)
    (eX₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (UXe : Scheme.{u})) (heX₁ : eX₁ ≫ UXe.ι = (LX.one (𝟙 _)).1)

    (OX : ∀ a, X₀.Opens → (Z a).Opens)
    (hOX : ∀ (a : 𝒱.ι) (W : X₀.Opens), gZ a ⁻¹ᵁ OX a W = (𝒱.U a).ι ⁻¹ᵁ W)
    (hOXm : ∀ a, Monotone (OX a))
    (hOXtop : ∀ a, OX a (𝒱.U a) = ⊤)
    (hOXinf : ∀ (a : 𝒱.ι) (W W' : X₀.Opens), OX a W ⊓ OX a W' ≤ OX a (W ⊓ W'))
    (hOXaff : ∀ (a : 𝒱.ι) (W : X₀.Opens), IsAffineOpen W → W ≤ 𝒱.U a → IsAffineOpen (OX a W))

    (σX : ∀ {n : ℕ} (s : 𝒱.Idx n),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      ((ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))) ≃+* Γ(Xk, (𝒱.comap j₀).inter s))
    (hσX₁ : ∀ {n : ℕ} (s : 𝒱.Idx n),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σX s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))).toRingHom) ≫
          (hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).fromSpec =
        Xk.homOfLE (𝒱.comap_inter_le j₀ s) ≫ (j₀ ∣_ 𝒱.inter s) ≫ X₀.homOfLE (𝒱.inter_le s 0) ≫ gZ (s.1 0))
    (hσX₂ : ∀ {n : ℕ} (s : 𝒱.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      letI := algebraOfHom fXk ((𝒱.comap j₀).inter s)
      σX s (x ⊗ₜ[T'] (1 : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) = algebraMap (ResidueField T') Γ(Xk, (𝒱.comap j₀).inter s) x)

    (φX : ∀ (a b : 𝒱.ι), a < b → ((↑(OX a (𝒱.U a ⊓ 𝒱.U b)) : Scheme.{u}) ≅ ↑(OX b (𝒱.U a ⊓ 𝒱.U b))))
    (hφXq : ∀ (a b : 𝒱.ι) (h : a < b),
      (φX a b h).hom ≫ (OX b (𝒱.U a ⊓ 𝒱.U b)).ι ≫ qZ b = (OX a (𝒱.U a ⊓ 𝒱.U b)).ι ≫ qZ a)
    (hφXg : ∀ (a b : 𝒱.ι) (h : a < b),
      ∃ (γ : (↑(𝒱.U a ⊓ 𝒱.U b) : Scheme.{u}) ⟶ ↑(OX a (𝒱.U a ⊓ 𝒱.U b)))
        (γ' : (↑(𝒱.U a ⊓ 𝒱.U b) : Scheme.{u}) ⟶ ↑(OX b (𝒱.U a ⊓ 𝒱.U b))),
        γ ≫ (OX a (𝒱.U a ⊓ 𝒱.U b)).ι = X₀.homOfLE inf_le_left ≫ gZ a ∧
        γ' ≫ (OX b (𝒱.U a ⊓ 𝒱.U b)).ι = X₀.homOfLE inf_le_right ≫ gZ b ∧
        γ ≫ (φX a b h).hom = γ')
    (hφXO : ∀ (a b : 𝒱.ι) (h : a < b) (W : X₀.Opens),
      (φX a b h).hom ⁻¹ᵁ ((OX b (𝒱.U a ⊓ 𝒱.U b)).ι ⁻¹ᵁ OX b W) = (OX a (𝒱.U a ⊓ 𝒱.U b)).ι ⁻¹ᵁ OX a W)

    (ρXab : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 0) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 1) (𝒱.inter r))))
    (ρXbc : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 1) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 2) (𝒱.inter r))))
    (ρXac : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 0) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 2) (𝒱.inter r))))
    (hρXab : ∀ r : 𝒱.Idx 2,
      (ρXab r).hom ≫ (Z (r.1 1)).homOfLE (hOXm (r.1 1) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 1))) =
        (Z (r.1 0)).homOfLE (hOXm (r.1 0) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 1))) ≫
          (φX (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρXbc : ∀ r : 𝒱.Idx 2,
      (ρXbc r).hom ≫ (Z (r.1 2)).homOfLE (hOXm (r.1 2) (le_inf (𝒱.inter_le r 1) (𝒱.inter_le r 2))) =
        (Z (r.1 1)).homOfLE (hOXm (r.1 1) (le_inf (𝒱.inter_le r 1) (𝒱.inter_le r 2))) ≫
          (φX (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρXac : ∀ r : 𝒱.Idx 2,
      (ρXac r).hom ≫ (Z (r.1 2)).homOfLE (hOXm (r.1 2) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 2))) =
        (Z (r.1 0)).homOfLE (hOXm (r.1 0) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 2))) ≫
          (φX (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ωX : letI := algebraOfHom fXk UXe
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Xk, UXe)
          ((UXe.topIso.inv ≫ eX₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fXk).cochain (𝒱.comap j₀) 2)))
    (hωX : ∀ r : 𝒱.Idx 2,
      letI := algebraOfHom (qZ (r.1 0)) (OX (r.1 0) (𝒱.inter r))
      letI := algebraOfHom fXk UXe
      ∃ cs : Γ(Xk, UXe) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Z (r.1 0), OX (r.1 0) (𝒱.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (r.1 0), OX (r.1 0) (𝒱.inter r))
          ((hOXaff (r.1 0) (𝒱.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 r) (𝒱.inter_le r 0)).isoSpec.inv ≫
              (ρXac r).hom ≫ (OX (r.1 2) (𝒱.inter r)).ι)
          ((hOXaff (r.1 0) (𝒱.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 r) (𝒱.inter_le r 0)).isoSpec.inv ≫
              (ρXab r).hom ≫ (ρXbc r).hom ≫ (OX (r.1 2) (𝒱.inter r)).ι)
          fXk LX (j₀ ⁻¹ᵁ 𝒱.U (r.1 2)) ((j₀ ∣_ 𝒱.U (r.1 2)) ≫ gZ (r.1 2)) UXe cs ∧
        ∀ (a : Γ(Xk, UXe)) (ξ : Module.Dual (ResidueField T') V), σX r (cs a ξ) = ωX.1 a ξ r)
    (hωXZ : letI := algebraOfHom fXk UXe
      ∀ (a : Γ(Xk, UXe)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fXk).d (𝒱.comap j₀) 2 (ωX.1 a ξ) = 0)

    (h₀ : X₀ ⟶ A₀) (hh₀ : h₀ ≫ f₀ = fX₀)
    (lam : 𝒱.ι → 𝒰.ι) (hlam₀ : ∀ w, 𝒱.U w ≤ h₀ ⁻¹ᵁ 𝒰.U (lam w))
    (hk : Xk ⟶ Ak) (hhk : hk ≫ i₀ = j₀ ≫ h₀) (hhkf : hk ≫ fk = fXk)
    (hhom : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fXk),
      (LX.mul t P Q).1 ≫ hk =
        (Lk.mul t ⟨P.1 ≫ hk, by rw [Category.assoc, hhkf, P.2]⟩ ⟨Q.1 ≫ hk, by rw [Category.assoc, hhkf, Q.2]⟩).1)
    (hUX : UXe ≤ hk ⁻¹ᵁ Ue)
    (hlamk : ∀ w, (𝒱.comap j₀).U w ≤ hk ⁻¹ᵁ (𝒰.comap i₀).U (lam w))
    (hZ : ∀ w, Z w ⟶ Y (lam w)) (hhZq : ∀ w, hZ w ≫ q (lam w) = qZ w)
    (hhZg : ∀ w, gZ w ≫ hZ w = X₀.homOfLE (hlam₀ w) ≫ (h₀ ∣_ 𝒰.U (lam w)) ≫ g (lam w))

    (Φ : ∀ (a b : 𝒰.ι) (W : A₀.Opens), W ≤ 𝒰.U a → W ≤ 𝒰.U b → ((↑(O a W) : Scheme.{u}) ≅ ↑(O b W)))
    (hΦq : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (O b W).ι ≫ q b = (O a W).ι ≫ q a)
    (hΦg : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b)
      (γ : (↑W : Scheme.{u}) ⟶ ↑(O a W)) (γ' : (↑W : Scheme.{u}) ⟶ ↑(O b W)),
      γ ≫ (O a W).ι = A₀.homOfLE ha ≫ g a → γ' ≫ (O b W).ι = A₀.homOfLE hb ≫ g b → γ ≫ (Φ a b W ha hb).hom = γ')
    (hΦres : ∀ (a b : 𝒰.ι) (W W' : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (ha' : W' ≤ 𝒰.U a) (hb' : W' ≤ 𝒰.U b)
      (hWW : W' ≤ W),
      (Φ a b W' ha' hb').hom ≫ (Y b).homOfLE (hOm b hWW) = (Y a).homOfLE (hOm a hWW) ≫ (Φ a b W ha hb).hom)
    (hΦrefl : ∀ (a : 𝒰.ι) (W : A₀.Opens) (ha ha' : W ≤ 𝒰.U a), (Φ a a W ha ha').hom = 𝟙 _)
    (hΦsymm : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (Φ b a W hb ha).hom = 𝟙 _)
    (hΦφ : ∀ (a b : 𝒰.ι) (h : a < b), (Φ a b (𝒰.U a ⊓ 𝒰.U b) inf_le_left inf_le_right).hom = (φ a b h).hom)

    (ΦX : ∀ (x y : 𝒱.ι), x < y → ∀ (W : X₀.Opens), W ≤ 𝒱.U x ⊓ 𝒱.U y → ((↑(OX x W) : Scheme.{u}) ≅ ↑(OX y W)))
    (hΦX : ∀ (x y : 𝒱.ι) (h : x < y) (W : X₀.Opens) (hW : W ≤ 𝒱.U x ⊓ 𝒱.U y),
      (ΦX x y h W hW).hom ≫ (Z y).homOfLE (hOXm y hW) = (Z x).homOfLE (hOXm x hW) ≫ (φX x y h).hom)

    (ℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens), WX ≤ h₀ ⁻¹ᵁ WA → ((↑(OX x WX) : Scheme.{u}) ⟶ ↑(O (lam x) WA)))
    (hℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens) (h : WX ≤ h₀ ⁻¹ᵁ WA),
      ℓ x WX WA h ≫ (O (lam x) WA).ι = (OX x WX).ι ≫ hZ x)
    (s : 𝒱.Idx 2)
    (D : letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      letI := algebraOfHom fk Ue
      Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))))
    (hD : letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      letI := algebraOfHom fk Ue
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))
        ((hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).isoSpec.inv ≫ ℓ (s.1 0) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) (by rw [Scheme.OrderedAffineCover.preimage_iInf_fin]; exact le_iInf fun j => (𝒱.inter_le s j).trans (hlam₀ (s.1 j))) ≫ (Φ (lam (s.1 0)) (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j))) (iInf_le (fun j => 𝒰.U (lam (s.1 j))) 0) (iInf_le (fun j => 𝒰.U (lam (s.1 j))) 2)).hom ≫ (O (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι)
        ((hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).isoSpec.inv ≫ ℓ (s.1 0) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) (by rw [Scheme.OrderedAffineCover.preimage_iInf_fin]; exact le_iInf fun j => (𝒱.inter_le s j).trans (hlam₀ (s.1 j))) ≫ (Φ (lam (s.1 0)) (lam (s.1 1)) (⨅ j, 𝒰.U (lam (s.1 j))) (iInf_le (fun j => 𝒰.U (lam (s.1 j))) 0) (iInf_le (fun j => 𝒰.U (lam (s.1 j))) 1)).hom ≫ (Φ (lam (s.1 1)) (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j))) (iInf_le (fun j => 𝒰.U (lam (s.1 j))) 1) (iInf_le (fun j => 𝒰.U (lam (s.1 j))) 2)).hom ≫ (O (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι)
        fk Lk (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))) ((i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))) Ue D) :
    letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
    letI := algebraOfHom fk Ue
    ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
      σX s (D a ξ) = OModulePresheaf.unitPullback (πX := fXk) hk (𝒱.comap j₀) (𝒰.comap i₀) lam hlamk 2 (ω.1 a ξ) s := by
  classical
  letI instC : Algebra T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
  letI instA : Algebra (ResidueField T') Γ(Ak, Ue) := algebraOfHom fk Ue
  intro a ξ
  have hOs : IsAffineOpen (OX (s.1 0) (𝒱.inter s)) :=
    hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)
  haveI : Smooth (qZ (s.1 0)) := hqZ _
  haveI : Module.Flat T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) := flat_sections (qZ (s.1 0)) hOs
  have hW : ∀ j, (⨅ j, 𝒰.U (lam (s.1 j))) ≤ 𝒰.U (lam (s.1 j)) := fun j => iInf_le _ j
  have hVW : 𝒱.inter s ≤ h₀ ⁻¹ᵁ (⨅ j, 𝒰.U (lam (s.1 j))) := by
    rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
    exact le_iInf fun j => (𝒱.inter_le s j).trans (hlam₀ (s.1 j))
  have hιq : hOs.isoSpec.inv ≫ (OX (s.1 0) (𝒱.inter s)).ι ≫ qZ (s.1 0) =
      Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) := by
    rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι]; exact fromSpec_comp_eq (qZ (s.1 0)) hOs

  obtain ⟨ℓE, hℓEd⟩ : ∃ m : Spec (CommRingCat.of Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))) ⟶
      ↑(O (lam (s.1 0)) (⨅ j, 𝒰.U (lam (s.1 j)))),
      m = hOs.isoSpec.inv ≫ ℓ (s.1 0) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) hVW := ⟨_, rfl⟩
  have hℓET : ℓE ≫ (O (lam (s.1 0)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι ≫ q (lam (s.1 0)) =
      Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) := by
    rw [hℓEd, Category.assoc, ← Category.assoc (ℓ _ _ _ _), hℓ, Category.assoc, hhZq]
    exact hιq
  have hD' : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))
      (ℓE ≫ (Φ ((lam ∘ s.1) 0) ((lam ∘ s.1) 2) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 0) (hW 2)).hom ≫
        (O ((lam ∘ s.1) 2) (⨅ j, 𝒰.U (lam (s.1 j)))).ι)
      (ℓE ≫ (Φ ((lam ∘ s.1) 0) ((lam ∘ s.1) 1) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 0) (hW 1)).hom ≫
        (Φ ((lam ∘ s.1) 1) ((lam ∘ s.1) 2) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 1) (hW 2)).hom ≫
        (O ((lam ∘ s.1) 2) (⨅ j, 𝒰.U (lam (s.1 j)))).ι)
      fk Lk (i₀ ⁻¹ᵁ 𝒰.U ((lam ∘ s.1) 2)) ((i₀ ∣_ 𝒰.U ((lam ∘ s.1) 2)) ≫ g ((lam ∘ s.1) 2)) Ue D := by
    rw [hℓEd]; simpa only [Category.assoc, Function.comp] using hD
  obtain ⟨E1, E2⟩ := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_defect_eq_sign_smul_of_pin
    T' T π hsmall hI ρ hρ V ι hι hιI f₀ 𝒰 Y q hq g hg fk Lk i₀ hi₀ Ue hUe e₁ he₁ O hO hOm hOaff
    Φ hΦq hΦg hΦres hΦrefl hΦsymm (lam ∘ s.1) (⨅ j, 𝒰.U (lam (s.1 j))) hW
    Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) ℓE hℓET D hD'
  by_cases hinj : Function.Injective (lam ∘ s.1)
  swap
  ·
    rw [OModulePresheaf.unitPullback_apply_of_not_injective hk (𝒱.comap j₀) (𝒰.comap i₀) lam hlamk 2 (ω.1 a ξ) s hinj,
      E1 hinj a, LinearMap.zero_apply, map_zero]
    rfl

  rw [OModulePresheaf.unitPullback_apply_of_injective hk (𝒱.comap j₀) (𝒰.comap i₀) lam hlamk 2 (ω.1 a ξ) s hinj]
  set r : 𝒰.Idx 2 := (𝒱.comap j₀).sortIdx (𝒰.comap i₀) lam s hinj with hrd
  have hr : ∀ j, r.1 j = (lam ∘ s.1) ((Tuple.sort (lam ∘ s.1)) j) := fun j => rfl
  have hWr : (⨅ j, 𝒰.U (lam (s.1 j))) ≤ 𝒰.inter r :=
    le_iInf fun j => iInf_le (fun j => 𝒰.U (lam (s.1 j))) ((Tuple.sort (lam ∘ s.1)) j)
  have hWW : (𝒱.comap j₀).inter s ≤ hk ⁻¹ᵁ (𝒰.comap i₀).inter r :=
    (𝒱.comap j₀).inter_le_preimage_inter_sortIdx hk (𝒰.comap i₀) lam hlamk s hinj
  obtain ⟨cs, hcs, hp⟩ := hω r
  have hAr : IsAffineOpen (O (r.1 0) (𝒰.inter r)) :=
    hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)
  letI instR : Algebra T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))

  have hr02 : 𝒰.inter r ≤ 𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 2) := le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2)
  have hr01 : 𝒰.inter r ≤ 𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 1) := le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1)
  have hr12 : 𝒰.inter r ≤ 𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2) := le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2)
  have cac : (ρac r).hom = (Φ (r.1 0) (r.1 2) (𝒰.inter r) (𝒰.inter_le r 0) (𝒰.inter_le r 2)).hom := by
    rw [← cancel_mono ((Y (r.1 2)).homOfLE (hOm (r.1 2) hr02)), hρac r,
      hΦres (r.1 0) (r.1 2) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 2)) (𝒰.inter r) inf_le_left inf_le_right
        (𝒰.inter_le r 0) (𝒰.inter_le r 2) hr02,
      hΦφ (r.1 0) (r.1 2) (r.2 (by decide))]
  have cab : (ρab r).hom = (Φ (r.1 0) (r.1 1) (𝒰.inter r) (𝒰.inter_le r 0) (𝒰.inter_le r 1)).hom := by
    rw [← cancel_mono ((Y (r.1 1)).homOfLE (hOm (r.1 1) hr01)), hρab r,
      hΦres (r.1 0) (r.1 1) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 1)) (𝒰.inter r) inf_le_left inf_le_right
        (𝒰.inter_le r 0) (𝒰.inter_le r 1) hr01,
      hΦφ (r.1 0) (r.1 1) (r.2 (by decide))]
  have cbc : (ρbc r).hom = (Φ (r.1 1) (r.1 2) (𝒰.inter r) (𝒰.inter_le r 1) (𝒰.inter_le r 2)).hom := by
    rw [← cancel_mono ((Y (r.1 2)).homOfLE (hOm (r.1 2) hr12)), hρbc r,
      hΦres (r.1 1) (r.1 2) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2)) (𝒰.inter r) inf_le_left inf_le_right
        (𝒰.inter_le r 1) (𝒰.inter_le r 2) hr12,
      hΦφ (r.1 1) (r.1 2) (r.2 (by decide))]
  rw [cac, cab, cbc] at hcs

  obtain ⟨θ₀, hθ₀d⟩ : ∃ θ₀ : (↑(OX (s.1 0) (𝒱.inter s)) : Scheme.{u}) ⟶ ↑(O (r.1 0) (𝒰.inter r)),
      θ₀ = ℓ (s.1 0) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) hVW ≫
        (Φ (lam (s.1 0)) (r.1 0) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 0) (hWr.trans (𝒰.inter_le r 0))).hom ≫
        (Y (r.1 0)).homOfLE (hOm (r.1 0) hWr) := ⟨_, rfl⟩
  have hθ₀q : θ₀ ≫ (O (r.1 0) (𝒰.inter r)).ι ≫ q (r.1 0) = (OX (s.1 0) (𝒱.inter s)).ι ≫ qZ (s.1 0) := by
    rw [hθ₀d]
    simp only [Category.assoc]
    rw [Scheme.homOfLE_ι_assoc, hΦq, ← Category.assoc, hℓ, Category.assoc, hhZq]
  obtain ⟨h0r, hh0⟩ : ∃ h0r : CommRingCat.of Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) ⟶
      CommRingCat.of Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)), Spec.map h0r = hOs.isoSpec.inv ≫ θ₀ ≫ hAr.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hh0T : CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))) ≫ h0r =
      CommRingCat.ofHom (algebraMap T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hh0, ← fromSpec_comp_eq (q (r.1 0)) hAr, ← hιq, ← IsAffineOpen.isoSpec_inv_ι hAr]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hθ₀q]
  let θ : Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) →ₐ[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) :=
    { toRingHom := h0r.hom
      commutes' := fun t => congrArg (fun φ : CommRingCat.of T' ⟶ _ => φ.hom t) hh0T }
  have hθ : Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ hAr.isoSpec.inv =
      ℓE ≫ (Φ (lam (s.1 0)) (r.1 0) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 0) (hWr.trans (𝒰.inter_le r 0))).hom ≫
        (Y (r.1 0)).homOfLE (hOm (r.1 0) hWr) := by
    show Spec.map h0r ≫ _ = _
    rw [hh0, hℓEd, hθ₀d]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hval := E2 hinj r hr hWr cs hcs θ hθ a ξ
  rw [hval, map_zsmul]
  congr 1
  rw [← hp a ξ]

  refine AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_map_app_of_specMap_comp_fromSpec_eq
    (q (r.1 0)) (qZ (s.1 0)) fk fXk hk hhkf (O (r.1 0) (𝒰.inter r)) hAr (OX (s.1 0) (𝒱.inter s)) hOs
    ((𝒰.comap i₀).inter r) ((𝒱.comap j₀).inter s)
    (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) r)
    (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s)
    hWW
    (Ak.homOfLE (𝒰.comap_inter_le i₀ r) ≫ (i₀ ∣_ 𝒰.inter r) ≫ A₀.homOfLE (𝒰.inter_le r 0) ≫ g (r.1 0))
    θ (σ r) (σX s) (hσ₁ r) (hσ₂ r) (hσX₂ s) ?_ (cs a ξ)

  obtain ⟨γα, hγα⟩ := exists_gamma (𝒰.U (lam (s.1 0))) (g (lam (s.1 0))) (O (lam (s.1 0))) (hO (lam (s.1 0)))
    (⨅ j, 𝒰.U (lam (s.1 j))) (hW 0)
  obtain ⟨γr, hγr⟩ := exists_gamma (𝒰.U (r.1 0)) (g (r.1 0)) (O (r.1 0)) (hO (r.1 0))
    (⨅ j, 𝒰.U (lam (s.1 j))) (hWr.trans (𝒰.inter_le r 0))
  have hγΦ := hΦg (lam (s.1 0)) (r.1 0) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 0) (hWr.trans (𝒰.inter_le r 0)) γα γr hγα hγr

  have h1 : (𝒱.comap j₀).inter s ≤ j₀ ⁻¹ᵁ (h₀ ⁻¹ᵁ (⨅ j, 𝒰.U (lam (s.1 j)))) :=
    (𝒱.comap_inter_le j₀ s).trans (j₀.preimage_mono hVW)
  obtain ⟨κ, hκd⟩ : ∃ κ : (↑((𝒱.comap j₀).inter s) : Scheme.{u}) ⟶ ↑(⨅ j, 𝒰.U (lam (s.1 j))),
      κ = Xk.homOfLE h1 ≫ (j₀ ∣_ (h₀ ⁻¹ᵁ (⨅ j, 𝒰.U (lam (s.1 j))))) ≫ (h₀ ∣_ (⨅ j, 𝒰.U (lam (s.1 j)))) :=
    ⟨_, rfl⟩
  have hκι : κ ≫ (⨅ j, 𝒰.U (lam (s.1 j))).ι = ((𝒱.comap j₀).inter s).ι ≫ j₀ ≫ h₀ := by
    rw [hκd]; simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc]

  have hX := hσX₁ s
  have Claim0 : Xk.homOfLE (𝒱.comap_inter_le j₀ s) ≫ (j₀ ∣_ 𝒱.inter s) ≫ X₀.homOfLE (𝒱.inter_le s 0) ≫
      X₀.homOfLE (hlam₀ (s.1 0)) ≫ (h₀ ∣_ 𝒰.U (lam (s.1 0))) = κ ≫ A₀.homOfLE (hW 0) := by
    rw [← cancel_mono (𝒰.U (lam (s.1 0))).ι]
    simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, Scheme.homOfLE_ι,
      Scheme.homOfLE_ι_assoc]
    rw [hκι]
  have Claim1 : ((Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s).isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (σX s).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) →ₐ[T']
          (ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))).toRingHom)) ≫
      hOs.isoSpec.inv ≫ ℓ (s.1 0) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) hVW = κ ≫ γα := by
    rw [← cancel_mono (O (lam (s.1 0)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι]
    simp only [Category.assoc]
    rw [← IsAffineOpen.isoSpec_inv_ι hOs] at hX
    rw [hℓ, hγα, ← reassoc_of% Claim0, reassoc_of% hX, hhZg]
  have Claim2 : Xk.homOfLE hWW ≫
      (hk ∣_ (𝒰.comap i₀).inter r) ≫ Ak.homOfLE (𝒰.comap_inter_le i₀ r) ≫ (i₀ ∣_ 𝒰.inter r) ≫
      A₀.homOfLE (𝒰.inter_le r 0) = κ ≫ A₀.homOfLE (hWr.trans (𝒰.inter_le r 0)) := by
    rw [← cancel_mono (𝒰.U (r.1 0)).ι]
    simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, Scheme.homOfLE_ι,
      Scheme.homOfLE_ι_assoc]
    rw [hκι, hhk]

  rw [← IsAffineOpen.isoSpec_inv_ι hAr, ← Category.assoc (Spec.map (CommRingCat.ofHom θ.toRingHom)), hθ, hℓEd]
  simp only [Category.assoc]
  rw [Scheme.homOfLE_ι, reassoc_of% Claim1, reassoc_of% hγΦ, hγr, reassoc_of% Claim2]

theorem N2G.exists_hvw
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))

    (σ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      ((ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))) ≃+* Γ(Ak, (𝒰.comap i₀).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σ s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))).toRingHom) ≫
          (hOaff (s.1 0) (𝒰.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 s) (𝒰.inter_le s 0)).fromSpec =
        Ak.homOfLE (𝒰.comap_inter_le i₀ s) ≫ (i₀ ∣_ 𝒰.inter s) ≫ A₀.homOfLE (𝒰.inter_le s 0) ≫ g (s.1 0))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒰.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
      σ s (x ⊗ₜ[T'] (1 : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)))) = algebraMap (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter s) x)

    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)

    (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
    (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (hρab : ∀ r : 𝒰.Idx 2,
      (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
          (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρbc : ∀ r : 𝒰.Idx 2,
      (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
        (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
          (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρac : ∀ r : 𝒰.Idx 2,
      (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
          (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ω : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2)))
    (hω : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      letI := algebraOfHom fk Ue
      ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs ∧
        ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ r (cs a ξ) = ω.1 a ξ r)
    (hωZ : letI := algebraOfHom fk Ue
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fk).d (𝒰.comap i₀) 2 (ω.1 a ξ) = 0)
    {X₀ : Scheme.{u}} (fX₀ : X₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated fX₀] [Smooth fX₀]

    (𝒱 : X₀.OrderedAffineCover)
    (Z : 𝒱.ι → Scheme.{u}) (qZ : ∀ a, Z a ⟶ Spec (CommRingCat.of T')) (hqZ : ∀ a, Smooth (qZ a))
    (gZ : ∀ a, (↑(𝒱.U a) : Scheme.{u}) ⟶ Z a)
    (hgZ : ∀ a, IsPullback (gZ a) ((𝒱.U a).ι ≫ fX₀) (qZ a) (Spec.map (CommRingCat.ofHom π)))

    {Xk : Scheme.{u}} (fXk : Xk ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fXk]
    (LX : RelativeGroupLaw (ResidueField T') fXk)
    (j₀ : Xk ⟶ X₀) [IsAffineHom j₀] (hj₀ : IsPullback j₀ fXk fX₀ (Spec.map (CommRingCat.ofHom ρ)))
    (UXe : Xk.Opens) (hUXe : IsAffineOpen UXe)
    (eX₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (UXe : Scheme.{u})) (heX₁ : eX₁ ≫ UXe.ι = (LX.one (𝟙 _)).1)

    (OX : ∀ a, X₀.Opens → (Z a).Opens)
    (hOX : ∀ (a : 𝒱.ι) (W : X₀.Opens), gZ a ⁻¹ᵁ OX a W = (𝒱.U a).ι ⁻¹ᵁ W)
    (hOXm : ∀ a, Monotone (OX a))
    (hOXtop : ∀ a, OX a (𝒱.U a) = ⊤)
    (hOXinf : ∀ (a : 𝒱.ι) (W W' : X₀.Opens), OX a W ⊓ OX a W' ≤ OX a (W ⊓ W'))
    (hOXaff : ∀ (a : 𝒱.ι) (W : X₀.Opens), IsAffineOpen W → W ≤ 𝒱.U a → IsAffineOpen (OX a W))

    (σX : ∀ {n : ℕ} (s : 𝒱.Idx n),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      ((ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))) ≃+* Γ(Xk, (𝒱.comap j₀).inter s))
    (hσX₁ : ∀ {n : ℕ} (s : 𝒱.Idx n),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σX s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))).toRingHom) ≫
          (hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).fromSpec =
        Xk.homOfLE (𝒱.comap_inter_le j₀ s) ≫ (j₀ ∣_ 𝒱.inter s) ≫ X₀.homOfLE (𝒱.inter_le s 0) ≫ gZ (s.1 0))
    (hσX₂ : ∀ {n : ℕ} (s : 𝒱.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      letI := algebraOfHom fXk ((𝒱.comap j₀).inter s)
      σX s (x ⊗ₜ[T'] (1 : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) = algebraMap (ResidueField T') Γ(Xk, (𝒱.comap j₀).inter s) x)

    (φX : ∀ (a b : 𝒱.ι), a < b → ((↑(OX a (𝒱.U a ⊓ 𝒱.U b)) : Scheme.{u}) ≅ ↑(OX b (𝒱.U a ⊓ 𝒱.U b))))
    (hφXq : ∀ (a b : 𝒱.ι) (h : a < b),
      (φX a b h).hom ≫ (OX b (𝒱.U a ⊓ 𝒱.U b)).ι ≫ qZ b = (OX a (𝒱.U a ⊓ 𝒱.U b)).ι ≫ qZ a)
    (hφXg : ∀ (a b : 𝒱.ι) (h : a < b),
      ∃ (γ : (↑(𝒱.U a ⊓ 𝒱.U b) : Scheme.{u}) ⟶ ↑(OX a (𝒱.U a ⊓ 𝒱.U b)))
        (γ' : (↑(𝒱.U a ⊓ 𝒱.U b) : Scheme.{u}) ⟶ ↑(OX b (𝒱.U a ⊓ 𝒱.U b))),
        γ ≫ (OX a (𝒱.U a ⊓ 𝒱.U b)).ι = X₀.homOfLE inf_le_left ≫ gZ a ∧
        γ' ≫ (OX b (𝒱.U a ⊓ 𝒱.U b)).ι = X₀.homOfLE inf_le_right ≫ gZ b ∧
        γ ≫ (φX a b h).hom = γ')
    (hφXO : ∀ (a b : 𝒱.ι) (h : a < b) (W : X₀.Opens),
      (φX a b h).hom ⁻¹ᵁ ((OX b (𝒱.U a ⊓ 𝒱.U b)).ι ⁻¹ᵁ OX b W) = (OX a (𝒱.U a ⊓ 𝒱.U b)).ι ⁻¹ᵁ OX a W)

    (ρXab : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 0) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 1) (𝒱.inter r))))
    (ρXbc : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 1) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 2) (𝒱.inter r))))
    (ρXac : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 0) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 2) (𝒱.inter r))))
    (hρXab : ∀ r : 𝒱.Idx 2,
      (ρXab r).hom ≫ (Z (r.1 1)).homOfLE (hOXm (r.1 1) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 1))) =
        (Z (r.1 0)).homOfLE (hOXm (r.1 0) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 1))) ≫
          (φX (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρXbc : ∀ r : 𝒱.Idx 2,
      (ρXbc r).hom ≫ (Z (r.1 2)).homOfLE (hOXm (r.1 2) (le_inf (𝒱.inter_le r 1) (𝒱.inter_le r 2))) =
        (Z (r.1 1)).homOfLE (hOXm (r.1 1) (le_inf (𝒱.inter_le r 1) (𝒱.inter_le r 2))) ≫
          (φX (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρXac : ∀ r : 𝒱.Idx 2,
      (ρXac r).hom ≫ (Z (r.1 2)).homOfLE (hOXm (r.1 2) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 2))) =
        (Z (r.1 0)).homOfLE (hOXm (r.1 0) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 2))) ≫
          (φX (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ωX : letI := algebraOfHom fXk UXe
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Xk, UXe)
          ((UXe.topIso.inv ≫ eX₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fXk).cochain (𝒱.comap j₀) 2)))
    (hωX : ∀ r : 𝒱.Idx 2,
      letI := algebraOfHom (qZ (r.1 0)) (OX (r.1 0) (𝒱.inter r))
      letI := algebraOfHom fXk UXe
      ∃ cs : Γ(Xk, UXe) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Z (r.1 0), OX (r.1 0) (𝒱.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (r.1 0), OX (r.1 0) (𝒱.inter r))
          ((hOXaff (r.1 0) (𝒱.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 r) (𝒱.inter_le r 0)).isoSpec.inv ≫
              (ρXac r).hom ≫ (OX (r.1 2) (𝒱.inter r)).ι)
          ((hOXaff (r.1 0) (𝒱.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 r) (𝒱.inter_le r 0)).isoSpec.inv ≫
              (ρXab r).hom ≫ (ρXbc r).hom ≫ (OX (r.1 2) (𝒱.inter r)).ι)
          fXk LX (j₀ ⁻¹ᵁ 𝒱.U (r.1 2)) ((j₀ ∣_ 𝒱.U (r.1 2)) ≫ gZ (r.1 2)) UXe cs ∧
        ∀ (a : Γ(Xk, UXe)) (ξ : Module.Dual (ResidueField T') V), σX r (cs a ξ) = ωX.1 a ξ r)
    (hωXZ : letI := algebraOfHom fXk UXe
      ∀ (a : Γ(Xk, UXe)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fXk).d (𝒱.comap j₀) 2 (ωX.1 a ξ) = 0)

    (h₀ : X₀ ⟶ A₀) (hh₀ : h₀ ≫ f₀ = fX₀)
    (lam : 𝒱.ι → 𝒰.ι) (hlam₀ : ∀ w, 𝒱.U w ≤ h₀ ⁻¹ᵁ 𝒰.U (lam w))
    (hk : Xk ⟶ Ak) (hhk : hk ≫ i₀ = j₀ ≫ h₀) (hhkf : hk ≫ fk = fXk)
    (hhom : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fXk),
      (LX.mul t P Q).1 ≫ hk =
        (Lk.mul t ⟨P.1 ≫ hk, by rw [Category.assoc, hhkf, P.2]⟩ ⟨Q.1 ≫ hk, by rw [Category.assoc, hhkf, Q.2]⟩).1)
    (hUX : UXe ≤ hk ⁻¹ᵁ Ue)
    (hlamk : ∀ w, (𝒱.comap j₀).U w ≤ hk ⁻¹ᵁ (𝒰.comap i₀).U (lam w))
    (hZ : ∀ w, Z w ⟶ Y (lam w)) (hhZq : ∀ w, hZ w ≫ q (lam w) = qZ w)
    (hhZg : ∀ w, gZ w ≫ hZ w = X₀.homOfLE (hlam₀ w) ≫ (h₀ ∣_ 𝒰.U (lam w)) ≫ g (lam w))

    (Φ : ∀ (a b : 𝒰.ι) (W : A₀.Opens), W ≤ 𝒰.U a → W ≤ 𝒰.U b → ((↑(O a W) : Scheme.{u}) ≅ ↑(O b W)))
    (hΦq : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (O b W).ι ≫ q b = (O a W).ι ≫ q a)
    (hΦg : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b)
      (γ : (↑W : Scheme.{u}) ⟶ ↑(O a W)) (γ' : (↑W : Scheme.{u}) ⟶ ↑(O b W)),
      γ ≫ (O a W).ι = A₀.homOfLE ha ≫ g a → γ' ≫ (O b W).ι = A₀.homOfLE hb ≫ g b → γ ≫ (Φ a b W ha hb).hom = γ')
    (hΦres : ∀ (a b : 𝒰.ι) (W W' : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (ha' : W' ≤ 𝒰.U a) (hb' : W' ≤ 𝒰.U b)
      (hWW : W' ≤ W),
      (Φ a b W' ha' hb').hom ≫ (Y b).homOfLE (hOm b hWW) = (Y a).homOfLE (hOm a hWW) ≫ (Φ a b W ha hb).hom)
    (hΦrefl : ∀ (a : 𝒰.ι) (W : A₀.Opens) (ha ha' : W ≤ 𝒰.U a), (Φ a a W ha ha').hom = 𝟙 _)
    (hΦsymm : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (Φ b a W hb ha).hom = 𝟙 _)
    (hΦφ : ∀ (a b : 𝒰.ι) (h : a < b), (Φ a b (𝒰.U a ⊓ 𝒰.U b) inf_le_left inf_le_right).hom = (φ a b h).hom)

    (ΦX : ∀ (x y : 𝒱.ι), x < y → ∀ (W : X₀.Opens), W ≤ 𝒱.U x ⊓ 𝒱.U y → ((↑(OX x W) : Scheme.{u}) ≅ ↑(OX y W)))
    (hΦX : ∀ (x y : 𝒱.ι) (h : x < y) (W : X₀.Opens) (hW : W ≤ 𝒱.U x ⊓ 𝒱.U y),
      (ΦX x y h W hW).hom ≫ (Z y).homOfLE (hOXm y hW) = (Z x).homOfLE (hOXm x hW) ≫ (φX x y h).hom)

    (ℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens), WX ≤ h₀ ⁻¹ᵁ WA → ((↑(OX x WX) : Scheme.{u}) ⟶ ↑(O (lam x) WA)))
    (hℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens) (h : WX ≤ h₀ ⁻¹ᵁ WA),
      ℓ x WX WA h ≫ (O (lam x) WA).ι = (OX x WX).ι ≫ hZ x)
    (s : 𝒱.Idx 2) :
    letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
    letI := algebraOfHom (qZ (s.1 1)) (OX (s.1 1) (𝒱.inter (𝒱.face s 0)))
    ∃ hvw : Γ(Z (s.1 1), OX (s.1 1) (𝒱.inter (𝒱.face s 0))) →ₐ[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)),
      Spec.map (CommRingCat.ofHom hvw.toRingHom) ≫ (hOXaff ((𝒱.face s 0).1 0) (𝒱.inter (𝒱.face s 0)) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 (𝒱.face s 0))
          (𝒱.inter_le (𝒱.face s 0) 0)).isoSpec.inv =
        (hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).isoSpec.inv ≫ (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter s) (le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1))).hom ≫
          (Z (s.1 1)).homOfLE (hOXm (s.1 1) (𝒱.inter_le_inter_face s 0)) := by
  classical
  letI instC : Algebra T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
  letI instT : Algebra T' Γ(Z (s.1 1), OX (s.1 1) (𝒱.inter (𝒱.face s 0))) :=
    algebraOfHom (qZ (s.1 1)) (OX (s.1 1) (𝒱.inter (𝒱.face s 0)))
  have hOs : IsAffineOpen (OX (s.1 0) (𝒱.inter s)) :=
    hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)
  have hOt : IsAffineOpen (OX (s.1 1) (𝒱.inter (𝒱.face s 0))) :=
    hOXaff ((𝒱.face s 0).1 0) (𝒱.inter (𝒱.face s 0)) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 (𝒱.face s 0))
      (𝒱.inter_le (𝒱.face s 0) 0)
  have hs01 : 𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1) := le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1)
  obtain ⟨θ₀, hθ₀d⟩ : ∃ θ₀ : (↑(OX (s.1 0) (𝒱.inter s)) : Scheme.{u}) ⟶ ↑(OX (s.1 1) (𝒱.inter (𝒱.face s 0))),
      θ₀ = (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter s) hs01).hom ≫
        (Z (s.1 1)).homOfLE (hOXm (s.1 1) (𝒱.inter_le_inter_face s 0)) := ⟨_, rfl⟩
  have hθ₀q : θ₀ ≫ (OX (s.1 1) (𝒱.inter (𝒱.face s 0))).ι ≫ qZ (s.1 1) = (OX (s.1 0) (𝒱.inter s)).ι ≫ qZ (s.1 0) := by
    rw [hθ₀d, Category.assoc, Scheme.homOfLE_ι_assoc, ← Scheme.homOfLE_ι (Z (s.1 1)) (hOXm (s.1 1) hs01),
      Category.assoc, ← Category.assoc (ΦX _ _ _ _ _).hom, hΦX, Category.assoc, hφXq, Scheme.homOfLE_ι_assoc]
  have hιq : hOs.isoSpec.inv ≫ (OX (s.1 0) (𝒱.inter s)).ι ≫ qZ (s.1 0) =
      Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) := by
    rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι]; exact fromSpec_comp_eq (qZ (s.1 0)) hOs
  obtain ⟨h0r, hh0⟩ : ∃ h0r : CommRingCat.of Γ(Z (s.1 1), OX (s.1 1) (𝒱.inter (𝒱.face s 0))) ⟶
      CommRingCat.of Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)), Spec.map h0r = hOs.isoSpec.inv ≫ θ₀ ≫ hOt.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hh0T : CommRingCat.ofHom (algebraMap T' Γ(Z (s.1 1), OX (s.1 1) (𝒱.inter (𝒱.face s 0)))) ≫ h0r =
      CommRingCat.ofHom (algebraMap T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hh0, ← fromSpec_comp_eq (qZ (s.1 1)) hOt, ← hιq, ← IsAffineOpen.isoSpec_inv_ι hOt]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hθ₀q]
  refine ⟨{ toRingHom := h0r.hom, commutes' := fun t => congrArg (fun φ : CommRingCat.of T' ⟶ _ => φ.hom t) hh0T }, ?_⟩
  show Spec.map h0r ≫ hOt.isoSpec.inv = hOs.isoSpec.inv ≫ (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter s) hs01).hom ≫
    (Z (s.1 1)).homOfLE (hOXm (s.1 1) (𝒱.inter_le_inter_face s 0))
  rw [hh0, hθ₀d]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem N2G.svw
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))

    (σ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      ((ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))) ≃+* Γ(Ak, (𝒰.comap i₀).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σ s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))).toRingHom) ≫
          (hOaff (s.1 0) (𝒰.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 s) (𝒰.inter_le s 0)).fromSpec =
        Ak.homOfLE (𝒰.comap_inter_le i₀ s) ≫ (i₀ ∣_ 𝒰.inter s) ≫ A₀.homOfLE (𝒰.inter_le s 0) ≫ g (s.1 0))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒰.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
      σ s (x ⊗ₜ[T'] (1 : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)))) = algebraMap (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter s) x)

    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)

    (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
    (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (hρab : ∀ r : 𝒰.Idx 2,
      (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
          (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρbc : ∀ r : 𝒰.Idx 2,
      (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
        (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
          (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρac : ∀ r : 𝒰.Idx 2,
      (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
          (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ω : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2)))
    (hω : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      letI := algebraOfHom fk Ue
      ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs ∧
        ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ r (cs a ξ) = ω.1 a ξ r)
    (hωZ : letI := algebraOfHom fk Ue
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fk).d (𝒰.comap i₀) 2 (ω.1 a ξ) = 0)
    {X₀ : Scheme.{u}} (fX₀ : X₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated fX₀] [Smooth fX₀]

    (𝒱 : X₀.OrderedAffineCover)
    (Z : 𝒱.ι → Scheme.{u}) (qZ : ∀ a, Z a ⟶ Spec (CommRingCat.of T')) (hqZ : ∀ a, Smooth (qZ a))
    (gZ : ∀ a, (↑(𝒱.U a) : Scheme.{u}) ⟶ Z a)
    (hgZ : ∀ a, IsPullback (gZ a) ((𝒱.U a).ι ≫ fX₀) (qZ a) (Spec.map (CommRingCat.ofHom π)))

    {Xk : Scheme.{u}} (fXk : Xk ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fXk]
    (LX : RelativeGroupLaw (ResidueField T') fXk)
    (j₀ : Xk ⟶ X₀) [IsAffineHom j₀] (hj₀ : IsPullback j₀ fXk fX₀ (Spec.map (CommRingCat.ofHom ρ)))
    (UXe : Xk.Opens) (hUXe : IsAffineOpen UXe)
    (eX₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (UXe : Scheme.{u})) (heX₁ : eX₁ ≫ UXe.ι = (LX.one (𝟙 _)).1)

    (OX : ∀ a, X₀.Opens → (Z a).Opens)
    (hOX : ∀ (a : 𝒱.ι) (W : X₀.Opens), gZ a ⁻¹ᵁ OX a W = (𝒱.U a).ι ⁻¹ᵁ W)
    (hOXm : ∀ a, Monotone (OX a))
    (hOXtop : ∀ a, OX a (𝒱.U a) = ⊤)
    (hOXinf : ∀ (a : 𝒱.ι) (W W' : X₀.Opens), OX a W ⊓ OX a W' ≤ OX a (W ⊓ W'))
    (hOXaff : ∀ (a : 𝒱.ι) (W : X₀.Opens), IsAffineOpen W → W ≤ 𝒱.U a → IsAffineOpen (OX a W))

    (σX : ∀ {n : ℕ} (s : 𝒱.Idx n),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      ((ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))) ≃+* Γ(Xk, (𝒱.comap j₀).inter s))
    (hσX₁ : ∀ {n : ℕ} (s : 𝒱.Idx n),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σX s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))).toRingHom) ≫
          (hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).fromSpec =
        Xk.homOfLE (𝒱.comap_inter_le j₀ s) ≫ (j₀ ∣_ 𝒱.inter s) ≫ X₀.homOfLE (𝒱.inter_le s 0) ≫ gZ (s.1 0))
    (hσX₂ : ∀ {n : ℕ} (s : 𝒱.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      letI := algebraOfHom fXk ((𝒱.comap j₀).inter s)
      σX s (x ⊗ₜ[T'] (1 : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) = algebraMap (ResidueField T') Γ(Xk, (𝒱.comap j₀).inter s) x)

    (φX : ∀ (a b : 𝒱.ι), a < b → ((↑(OX a (𝒱.U a ⊓ 𝒱.U b)) : Scheme.{u}) ≅ ↑(OX b (𝒱.U a ⊓ 𝒱.U b))))
    (hφXq : ∀ (a b : 𝒱.ι) (h : a < b),
      (φX a b h).hom ≫ (OX b (𝒱.U a ⊓ 𝒱.U b)).ι ≫ qZ b = (OX a (𝒱.U a ⊓ 𝒱.U b)).ι ≫ qZ a)
    (hφXg : ∀ (a b : 𝒱.ι) (h : a < b),
      ∃ (γ : (↑(𝒱.U a ⊓ 𝒱.U b) : Scheme.{u}) ⟶ ↑(OX a (𝒱.U a ⊓ 𝒱.U b)))
        (γ' : (↑(𝒱.U a ⊓ 𝒱.U b) : Scheme.{u}) ⟶ ↑(OX b (𝒱.U a ⊓ 𝒱.U b))),
        γ ≫ (OX a (𝒱.U a ⊓ 𝒱.U b)).ι = X₀.homOfLE inf_le_left ≫ gZ a ∧
        γ' ≫ (OX b (𝒱.U a ⊓ 𝒱.U b)).ι = X₀.homOfLE inf_le_right ≫ gZ b ∧
        γ ≫ (φX a b h).hom = γ')
    (hφXO : ∀ (a b : 𝒱.ι) (h : a < b) (W : X₀.Opens),
      (φX a b h).hom ⁻¹ᵁ ((OX b (𝒱.U a ⊓ 𝒱.U b)).ι ⁻¹ᵁ OX b W) = (OX a (𝒱.U a ⊓ 𝒱.U b)).ι ⁻¹ᵁ OX a W)

    (ρXab : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 0) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 1) (𝒱.inter r))))
    (ρXbc : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 1) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 2) (𝒱.inter r))))
    (ρXac : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 0) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 2) (𝒱.inter r))))
    (hρXab : ∀ r : 𝒱.Idx 2,
      (ρXab r).hom ≫ (Z (r.1 1)).homOfLE (hOXm (r.1 1) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 1))) =
        (Z (r.1 0)).homOfLE (hOXm (r.1 0) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 1))) ≫
          (φX (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρXbc : ∀ r : 𝒱.Idx 2,
      (ρXbc r).hom ≫ (Z (r.1 2)).homOfLE (hOXm (r.1 2) (le_inf (𝒱.inter_le r 1) (𝒱.inter_le r 2))) =
        (Z (r.1 1)).homOfLE (hOXm (r.1 1) (le_inf (𝒱.inter_le r 1) (𝒱.inter_le r 2))) ≫
          (φX (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρXac : ∀ r : 𝒱.Idx 2,
      (ρXac r).hom ≫ (Z (r.1 2)).homOfLE (hOXm (r.1 2) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 2))) =
        (Z (r.1 0)).homOfLE (hOXm (r.1 0) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 2))) ≫
          (φX (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ωX : letI := algebraOfHom fXk UXe
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Xk, UXe)
          ((UXe.topIso.inv ≫ eX₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fXk).cochain (𝒱.comap j₀) 2)))
    (hωX : ∀ r : 𝒱.Idx 2,
      letI := algebraOfHom (qZ (r.1 0)) (OX (r.1 0) (𝒱.inter r))
      letI := algebraOfHom fXk UXe
      ∃ cs : Γ(Xk, UXe) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Z (r.1 0), OX (r.1 0) (𝒱.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (r.1 0), OX (r.1 0) (𝒱.inter r))
          ((hOXaff (r.1 0) (𝒱.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 r) (𝒱.inter_le r 0)).isoSpec.inv ≫
              (ρXac r).hom ≫ (OX (r.1 2) (𝒱.inter r)).ι)
          ((hOXaff (r.1 0) (𝒱.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 r) (𝒱.inter_le r 0)).isoSpec.inv ≫
              (ρXab r).hom ≫ (ρXbc r).hom ≫ (OX (r.1 2) (𝒱.inter r)).ι)
          fXk LX (j₀ ⁻¹ᵁ 𝒱.U (r.1 2)) ((j₀ ∣_ 𝒱.U (r.1 2)) ≫ gZ (r.1 2)) UXe cs ∧
        ∀ (a : Γ(Xk, UXe)) (ξ : Module.Dual (ResidueField T') V), σX r (cs a ξ) = ωX.1 a ξ r)
    (hωXZ : letI := algebraOfHom fXk UXe
      ∀ (a : Γ(Xk, UXe)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fXk).d (𝒱.comap j₀) 2 (ωX.1 a ξ) = 0)

    (h₀ : X₀ ⟶ A₀) (hh₀ : h₀ ≫ f₀ = fX₀)
    (lam : 𝒱.ι → 𝒰.ι) (hlam₀ : ∀ w, 𝒱.U w ≤ h₀ ⁻¹ᵁ 𝒰.U (lam w))
    (hk : Xk ⟶ Ak) (hhk : hk ≫ i₀ = j₀ ≫ h₀) (hhkf : hk ≫ fk = fXk)
    (hhom : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fXk),
      (LX.mul t P Q).1 ≫ hk =
        (Lk.mul t ⟨P.1 ≫ hk, by rw [Category.assoc, hhkf, P.2]⟩ ⟨Q.1 ≫ hk, by rw [Category.assoc, hhkf, Q.2]⟩).1)
    (hUX : UXe ≤ hk ⁻¹ᵁ Ue)
    (hlamk : ∀ w, (𝒱.comap j₀).U w ≤ hk ⁻¹ᵁ (𝒰.comap i₀).U (lam w))
    (hZ : ∀ w, Z w ⟶ Y (lam w)) (hhZq : ∀ w, hZ w ≫ q (lam w) = qZ w)
    (hhZg : ∀ w, gZ w ≫ hZ w = X₀.homOfLE (hlam₀ w) ≫ (h₀ ∣_ 𝒰.U (lam w)) ≫ g (lam w))

    (Φ : ∀ (a b : 𝒰.ι) (W : A₀.Opens), W ≤ 𝒰.U a → W ≤ 𝒰.U b → ((↑(O a W) : Scheme.{u}) ≅ ↑(O b W)))
    (hΦq : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (O b W).ι ≫ q b = (O a W).ι ≫ q a)
    (hΦg : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b)
      (γ : (↑W : Scheme.{u}) ⟶ ↑(O a W)) (γ' : (↑W : Scheme.{u}) ⟶ ↑(O b W)),
      γ ≫ (O a W).ι = A₀.homOfLE ha ≫ g a → γ' ≫ (O b W).ι = A₀.homOfLE hb ≫ g b → γ ≫ (Φ a b W ha hb).hom = γ')
    (hΦres : ∀ (a b : 𝒰.ι) (W W' : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (ha' : W' ≤ 𝒰.U a) (hb' : W' ≤ 𝒰.U b)
      (hWW : W' ≤ W),
      (Φ a b W' ha' hb').hom ≫ (Y b).homOfLE (hOm b hWW) = (Y a).homOfLE (hOm a hWW) ≫ (Φ a b W ha hb).hom)
    (hΦrefl : ∀ (a : 𝒰.ι) (W : A₀.Opens) (ha ha' : W ≤ 𝒰.U a), (Φ a a W ha ha').hom = 𝟙 _)
    (hΦsymm : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (Φ b a W hb ha).hom = 𝟙 _)
    (hΦφ : ∀ (a b : 𝒰.ι) (h : a < b), (Φ a b (𝒰.U a ⊓ 𝒰.U b) inf_le_left inf_le_right).hom = (φ a b h).hom)

    (ΦX : ∀ (x y : 𝒱.ι), x < y → ∀ (W : X₀.Opens), W ≤ 𝒱.U x ⊓ 𝒱.U y → ((↑(OX x W) : Scheme.{u}) ≅ ↑(OX y W)))
    (hΦX : ∀ (x y : 𝒱.ι) (h : x < y) (W : X₀.Opens) (hW : W ≤ 𝒱.U x ⊓ 𝒱.U y),
      (ΦX x y h W hW).hom ≫ (Z y).homOfLE (hOXm y hW) = (Z x).homOfLE (hOXm x hW) ≫ (φX x y h).hom)

    (ℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens), WX ≤ h₀ ⁻¹ᵁ WA → ((↑(OX x WX) : Scheme.{u}) ⟶ ↑(O (lam x) WA)))
    (hℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens) (h : WX ≤ h₀ ⁻¹ᵁ WA),
      ℓ x WX WA h ≫ (O (lam x) WA).ι = (OX x WX).ι ≫ hZ x)
    (s : 𝒱.Idx 2)
    (hvw : letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      letI := algebraOfHom (qZ (s.1 1)) (OX (s.1 1) (𝒱.inter (𝒱.face s 0)))
      Γ(Z (s.1 1), OX (s.1 1) (𝒱.inter (𝒱.face s 0))) →ₐ[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))
    (hhvw : letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      letI := algebraOfHom (qZ (s.1 1)) (OX (s.1 1) (𝒱.inter (𝒱.face s 0)))
      Spec.map (CommRingCat.ofHom hvw.toRingHom) ≫ (hOXaff ((𝒱.face s 0).1 0) (𝒱.inter (𝒱.face s 0)) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 (𝒱.face s 0))
          (𝒱.inter_le (𝒱.face s 0) 0)).isoSpec.inv =
        (hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).isoSpec.inv ≫ (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter s) (le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1))).hom ≫
          (Z (s.1 1)).homOfLE (hOXm (s.1 1) (𝒱.inter_le_inter_face s 0))) :
    letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
    letI := algebraOfHom (qZ (s.1 1)) (OX (s.1 1) (𝒱.inter (𝒱.face s 0)))
    ∀ z : (ResidueField T') ⊗[T'] Γ(Z (s.1 1), OX (s.1 1) (𝒱.inter (𝒱.face s 0))),
      σX s (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hvw z) =
        (Xk.presheaf.map (homOfLE ((𝒱.comap j₀).inter_le_inter_face s 0)).op).hom (σX (𝒱.face s 0) z) := by
  classical
  letI instC : Algebra T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
  letI instT : Algebra T' Γ(Z (s.1 1), OX (s.1 1) (𝒱.inter (𝒱.face s 0))) :=
    algebraOfHom (qZ (s.1 1)) (OX (s.1 1) (𝒱.inter (𝒱.face s 0)))
  have hOs : IsAffineOpen (OX (s.1 0) (𝒱.inter s)) :=
    hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)
  have hOt : IsAffineOpen (OX (s.1 1) (𝒱.inter (𝒱.face s 0))) :=
    hOXaff ((𝒱.face s 0).1 0) (𝒱.inter (𝒱.face s 0)) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 (𝒱.face s 0))
      (𝒱.inter_le (𝒱.face s 0) 0)
  have hs01 : 𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1) := le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1)
  have hX := hσX₁ s
  refine AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
    (qZ ((𝒱.face s 0).1 0)) (qZ (s.1 0)) fXk (OX ((𝒱.face s 0).1 0) (𝒱.inter (𝒱.face s 0))) hOt
    (OX (s.1 0) (𝒱.inter s)) hOs ((𝒱.comap j₀).inter (𝒱.face s 0)) ((𝒱.comap j₀).inter s)
    (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) (𝒱.face s 0))
    (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s)
    ((𝒱.comap j₀).inter_le_inter_face s 0)
    (Xk.homOfLE (𝒱.comap_inter_le j₀ (𝒱.face s 0)) ≫ (j₀ ∣_ 𝒱.inter (𝒱.face s 0)) ≫
      X₀.homOfLE (𝒱.inter_le (𝒱.face s 0) 0) ≫ gZ ((𝒱.face s 0).1 0))
    hvw (σX (𝒱.face s 0)) (σX s) (hσX₁ (𝒱.face s 0)) (hσX₂ (𝒱.face s 0)) (hσX₂ s) ?_

  show (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s).isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (σX s).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))).toRingHom) ≫
      Spec.map (CommRingCat.ofHom hvw.toRingHom) ≫ hOt.fromSpec =
    Xk.homOfLE ((𝒱.comap j₀).inter_le_inter_face s 0) ≫ Xk.homOfLE (𝒱.comap_inter_le j₀ (𝒱.face s 0)) ≫
      (j₀ ∣_ 𝒱.inter (𝒱.face s 0)) ≫ X₀.homOfLE (V := 𝒱.U (s.1 1)) (𝒱.inter_le (𝒱.face s 0) 0) ≫ gZ (s.1 1)
  obtain ⟨γ, γ', hγ, hγ', hγφ⟩ := hφXg (s.1 0) (s.1 1) (s.2 (by decide))

  have h1 : (𝒱.comap j₀).inter s ≤ j₀ ⁻¹ᵁ (𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1)) :=
    (𝒱.comap_inter_le j₀ s).trans (j₀.preimage_mono hs01)
  obtain ⟨κ, hκd⟩ : ∃ κ : (↑((𝒱.comap j₀).inter s) : Scheme.{u}) ⟶ ↑(𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1)),
      κ = Xk.homOfLE h1 ≫ (j₀ ∣_ (𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1))) := ⟨_, rfl⟩
  have hκι : κ ≫ (𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1)).ι = ((𝒱.comap j₀).inter s).ι ≫ j₀ := by
    rw [hκd]; simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  rw [← IsAffineOpen.isoSpec_inv_ι hOs] at hX
  have hhvw' : Spec.map (CommRingCat.ofHom hvw.toRingHom) ≫ hOt.isoSpec.inv =
      hOs.isoSpec.inv ≫ (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter s) hs01).hom ≫
        (Z (s.1 1)).homOfLE (hOXm (s.1 1) (𝒱.inter_le_inter_face s 0)) := hhvw
  rw [← IsAffineOpen.isoSpec_inv_ι hOt, ← Category.assoc (Spec.map (CommRingCat.ofHom hvw.toRingHom)), hhvw']
  simp only [Category.assoc]
  rw [Scheme.homOfLE_ι, ← Scheme.homOfLE_ι (Z (s.1 1)) (hOXm (s.1 1) hs01), ← Category.assoc (ΦX _ _ _ _ _).hom, hΦX,
    Category.assoc]

  have Claim1 : ((Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s).isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (σX s).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))).toRingHom)) ≫
      hOs.isoSpec.inv ≫ (Z (s.1 0)).homOfLE (hOXm (s.1 0) hs01) = κ ≫ γ := by
    have Claim0 : Xk.homOfLE (𝒱.comap_inter_le j₀ s) ≫ (j₀ ∣_ 𝒱.inter s) ≫ X₀.homOfLE (𝒱.inter_le s 0) =
        κ ≫ X₀.homOfLE inf_le_left := by
      rw [← cancel_mono (𝒱.U (s.1 0)).ι]
      simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, Scheme.homOfLE_ι,
        Scheme.homOfLE_ι_assoc]
      rw [hκι]
    rw [← cancel_mono (OX (s.1 0) (𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1))).ι]
    simp only [Category.assoc]
    rw [Scheme.homOfLE_ι, hX, hγ, reassoc_of% Claim0]
  have Claim2 : Xk.homOfLE ((𝒱.comap j₀).inter_le_inter_face s 0) ≫ Xk.homOfLE (𝒱.comap_inter_le j₀ (𝒱.face s 0)) ≫
      (j₀ ∣_ 𝒱.inter (𝒱.face s 0)) ≫ X₀.homOfLE (V := 𝒱.U (s.1 1)) (𝒱.inter_le (𝒱.face s 0) 0) =
      κ ≫ X₀.homOfLE (inf_le_right : 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1) ≤ 𝒱.U (s.1 1)) := by
    rw [← cancel_mono (𝒱.U (s.1 1)).ι]
    simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, Scheme.homOfLE_ι,
      Scheme.homOfLE_ι_assoc]
    rw [hκι]
  rw [reassoc_of% Claim1, reassoc_of% hγφ, hγ', reassoc_of% Claim2]

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))

    (σ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      ((ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))) ≃+* Γ(Ak, (𝒰.comap i₀).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σ s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))).toRingHom) ≫
          (hOaff (s.1 0) (𝒰.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 s) (𝒰.inter_le s 0)).fromSpec =
        Ak.homOfLE (𝒰.comap_inter_le i₀ s) ≫ (i₀ ∣_ 𝒰.inter s) ≫ A₀.homOfLE (𝒰.inter_le s 0) ≫ g (s.1 0))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒰.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
      σ s (x ⊗ₜ[T'] (1 : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)))) = algebraMap (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter s) x)

    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)

    (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
    (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (hρab : ∀ r : 𝒰.Idx 2,
      (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
          (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρbc : ∀ r : 𝒰.Idx 2,
      (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
        (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
          (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρac : ∀ r : 𝒰.Idx 2,
      (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
        (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
          (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ω : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2)))
    (hω : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      letI := algebraOfHom fk Ue
      ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs ∧
        ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ r (cs a ξ) = ω.1 a ξ r)
    (hωZ : letI := algebraOfHom fk Ue
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fk).d (𝒰.comap i₀) 2 (ω.1 a ξ) = 0)
    {X₀ : Scheme.{u}} (fX₀ : X₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated fX₀] [Smooth fX₀]

    (𝒱 : X₀.OrderedAffineCover)
    (Z : 𝒱.ι → Scheme.{u}) (qZ : ∀ a, Z a ⟶ Spec (CommRingCat.of T')) (hqZ : ∀ a, Smooth (qZ a))
    (gZ : ∀ a, (↑(𝒱.U a) : Scheme.{u}) ⟶ Z a)
    (hgZ : ∀ a, IsPullback (gZ a) ((𝒱.U a).ι ≫ fX₀) (qZ a) (Spec.map (CommRingCat.ofHom π)))

    {Xk : Scheme.{u}} (fXk : Xk ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fXk]
    (LX : RelativeGroupLaw (ResidueField T') fXk)
    (j₀ : Xk ⟶ X₀) [IsAffineHom j₀] (hj₀ : IsPullback j₀ fXk fX₀ (Spec.map (CommRingCat.ofHom ρ)))
    (UXe : Xk.Opens) (hUXe : IsAffineOpen UXe)
    (eX₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (UXe : Scheme.{u})) (heX₁ : eX₁ ≫ UXe.ι = (LX.one (𝟙 _)).1)

    (OX : ∀ a, X₀.Opens → (Z a).Opens)
    (hOX : ∀ (a : 𝒱.ι) (W : X₀.Opens), gZ a ⁻¹ᵁ OX a W = (𝒱.U a).ι ⁻¹ᵁ W)
    (hOXm : ∀ a, Monotone (OX a))
    (hOXtop : ∀ a, OX a (𝒱.U a) = ⊤)
    (hOXinf : ∀ (a : 𝒱.ι) (W W' : X₀.Opens), OX a W ⊓ OX a W' ≤ OX a (W ⊓ W'))
    (hOXaff : ∀ (a : 𝒱.ι) (W : X₀.Opens), IsAffineOpen W → W ≤ 𝒱.U a → IsAffineOpen (OX a W))

    (σX : ∀ {n : ℕ} (s : 𝒱.Idx n),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      ((ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))) ≃+* Γ(Xk, (𝒱.comap j₀).inter s))
    (hσX₁ : ∀ {n : ℕ} (s : 𝒱.Idx n),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σX s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s))).toRingHom) ≫
          (hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)).fromSpec =
        Xk.homOfLE (𝒱.comap_inter_le j₀ s) ≫ (j₀ ∣_ 𝒱.inter s) ≫ X₀.homOfLE (𝒱.inter_le s 0) ≫ gZ (s.1 0))
    (hσX₂ : ∀ {n : ℕ} (s : 𝒱.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
      letI := algebraOfHom fXk ((𝒱.comap j₀).inter s)
      σX s (x ⊗ₜ[T'] (1 : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) = algebraMap (ResidueField T') Γ(Xk, (𝒱.comap j₀).inter s) x)

    (φX : ∀ (a b : 𝒱.ι), a < b → ((↑(OX a (𝒱.U a ⊓ 𝒱.U b)) : Scheme.{u}) ≅ ↑(OX b (𝒱.U a ⊓ 𝒱.U b))))
    (hφXq : ∀ (a b : 𝒱.ι) (h : a < b),
      (φX a b h).hom ≫ (OX b (𝒱.U a ⊓ 𝒱.U b)).ι ≫ qZ b = (OX a (𝒱.U a ⊓ 𝒱.U b)).ι ≫ qZ a)
    (hφXg : ∀ (a b : 𝒱.ι) (h : a < b),
      ∃ (γ : (↑(𝒱.U a ⊓ 𝒱.U b) : Scheme.{u}) ⟶ ↑(OX a (𝒱.U a ⊓ 𝒱.U b)))
        (γ' : (↑(𝒱.U a ⊓ 𝒱.U b) : Scheme.{u}) ⟶ ↑(OX b (𝒱.U a ⊓ 𝒱.U b))),
        γ ≫ (OX a (𝒱.U a ⊓ 𝒱.U b)).ι = X₀.homOfLE inf_le_left ≫ gZ a ∧
        γ' ≫ (OX b (𝒱.U a ⊓ 𝒱.U b)).ι = X₀.homOfLE inf_le_right ≫ gZ b ∧
        γ ≫ (φX a b h).hom = γ')
    (hφXO : ∀ (a b : 𝒱.ι) (h : a < b) (W : X₀.Opens),
      (φX a b h).hom ⁻¹ᵁ ((OX b (𝒱.U a ⊓ 𝒱.U b)).ι ⁻¹ᵁ OX b W) = (OX a (𝒱.U a ⊓ 𝒱.U b)).ι ⁻¹ᵁ OX a W)

    (ρXab : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 0) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 1) (𝒱.inter r))))
    (ρXbc : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 1) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 2) (𝒱.inter r))))
    (ρXac : ∀ r : 𝒱.Idx 2, ((↑(OX (r.1 0) (𝒱.inter r)) : Scheme.{u}) ≅ ↑(OX (r.1 2) (𝒱.inter r))))
    (hρXab : ∀ r : 𝒱.Idx 2,
      (ρXab r).hom ≫ (Z (r.1 1)).homOfLE (hOXm (r.1 1) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 1))) =
        (Z (r.1 0)).homOfLE (hOXm (r.1 0) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 1))) ≫
          (φX (r.1 0) (r.1 1) (r.2 (by decide))).hom)
    (hρXbc : ∀ r : 𝒱.Idx 2,
      (ρXbc r).hom ≫ (Z (r.1 2)).homOfLE (hOXm (r.1 2) (le_inf (𝒱.inter_le r 1) (𝒱.inter_le r 2))) =
        (Z (r.1 1)).homOfLE (hOXm (r.1 1) (le_inf (𝒱.inter_le r 1) (𝒱.inter_le r 2))) ≫
          (φX (r.1 1) (r.1 2) (r.2 (by decide))).hom)
    (hρXac : ∀ r : 𝒱.Idx 2,
      (ρXac r).hom ≫ (Z (r.1 2)).homOfLE (hOXm (r.1 2) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 2))) =
        (Z (r.1 0)).homOfLE (hOXm (r.1 0) (le_inf (𝒱.inter_le r 0) (𝒱.inter_le r 2))) ≫
          (φX (r.1 0) (r.1 2) (r.2 (by decide))).hom)

    (ωX : letI := algebraOfHom fXk UXe
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Xk, UXe)
          ((UXe.topIso.inv ≫ eX₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fXk).cochain (𝒱.comap j₀) 2)))
    (hωX : ∀ r : 𝒱.Idx 2,
      letI := algebraOfHom (qZ (r.1 0)) (OX (r.1 0) (𝒱.inter r))
      letI := algebraOfHom fXk UXe
      ∃ cs : Γ(Xk, UXe) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Z (r.1 0), OX (r.1 0) (𝒱.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (r.1 0), OX (r.1 0) (𝒱.inter r))
          ((hOXaff (r.1 0) (𝒱.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 r) (𝒱.inter_le r 0)).isoSpec.inv ≫
              (ρXac r).hom ≫ (OX (r.1 2) (𝒱.inter r)).ι)
          ((hOXaff (r.1 0) (𝒱.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 r) (𝒱.inter_le r 0)).isoSpec.inv ≫
              (ρXab r).hom ≫ (ρXbc r).hom ≫ (OX (r.1 2) (𝒱.inter r)).ι)
          fXk LX (j₀ ⁻¹ᵁ 𝒱.U (r.1 2)) ((j₀ ∣_ 𝒱.U (r.1 2)) ≫ gZ (r.1 2)) UXe cs ∧
        ∀ (a : Γ(Xk, UXe)) (ξ : Module.Dual (ResidueField T') V), σX r (cs a ξ) = ωX.1 a ξ r)
    (hωXZ : letI := algebraOfHom fXk UXe
      ∀ (a : Γ(Xk, UXe)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fXk).d (𝒱.comap j₀) 2 (ωX.1 a ξ) = 0)

    (h₀ : X₀ ⟶ A₀) (hh₀ : h₀ ≫ f₀ = fX₀)
    (lam : 𝒱.ι → 𝒰.ι) (hlam₀ : ∀ w, 𝒱.U w ≤ h₀ ⁻¹ᵁ 𝒰.U (lam w))
    (hk : Xk ⟶ Ak) (hhk : hk ≫ i₀ = j₀ ≫ h₀) (hhkf : hk ≫ fk = fXk)
    (hhom : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t fXk),
      (LX.mul t P Q).1 ≫ hk =
        (Lk.mul t ⟨P.1 ≫ hk, by rw [Category.assoc, hhkf, P.2]⟩ ⟨Q.1 ≫ hk, by rw [Category.assoc, hhkf, Q.2]⟩).1)
    (hUX : UXe ≤ hk ⁻¹ᵁ Ue)
    (hlamk : ∀ w, (𝒱.comap j₀).U w ≤ hk ⁻¹ᵁ (𝒰.comap i₀).U (lam w))
    (hZ : ∀ w, Z w ⟶ Y (lam w)) (hhZq : ∀ w, hZ w ≫ q (lam w) = qZ w)
    (hhZg : ∀ w, gZ w ≫ hZ w = X₀.homOfLE (hlam₀ w) ≫ (h₀ ∣_ 𝒰.U (lam w)) ≫ g (lam w))

    (Φ : ∀ (a b : 𝒰.ι) (W : A₀.Opens), W ≤ 𝒰.U a → W ≤ 𝒰.U b → ((↑(O a W) : Scheme.{u}) ≅ ↑(O b W)))
    (hΦq : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (O b W).ι ≫ q b = (O a W).ι ≫ q a)
    (hΦg : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b)
      (γ : (↑W : Scheme.{u}) ⟶ ↑(O a W)) (γ' : (↑W : Scheme.{u}) ⟶ ↑(O b W)),
      γ ≫ (O a W).ι = A₀.homOfLE ha ≫ g a → γ' ≫ (O b W).ι = A₀.homOfLE hb ≫ g b → γ ≫ (Φ a b W ha hb).hom = γ')
    (hΦres : ∀ (a b : 𝒰.ι) (W W' : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (ha' : W' ≤ 𝒰.U a) (hb' : W' ≤ 𝒰.U b)
      (hWW : W' ≤ W),
      (Φ a b W' ha' hb').hom ≫ (Y b).homOfLE (hOm b hWW) = (Y a).homOfLE (hOm a hWW) ≫ (Φ a b W ha hb).hom)
    (hΦrefl : ∀ (a : 𝒰.ι) (W : A₀.Opens) (ha ha' : W ≤ 𝒰.U a), (Φ a a W ha ha').hom = 𝟙 _)
    (hΦsymm : ∀ (a b : 𝒰.ι) (W : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b),
      (Φ a b W ha hb).hom ≫ (Φ b a W hb ha).hom = 𝟙 _)
    (hΦφ : ∀ (a b : 𝒰.ι) (h : a < b), (Φ a b (𝒰.U a ⊓ 𝒰.U b) inf_le_left inf_le_right).hom = (φ a b h).hom)

    (ΦX : ∀ (x y : 𝒱.ι), x < y → ∀ (W : X₀.Opens), W ≤ 𝒱.U x ⊓ 𝒱.U y → ((↑(OX x W) : Scheme.{u}) ≅ ↑(OX y W)))
    (hΦX : ∀ (x y : 𝒱.ι) (h : x < y) (W : X₀.Opens) (hW : W ≤ 𝒱.U x ⊓ 𝒱.U y),
      (ΦX x y h W hW).hom ≫ (Z y).homOfLE (hOXm y hW) = (Z x).homOfLE (hOXm x hW) ≫ (φX x y h).hom)

    (ℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens), WX ≤ h₀ ⁻¹ᵁ WA → ((↑(OX x WX) : Scheme.{u}) ⟶ ↑(O (lam x) WA)))
    (hℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens) (h : WX ≤ h₀ ⁻¹ᵁ WA),
      ℓ x WX WA h ≫ (O (lam x) WA).ι = (OX x WX).ι ≫ hZ x)

    (B : Γ(Ak, Ue) → Module.Dual (ResidueField T') V → (OModulePresheaf.unit fXk).cochain (𝒱.comap j₀) 1)
    (hB :
      ∀ t : 𝒱.Idx 1,
        letI := algebraOfHom (qZ (t.1 0)) (OX (t.1 0) (𝒱.inter t))
        ∃ β : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Z (t.1 0), OX (t.1 0) (𝒱.inter t)))),
          IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (t.1 0), OX (t.1 0) (𝒱.inter t))
            ((hOXaff (t.1 0) (𝒱.inter t) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 t) (𝒱.inter_le t 0)).isoSpec.inv ≫
                (ΦX (t.1 0) (t.1 1) (t.2 (by decide)) (𝒱.inter t) (le_inf (𝒱.inter_le t 0) (𝒱.inter_le t 1))).hom ≫
                ℓ (t.1 1) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (by rw [Scheme.Hom.preimage_inf]; exact le_inf ((𝒱.inter_le t 0).trans (hlam₀ (t.1 0))) ((𝒱.inter_le t 1).trans (hlam₀ (t.1 1)))) ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι)
            ((hOXaff (t.1 0) (𝒱.inter t) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 t) (𝒱.inter_le t 0)).isoSpec.inv ≫
                ℓ (t.1 0) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (by rw [Scheme.Hom.preimage_inf]; exact le_inf ((𝒱.inter_le t 0).trans (hlam₀ (t.1 0))) ((𝒱.inter_le t 1).trans (hlam₀ (t.1 1)))) ≫
                (Φ (lam (t.1 0)) (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) inf_le_left inf_le_right).hom ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι)
            fk Lk (i₀ ⁻¹ᵁ 𝒰.U (lam (t.1 1))) ((i₀ ∣_ 𝒰.U (lam (t.1 1))) ≫ g (lam (t.1 1))) Ue β ∧
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σX t (β a ξ) = B a ξ t)
    :
    letI := algebraOfHom fk Ue
    letI := algebraOfHom fXk UXe
    ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V) (s : 𝒱.Idx 2),
      OModulePresheaf.unitPullback (πX := fXk) hk (𝒱.comap j₀) (𝒰.comap i₀) lam hlamk 2 (ω.1 a ξ) s -
          ωX.1 ((Xk.presheaf.map (homOfLE hUX).op).hom ((hk.app Ue).hom a)) ξ s =
        (OModulePresheaf.unit fXk).d (𝒱.comap j₀) 1 (B a ξ) s := by
  classical
  intro a ξ s
  letI instE : Algebra (ResidueField T') Γ(Ak, Ue) := algebraOfHom fk Ue
  letI instEX : Algebra (ResidueField T') Γ(Xk, UXe) := algebraOfHom fXk UXe

  letI instC : Algebra T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter s))
  have hOs : IsAffineOpen (OX (s.1 0) (𝒱.inter s)) :=
    hOXaff (s.1 0) (𝒱.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 s) (𝒱.inter_le s 0)
  haveI := hqZ (s.1 0)
  haveI : Module.Flat T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) := flat_sections (qZ (s.1 0)) hOs
  have hW : ∀ j, (⨅ j, 𝒰.U (lam (s.1 j))) ≤ 𝒰.U (lam (s.1 j)) := fun j => iInf_le _ j
  have hVW : 𝒱.inter s ≤ h₀ ⁻¹ᵁ (⨅ j, 𝒰.U (lam (s.1 j))) := by
    rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
    exact le_iInf fun j => (𝒱.inter_le s j).trans (hlam₀ (s.1 j))
  have hs01 : 𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1) := le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1)
  have hs02 : 𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 2) := le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 2)
  have hs12 : 𝒱.inter s ≤ 𝒱.U (s.1 1) ⊓ 𝒱.U (s.1 2) := le_inf (𝒱.inter_le s 1) (𝒱.inter_le s 2)
  let M1 := hOs.isoSpec.inv ≫ ℓ (s.1 0) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) hVW ≫
    (Φ (lam (s.1 0)) (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 0) (hW 2)).hom ≫ (O (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι
  let M2 := hOs.isoSpec.inv ≫ ℓ (s.1 0) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) hVW ≫
    (Φ (lam (s.1 0)) (lam (s.1 1)) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 0) (hW 1)).hom ≫
    (Φ (lam (s.1 1)) (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 1) (hW 2)).hom ≫ (O (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι
  let M3 := hOs.isoSpec.inv ≫ (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter s) hs01).hom ≫
    ℓ (s.1 1) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) hVW ≫
    (Φ (lam (s.1 1)) (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 1) (hW 2)).hom ≫ (O (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι
  let M4 := hOs.isoSpec.inv ≫ (ΦX (s.1 0) (s.1 2) (s.2 (by decide)) (𝒱.inter s) hs02).hom ≫
    ℓ (s.1 2) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) hVW ≫ (O (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι
  let M5 := hOs.isoSpec.inv ≫ (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter s) hs01).hom ≫
    (ΦX (s.1 1) (s.1 2) (s.2 (by decide)) (𝒱.inter s) hs12).hom ≫
    ℓ (s.1 2) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) hVW ≫ (O (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι

  obtain ⟨csX, hcsX, hpX⟩ := hωX s

  have X45 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) M4 M5 fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))) ((i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))) Ue
      (fun a => csX ((Xk.presheaf.map (homOfLE hUX).op).hom ((hk.app Ue).hom a))) :=
    N2G.xread T' T π hπ hker hsmall hI ρ hρ V ι hι hιI f₀ 𝒰 Y q hq g hg fk Lk i₀ hi₀ Ue hUe e₁ he₁ O hO hOm hOtop hOinf hOaff σ hσ₁ hσ₂ φ hφq hφg hφO ρab ρbc ρac hρab hρbc hρac ω hω hωZ fX₀ 𝒱 Z qZ hqZ gZ hgZ fXk LX j₀ hj₀ UXe hUXe eX₁ heX₁ OX hOX hOXm hOXtop hOXinf hOXaff σX hσX₁ hσX₂ φX hφXq hφXg hφXO ρXab ρXbc ρXac hρXab hρXbc hρXac ωX hωX hωXZ h₀ hh₀ lam hlam₀ hk hhk hhkf hhom hUX hlamk hZ hhZq hhZg Φ hΦq hΦg hΦres hΦrefl hΦsymm hΦφ ΦX hΦX ℓ hℓ s csX hcsX

  obtain ⟨βuv, hβuv, hBuv⟩ := hB (𝒱.face s 2)
  obtain ⟨βvw, hβvw, hBvw⟩ := hB (𝒱.face s 0)
  obtain ⟨βuw, hβuw, hBuw⟩ := hB (𝒱.face s 1)
  letI instCuv : Algebra T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter (𝒱.face s 2))) := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter (𝒱.face s 2)))
  letI instCuw : Algebra T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter (𝒱.face s 1))) := algebraOfHom (qZ (s.1 0)) (OX (s.1 0) (𝒱.inter (𝒱.face s 1)))
  letI instCvw : Algebra T' Γ(Z (s.1 1), OX (s.1 1) (𝒱.inter (𝒱.face s 0))) := algebraOfHom (qZ (s.1 1)) (OX (s.1 1) (𝒱.inter (𝒱.face s 0)))
  let resuv : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter (𝒱.face s 2))) →ₐ[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) :=
    restrictAlgHom (qZ (s.1 0)) (hOXm (s.1 0) (𝒱.inter_le_inter_face s 2))
  let resuw : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter (𝒱.face s 1))) →ₐ[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) :=
    restrictAlgHom (qZ (s.1 0)) (hOXm (s.1 0) (𝒱.inter_le_inter_face s 1))

  obtain ⟨hvw, hhvw⟩ : ∃ hvw : Γ(Z (s.1 1), OX (s.1 1) (𝒱.inter (𝒱.face s 0))) →ₐ[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)),
      Spec.map (CommRingCat.ofHom hvw.toRingHom) ≫
        (hOXaff ((𝒱.face s 0).1 0) (𝒱.inter (𝒱.face s 0)) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 (𝒱.face s 0))
          (𝒱.inter_le (𝒱.face s 0) 0)).isoSpec.inv =
        hOs.isoSpec.inv ≫ (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter s) hs01).hom ≫
          (Z (s.1 1)).homOfLE (hOXm (s.1 1) (𝒱.inter_le_inter_face s 0)) :=
    N2G.exists_hvw T' T π hπ hker hsmall hI ρ hρ V ι hι hιI f₀ 𝒰 Y q hq g hg fk Lk i₀ hi₀ Ue hUe e₁ he₁ O hO hOm hOtop hOinf hOaff σ hσ₁ hσ₂ φ hφq hφg hφO ρab ρbc ρac hρab hρbc hρac ω hω hωZ fX₀ 𝒱 Z qZ hqZ gZ hgZ fXk LX j₀ hj₀ UXe hUXe eX₁ heX₁ OX hOX hOXm hOXtop hOXinf hOXaff σX hσX₁ hσX₂ φX hφXq hφXg hφXO ρXab ρXbc ρXac hρXab hρXbc hρXac ωX hωX hωXZ h₀ hh₀ lam hlam₀ hk hhk hhkf hhom hUX hlamk hZ hhZq hhZg Φ hΦq hΦg hΦres hΦrefl hΦsymm hΦφ ΦX hΦX ℓ hℓ s

  have Fuv : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) M3 M2 fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))) ((i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))) Ue
      (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resuv).toLinearMap ∘ₗ βuv x) := by
    have L2 : ∀ (x y : 𝒱.ι) (h : x < y) (W : X₀.Opens) (hW' : W ≤ 𝒱.U x ⊓ 𝒱.U y),
        (ΦX x y h W hW').hom ≫ (OX y W).ι = (Z x).homOfLE (hOXm x hW') ≫ (φX x y h).hom ≫ (OX y (𝒱.U x ⊓ 𝒱.U y)).ι := by
      intro x y h W hW'
      rw [← Scheme.homOfLE_ι (Z y) (hOXm y hW'), ← Category.assoc, hΦX, Category.assoc]
    have L3 : ∀ (a b : 𝒰.ι) (W W' : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (ha' : W' ≤ 𝒰.U a) (hb' : W' ≤ 𝒰.U b)
        (hWW : W' ≤ W), (Φ a b W' ha' hb').hom ≫ (O b W').ι = (Y a).homOfLE (hOm a hWW) ≫ (Φ a b W ha hb).hom ≫ (O b W).ι := by
      intro a b W W' ha hb ha' hb' hWW
      rw [← Scheme.homOfLE_ι (Y b) (hOm b hWW), ← Category.assoc, hΦres a b W W' ha hb ha' hb' hWW, Category.assoc]
    have Lℓ : ∀ (x : 𝒱.ι) (WX WX' : X₀.Opens) (WA WA' : A₀.Opens) (h : WX ≤ h₀ ⁻¹ᵁ WA) (h' : WX' ≤ h₀ ⁻¹ᵁ WA')
        (hX : WX' ≤ WX) (hA : WA' ≤ WA),
        ℓ x WX' WA' h' ≫ (Y (lam x)).homOfLE (hOm (lam x) hA) = (Z x).homOfLE (hOXm x hX) ≫ ℓ x WX WA h := by
      intro x WX WX' WA WA' h h' hX hA
      rw [← cancel_mono (O (lam x) WA).ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, hℓ, hℓ, Scheme.homOfLE_ι_assoc]
    have resnat : ∀ {W W' : A₀.Opens} (h : W ≤ W'),
        Ak.homOfLE (i₀.preimage_mono h) ≫ (i₀ ∣_ W') = (i₀ ∣_ W) ≫ A₀.homOfLE h := by
      intro W W' h
      rw [← cancel_mono W'.ι]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]

    have ht01 : 𝒱.inter (𝒱.face s 2) ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1) := le_inf (𝒱.inter_le (𝒱.face s 2) 0) (𝒱.inter_le (𝒱.face s 2) 1)
    have hℓt : 𝒱.inter (𝒱.face s 2) ≤ h₀ ⁻¹ᵁ (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1))) := by
      rw [Scheme.Hom.preimage_inf]
      exact le_inf ((𝒱.inter_le (𝒱.face s 2) 0).trans (hlam₀ _)) ((𝒱.inter_le (𝒱.face s 2) 1).trans (hlam₀ _))
    have hOt : IsAffineOpen (OX (s.1 0) (𝒱.inter (𝒱.face s 2))) :=
      hOXaff (s.1 0) (𝒱.inter (𝒱.face s 2)) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 (𝒱.face s 2)) (𝒱.inter_le (𝒱.face s 2) 0)
    have hβ' : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter (𝒱.face s 2)))
        (hOt.isoSpec.inv ≫ (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter (𝒱.face s 2)) ht01).hom ≫
          ℓ (s.1 1) (𝒱.inter (𝒱.face s 2)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1))) hℓt ≫
          (O (lam (s.1 1)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1)))).ι)
        (hOt.isoSpec.inv ≫ ℓ (s.1 0) (𝒱.inter (𝒱.face s 2)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1))) hℓt ≫
          (Φ (lam (s.1 0)) (lam (s.1 1)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1))) inf_le_left inf_le_right).hom ≫
          (O (lam (s.1 1)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1)))).ι)
        fk Lk (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 1))) ((i₀ ∣_ 𝒰.U (lam (s.1 1))) ≫ g (lam (s.1 1))) Ue βuv := hβuv

    have hR := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat (RingHom.ker π) hI hsmall V ι hι hιI
      ((Z (s.1 0)).presheaf.obj (Opposite.op (OX (s.1 0) (𝒱.inter (𝒱.face s 2)))))
      ((Z (s.1 0)).presheaf.obj (Opposite.op (OX (s.1 0) (𝒱.inter s)))) resuv _ _ fk Lk _ _ Ue _ hβ'
    have hsp : Spec.map (CommRingCat.ofHom resuv.toRingHom) ≫ hOt.isoSpec.inv =
        hOs.isoSpec.inv ≫ (Z (s.1 0)).homOfLE (hOXm (s.1 0) (𝒱.inter_le_inter_face s 2)) :=
      spec_map_comp_isoSpec_inv _ hOs _
    have hUαβ : (⨅ j, 𝒰.U (lam (s.1 j))) ≤ 𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1)) := le_inf (hW 0) (hW 1)
    have e1 : Spec.map (CommRingCat.ofHom resuv.toRingHom) ≫
        (hOt.isoSpec.inv ≫ (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter (𝒱.face s 2)) ht01).hom ≫
          ℓ (s.1 1) (𝒱.inter (𝒱.face s 2)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1))) hℓt ≫
          (O (lam (s.1 1)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1)))).ι) =
        (hOs.isoSpec.inv ≫ (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter s) hs01).hom ≫
          ℓ (s.1 1) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) hVW) ≫ (O (lam (s.1 1)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι := by
      rw [← Category.assoc, hsp]
      simp only [Category.assoc, hℓ]
      rw [reassoc_of% (L2 (s.1 0) (s.1 1) _ _ _), reassoc_of% (L2 (s.1 0) (s.1 1) _ _ _), Scheme.homOfLE_homOfLE_assoc]
    have e2 : Spec.map (CommRingCat.ofHom resuv.toRingHom) ≫
        (hOt.isoSpec.inv ≫ ℓ (s.1 0) (𝒱.inter (𝒱.face s 2)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1))) hℓt ≫
          (Φ (lam (s.1 0)) (lam (s.1 1)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1))) inf_le_left inf_le_right).hom ≫
          (O (lam (s.1 1)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1)))).ι) =
        (hOs.isoSpec.inv ≫ ℓ (s.1 0) (𝒱.inter s) (⨅ j, 𝒰.U (lam (s.1 j))) hVW ≫
          (Φ (lam (s.1 0)) (lam (s.1 1)) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 0) (hW 1)).hom) ≫ (O (lam (s.1 1)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι := by
      rw [← Category.assoc, hsp]
      simp only [Category.assoc]
      rw [L3 (lam (s.1 0)) (lam (s.1 1)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 1))) (⨅ j, 𝒰.U (lam (s.1 j))) inf_le_left inf_le_right
        (hW 0) (hW 1) hUαβ, reassoc_of% (Lℓ (s.1 0) _ _ _ _ hℓt hVW (𝒱.inter_le_inter_face s 2) hUαβ)]
    rw [e1, e2] at hR

    obtain ⟨aW₀, haW₀, hsq⟩ := AlgebraicGeometry.exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift
      (𝒰.U (lam (s.1 1))) (g (lam (s.1 1))) (O (lam (s.1 1))) (hO (lam (s.1 1))) i₀ (⨅ j, 𝒰.U (lam (s.1 j))) (hW 1)
    have V2 := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_of_isPullback_of_comp_mono (RingHom.ker π) hI hsmall
      V ι ((Z (s.1 0)).presheaf.obj (Opposite.op (OX (s.1 0) (𝒱.inter s)))) (O (lam (s.1 1)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι _ _ fk Lk
      _ _ (i₀.preimage_mono (hW 1)) _ aW₀ hsq Ue _ hR

    have hlift : ∀ (a : 𝒰.ι) (ha : (⨅ j, 𝒰.U (lam (s.1 j))) ≤ 𝒰.U a), ∃ γ : (↑(⨅ j, 𝒰.U (lam (s.1 j))) : Scheme.{u}) ⟶ ↑(O a (⨅ j, 𝒰.U (lam (s.1 j)))),
        γ ≫ (O a (⨅ j, 𝒰.U (lam (s.1 j)))).ι = A₀.homOfLE ha ≫ g a := by
      intro a ha
      have hrange : Set.range (A₀.homOfLE ha ≫ g a).base ⊆ Set.range (O a (⨅ j, 𝒰.U (lam (s.1 j)))).ι.base := by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨x, rfl⟩
        show (A₀.homOfLE ha ≫ g a).base x ∈ O a (⨅ j, 𝒰.U (lam (s.1 j)))
        rw [Scheme.Hom.comp_apply]
        have hx : (A₀.homOfLE ha).base x ∈ g a ⁻¹ᵁ O a (⨅ j, 𝒰.U (lam (s.1 j))) := by
          rw [hO]
          show ((𝒰.U a).ι.base ((A₀.homOfLE ha).base x)) ∈ (⨅ j, 𝒰.U (lam (s.1 j)))
          rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
          exact x.2
        exact hx
      exact ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
    obtain ⟨γ, hγ⟩ := hlift (lam (s.1 1)) (hW 1)
    obtain ⟨γ', hγ'⟩ := hlift (lam (s.1 2)) (hW 2)
    have hcarry := hΦg (lam (s.1 1)) (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 1) (hW 2) γ γ' hγ hγ'
    have clA : aW₀ = (i₀ ∣_ (⨅ j, 𝒰.U (lam (s.1 j)))) ≫ γ := by
      rw [← cancel_mono (O (lam (s.1 1)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι, Category.assoc, hγ, haW₀, reassoc_of% (resnat (hW 1))]
    have haWc : Ak.homOfLE (i₀.preimage_mono (hW 2)) ≫ ((i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))) =
        aW₀ ≫ ((Φ (lam (s.1 1)) (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 1) (hW 2)).hom ≫ (O (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι) := by
      rw [clA, Category.assoc, reassoc_of% hcarry, hγ', reassoc_of% (resnat (hW 2))]
    have V3 := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq (RingHom.ker π) V ι
      ((Z (s.1 0)).presheaf.obj (Opposite.op (OX (s.1 0) (𝒱.inter s))))
      ((Φ (lam (s.1 1)) (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j))) (hW 1) (hW 2)).hom ≫ (O (lam (s.1 2)) (⨅ j, 𝒰.U (lam (s.1 j)))).ι) _ _ fk Lk
      _ _ (i₀.preimage_mono (hW 2)) aW₀ _ haWc Ue _ V2
    simp only [M3, M2]
    simpa only [Category.assoc] using V3
  have Fvw : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) M5 M3 fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))) ((i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))) Ue
      (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hvw).toLinearMap ∘ₗ βvw x) := by
    have L2 : ∀ (x y : 𝒱.ι) (h : x < y) (W : X₀.Opens) (hW' : W ≤ 𝒱.U x ⊓ 𝒱.U y),
        (ΦX x y h W hW').hom ≫ (OX y W).ι = (Z x).homOfLE (hOXm x hW') ≫ (φX x y h).hom ≫ (OX y (𝒱.U x ⊓ 𝒱.U y)).ι := by
      intro x y h W hW'
      rw [← Scheme.homOfLE_ι (Z y) (hOXm y hW'), ← Category.assoc, hΦX, Category.assoc]
    have L3 : ∀ (a b : 𝒰.ι) (W W' : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (ha' : W' ≤ 𝒰.U a) (hb' : W' ≤ 𝒰.U b)
        (hWW : W' ≤ W), (Φ a b W' ha' hb').hom ≫ (O b W').ι = (Y a).homOfLE (hOm a hWW) ≫ (Φ a b W ha hb).hom ≫ (O b W).ι := by
      intro a b W W' ha hb ha' hb' hWW
      rw [← Scheme.homOfLE_ι (Y b) (hOm b hWW), ← Category.assoc, hΦres a b W W' ha hb ha' hb' hWW, Category.assoc]
    have Lℓ : ∀ (x : 𝒱.ι) (WX WX' : X₀.Opens) (WA WA' : A₀.Opens) (h : WX ≤ h₀ ⁻¹ᵁ WA) (h' : WX' ≤ h₀ ⁻¹ᵁ WA')
        (hX : WX' ≤ WX) (hA : WA' ≤ WA),
        ℓ x WX' WA' h' ≫ (Y (lam x)).homOfLE (hOm (lam x) hA) = (Z x).homOfLE (hOXm x hX) ≫ ℓ x WX WA h := by
      intro x WX WX' WA WA' h h' hX hA
      rw [← cancel_mono (O (lam x) WA).ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, hℓ, hℓ, Scheme.homOfLE_ι_assoc]

    have ht12 : 𝒱.inter (𝒱.face s 0) ≤ 𝒱.U (s.1 1) ⊓ 𝒱.U (s.1 2) := le_inf (𝒱.inter_le (𝒱.face s 0) 0) (𝒱.inter_le (𝒱.face s 0) 1)
    have hℓt : 𝒱.inter (𝒱.face s 0) ≤ h₀ ⁻¹ᵁ (𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2))) := by
      rw [Scheme.Hom.preimage_inf]
      exact le_inf ((𝒱.inter_le (𝒱.face s 0) 0).trans (hlam₀ _)) ((𝒱.inter_le (𝒱.face s 0) 1).trans (hlam₀ _))
    have hOt : IsAffineOpen (OX (s.1 1) (𝒱.inter (𝒱.face s 0))) :=
      hOXaff (s.1 1) (𝒱.inter (𝒱.face s 0)) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 (𝒱.face s 0)) (𝒱.inter_le (𝒱.face s 0) 0)
    have hβ' : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (s.1 1), OX (s.1 1) (𝒱.inter (𝒱.face s 0)))
        (hOt.isoSpec.inv ≫ (ΦX (s.1 1) (s.1 2) (s.2 (by decide)) (𝒱.inter (𝒱.face s 0)) ht12).hom ≫
          ℓ (s.1 2) (𝒱.inter (𝒱.face s 0)) (𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2))) hℓt ≫
          (O (lam (s.1 2)) (𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2)))).ι)
        (hOt.isoSpec.inv ≫ ℓ (s.1 1) (𝒱.inter (𝒱.face s 0)) (𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2))) hℓt ≫
          (Φ (lam (s.1 1)) (lam (s.1 2)) (𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2))) inf_le_left inf_le_right).hom ≫
          (O (lam (s.1 2)) (𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2)))).ι)
        fk Lk (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))) ((i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))) Ue βvw := hβvw
    have hR := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat (RingHom.ker π) hI hsmall V ι hι hιI
      ((Z (s.1 1)).presheaf.obj (Opposite.op (OX (s.1 1) (𝒱.inter (𝒱.face s 0)))))
      ((Z (s.1 0)).presheaf.obj (Opposite.op (OX (s.1 0) (𝒱.inter s)))) hvw _ _ fk Lk _ _ Ue _ hβ'
    have hsp : Spec.map (CommRingCat.ofHom hvw.toRingHom) ≫ hOt.isoSpec.inv =
        hOs.isoSpec.inv ≫ (ΦX (s.1 0) (s.1 1) (s.2 (by decide)) (𝒱.inter s) hs01).hom ≫
          (Z (s.1 1)).homOfLE (hOXm (s.1 1) (𝒱.inter_le_inter_face s 0)) := hhvw
    have hUβγ : (⨅ j, 𝒰.U (lam (s.1 j))) ≤ 𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2)) := le_inf (hW 1) (hW 2)
    have e1 : Spec.map (CommRingCat.ofHom hvw.toRingHom) ≫
        (hOt.isoSpec.inv ≫ (ΦX (s.1 1) (s.1 2) (s.2 (by decide)) (𝒱.inter (𝒱.face s 0)) ht12).hom ≫
          ℓ (s.1 2) (𝒱.inter (𝒱.face s 0)) (𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2))) hℓt ≫
          (O (lam (s.1 2)) (𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2)))).ι) = M5 := by
      rw [← Category.assoc, hsp]
      simp only [M5, Category.assoc, hℓ]
      rw [reassoc_of% (L2 (s.1 1) (s.1 2) _ _ _), reassoc_of% (L2 (s.1 1) (s.1 2) _ _ _), Scheme.homOfLE_homOfLE_assoc]
    have e2 : Spec.map (CommRingCat.ofHom hvw.toRingHom) ≫
        (hOt.isoSpec.inv ≫ ℓ (s.1 1) (𝒱.inter (𝒱.face s 0)) (𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2))) hℓt ≫
          (Φ (lam (s.1 1)) (lam (s.1 2)) (𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2))) inf_le_left inf_le_right).hom ≫
          (O (lam (s.1 2)) (𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2)))).ι) = M3 := by
      rw [← Category.assoc, hsp]
      simp only [M3, Category.assoc]
      rw [L3 (lam (s.1 1)) (lam (s.1 2)) (𝒰.U (lam (s.1 1)) ⊓ 𝒰.U (lam (s.1 2))) (⨅ j, 𝒰.U (lam (s.1 j))) inf_le_left inf_le_right
        (hW 1) (hW 2) hUβγ, reassoc_of% (Lℓ (s.1 1) _ _ _ _ hℓt hVW (𝒱.inter_le_inter_face s 0) hUβγ)]
    rw [e1, e2] at hR
    exact hR
  have Fuw : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) M4 M1 fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))) ((i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))) Ue
      (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resuw).toLinearMap ∘ₗ βuw x) := by

    have L2 : ∀ (x y : 𝒱.ι) (h : x < y) (W : X₀.Opens) (hW' : W ≤ 𝒱.U x ⊓ 𝒱.U y),
        (ΦX x y h W hW').hom ≫ (OX y W).ι = (Z x).homOfLE (hOXm x hW') ≫ (φX x y h).hom ≫ (OX y (𝒱.U x ⊓ 𝒱.U y)).ι := by
      intro x y h W hW'
      rw [← Scheme.homOfLE_ι (Z y) (hOXm y hW'), ← Category.assoc, hΦX, Category.assoc]
    have L3 : ∀ (a b : 𝒰.ι) (W W' : A₀.Opens) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (ha' : W' ≤ 𝒰.U a) (hb' : W' ≤ 𝒰.U b)
        (hWW : W' ≤ W), (Φ a b W' ha' hb').hom ≫ (O b W').ι = (Y a).homOfLE (hOm a hWW) ≫ (Φ a b W ha hb).hom ≫ (O b W).ι := by
      intro a b W W' ha hb ha' hb' hWW
      rw [← Scheme.homOfLE_ι (Y b) (hOm b hWW), ← Category.assoc, hΦres a b W W' ha hb ha' hb' hWW, Category.assoc]
    have Lℓ : ∀ (x : 𝒱.ι) (WX WX' : X₀.Opens) (WA WA' : A₀.Opens) (h : WX ≤ h₀ ⁻¹ᵁ WA) (h' : WX' ≤ h₀ ⁻¹ᵁ WA')
        (hX : WX' ≤ WX) (hA : WA' ≤ WA),
        ℓ x WX' WA' h' ≫ (Y (lam x)).homOfLE (hOm (lam x) hA) = (Z x).homOfLE (hOXm x hX) ≫ ℓ x WX WA h := by
      intro x WX WX' WA WA' h h' hX hA
      rw [← cancel_mono (O (lam x) WA).ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, hℓ, hℓ, Scheme.homOfLE_ι_assoc]

    have ht02 : 𝒱.inter (𝒱.face s 1) ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 2) := le_inf (𝒱.inter_le (𝒱.face s 1) 0) (𝒱.inter_le (𝒱.face s 1) 1)
    have hℓt : 𝒱.inter (𝒱.face s 1) ≤ h₀ ⁻¹ᵁ (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2))) := by
      rw [Scheme.Hom.preimage_inf]
      exact le_inf ((𝒱.inter_le (𝒱.face s 1) 0).trans (hlam₀ _)) ((𝒱.inter_le (𝒱.face s 1) 1).trans (hlam₀ _))
    have hOt : IsAffineOpen (OX (s.1 0) (𝒱.inter (𝒱.face s 1))) :=
      hOXaff (s.1 0) (𝒱.inter (𝒱.face s 1)) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 (𝒱.face s 1)) (𝒱.inter_le (𝒱.face s 1) 0)
    have hβ' : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter (𝒱.face s 1)))
        (hOt.isoSpec.inv ≫ (ΦX (s.1 0) (s.1 2) (s.2 (by decide)) (𝒱.inter (𝒱.face s 1)) ht02).hom ≫
          ℓ (s.1 2) (𝒱.inter (𝒱.face s 1)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2))) hℓt ≫
          (O (lam (s.1 2)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2)))).ι)
        (hOt.isoSpec.inv ≫ ℓ (s.1 0) (𝒱.inter (𝒱.face s 1)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2))) hℓt ≫
          (Φ (lam (s.1 0)) (lam (s.1 2)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2))) inf_le_left inf_le_right).hom ≫
          (O (lam (s.1 2)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2)))).ι)
        fk Lk (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))) ((i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))) Ue βuw := hβuw
    have hR := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat (RingHom.ker π) hI hsmall V ι hι hιI
      ((Z (s.1 0)).presheaf.obj (Opposite.op (OX (s.1 0) (𝒱.inter (𝒱.face s 1)))))
      ((Z (s.1 0)).presheaf.obj (Opposite.op (OX (s.1 0) (𝒱.inter s)))) resuw _ _ fk Lk _ _ Ue _ hβ'
    have hsp : Spec.map (CommRingCat.ofHom resuw.toRingHom) ≫ hOt.isoSpec.inv =
        hOs.isoSpec.inv ≫ (Z (s.1 0)).homOfLE (hOXm (s.1 0) (𝒱.inter_le_inter_face s 1)) :=
      spec_map_comp_isoSpec_inv _ hOs _
    have hUαγ : (⨅ j, 𝒰.U (lam (s.1 j))) ≤ 𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2)) := le_inf (hW 0) (hW 2)
    have e1 : Spec.map (CommRingCat.ofHom resuw.toRingHom) ≫
        (hOt.isoSpec.inv ≫ (ΦX (s.1 0) (s.1 2) (s.2 (by decide)) (𝒱.inter (𝒱.face s 1)) ht02).hom ≫
          ℓ (s.1 2) (𝒱.inter (𝒱.face s 1)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2))) hℓt ≫
          (O (lam (s.1 2)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2)))).ι) = M4 := by
      rw [← Category.assoc, hsp]
      simp only [M4, Category.assoc, hℓ]
      rw [reassoc_of% (L2 _ _ _ _ _), reassoc_of% (L2 _ _ _ _ _), Scheme.homOfLE_homOfLE_assoc]
    have e2 : Spec.map (CommRingCat.ofHom resuw.toRingHom) ≫
        (hOt.isoSpec.inv ≫ ℓ (s.1 0) (𝒱.inter (𝒱.face s 1)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2))) hℓt ≫
          (Φ (lam (s.1 0)) (lam (s.1 2)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2))) inf_le_left inf_le_right).hom ≫
          (O (lam (s.1 2)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2)))).ι) = M1 := by
      rw [← Category.assoc, hsp]
      simp only [M1, Category.assoc]
      rw [L3 (lam (s.1 0)) (lam (s.1 2)) (𝒰.U (lam (s.1 0)) ⊓ 𝒰.U (lam (s.1 2))) (⨅ j, 𝒰.U (lam (s.1 j))) inf_le_left inf_le_right
        (hW 0) (hW 2) hUαγ, reassoc_of% (Lℓ (s.1 0) _ _ _ _ hℓt hVW (𝒱.inter_le_inter_face s 1) hUαγ)]
    rw [e1, e2] at hR
    exact hR

  letI instks : Algebra (ResidueField T') Γ(Xk, (𝒱.comap j₀).inter s) := algebraOfHom fXk ((𝒱.comap j₀).inter s)
  have Suv : ∀ (x : Γ(Ak, Ue)) (ξ' : Module.Dual (ResidueField T') V),
      σX s (((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resuv).toLinearMap ∘ₗ βuv x) ξ') =
        (OModulePresheaf.unit fXk).res ((𝒱.comap j₀).inter_le_inter_face s 2) (B x ξ' ((𝒱.comap j₀).face s 2)) := by
    intro x ξ'
    have hsU0 : 𝒱.inter (𝒱.face s 2) ≤ 𝒱.U (s.1 0) := 𝒱.inter_le (𝒱.face s 2) 0
    letI instksJ : Algebra (ResidueField T') Γ(Xk, (𝒱.comap j₀).inter (𝒱.face s 2)) :=
      algebraOfHom fXk ((𝒱.comap j₀).inter (𝒱.face s 2))
    have hpin : (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) (𝒱.face s 2)).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (σX (𝒱.face s 2)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter (𝒱.face s 2))) →ₐ[T']
            (ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter (𝒱.face s 2)))).toRingHom) ≫
        (hOXaff (s.1 0) (𝒱.inter (𝒱.face s 2)) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 _) hsU0).fromSpec =
        Xk.homOfLE (𝒱.comap_inter_le j₀ (𝒱.face s 2)) ≫ (j₀ ∣_ 𝒱.inter (𝒱.face s 2)) ≫ X₀.homOfLE hsU0 ≫ gZ (s.1 0) :=
      hσX₁ (𝒱.face s 2)
    have hST := AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
      (qZ (s.1 0)) (qZ (s.1 0)) fXk (OX (s.1 0) (𝒱.inter (𝒱.face s 2)))
      (hOXaff (s.1 0) _ (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 _) hsU0)
      (OX (s.1 0) (𝒱.inter s)) hOs
      ((𝒱.comap j₀).inter (𝒱.face s 2)) ((𝒱.comap j₀).inter s)
      (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) _) (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s)
      ((𝒱.comap j₀).inter_le_inter_face s 2)
      (Xk.homOfLE (𝒱.comap_inter_le j₀ (𝒱.face s 2)) ≫ (j₀ ∣_ 𝒱.inter (𝒱.face s 2)) ≫ X₀.homOfLE hsU0 ≫ gZ (s.1 0))
      resuv (σX (𝒱.face s 2)) (σX s) hpin (hσX₂ _) (hσX₂ s) ?_ (βuv x ξ')
    · change σX s ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resuv) (βuv x ξ')) = _
      rw [hST]
      show (Xk.presheaf.map _).hom _ = (Xk.presheaf.map _).hom _
      congr 1
      exact hBuv x ξ'
    · rw [show Spec.map (CommRingCat.ofHom resuv.toRingHom) =
          Spec.map ((Z (s.1 0)).presheaf.map (homOfLE (hOXm (s.1 0) (𝒱.inter_le_inter_face s 2))).op) from rfl,
        IsAffineOpen.map_fromSpec _ hOs, hσX₁ s]
      simp only [← Category.assoc]
      congr 1
      rw [← cancel_mono (𝒱.U (s.1 0)).ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc]
  have Svw : ∀ (x : Γ(Ak, Ue)) (ξ' : Module.Dual (ResidueField T') V),
      σX s (((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hvw).toLinearMap ∘ₗ βvw x) ξ') =
        (OModulePresheaf.unit fXk).res ((𝒱.comap j₀).inter_le_inter_face s 0) (B x ξ' ((𝒱.comap j₀).face s 0)) := by
    intro x ξ'
    change σX s ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hvw) (βvw x ξ')) = _
    rw [N2G.svw T' T π hπ hker hsmall hI ρ hρ V ι hι hιI f₀ 𝒰 Y q hq g hg fk Lk i₀ hi₀ Ue hUe e₁ he₁ O hO hOm hOtop hOinf hOaff σ hσ₁ hσ₂ φ hφq hφg hφO ρab ρbc ρac hρab hρbc hρac ω hω hωZ fX₀ 𝒱 Z qZ hqZ gZ hgZ fXk LX j₀ hj₀ UXe hUXe eX₁ heX₁ OX hOX hOXm hOXtop hOXinf hOXaff σX hσX₁ hσX₂ φX hφXq hφXg hφXO ρXab ρXbc ρXac hρXab hρXbc hρXac ωX hωX hωXZ h₀ hh₀ lam hlam₀ hk hhk hhkf hhom hUX hlamk hZ hhZq hhZg Φ hΦq hΦg hΦres hΦrefl hΦsymm hΦφ ΦX hΦX ℓ hℓ s hvw hhvw (βvw x ξ')]
    show (Xk.presheaf.map _).hom _ = (Xk.presheaf.map _).hom _
    congr 1
    exact hBvw x ξ'
  have Suw : ∀ (x : Γ(Ak, Ue)) (ξ' : Module.Dual (ResidueField T') V),
      σX s (((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resuw).toLinearMap ∘ₗ βuw x) ξ') =
        (OModulePresheaf.unit fXk).res ((𝒱.comap j₀).inter_le_inter_face s 1) (B x ξ' ((𝒱.comap j₀).face s 1)) := by
    intro x ξ'
    have hsU0 : 𝒱.inter (𝒱.face s 1) ≤ 𝒱.U (s.1 0) := 𝒱.inter_le (𝒱.face s 1) 0
    letI instksJ : Algebra (ResidueField T') Γ(Xk, (𝒱.comap j₀).inter (𝒱.face s 1)) :=
      algebraOfHom fXk ((𝒱.comap j₀).inter (𝒱.face s 1))
    have hpin : (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) (𝒱.face s 1)).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (σX (𝒱.face s 1)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter (𝒱.face s 1))) →ₐ[T']
            (ResidueField T') ⊗[T'] Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter (𝒱.face s 1)))).toRingHom) ≫
        (hOXaff (s.1 0) (𝒱.inter (𝒱.face s 1)) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 _) hsU0).fromSpec =
        Xk.homOfLE (𝒱.comap_inter_le j₀ (𝒱.face s 1)) ≫ (j₀ ∣_ 𝒱.inter (𝒱.face s 1)) ≫ X₀.homOfLE hsU0 ≫ gZ (s.1 0) :=
      hσX₁ (𝒱.face s 1)
    have hST := AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
      (qZ (s.1 0)) (qZ (s.1 0)) fXk (OX (s.1 0) (𝒱.inter (𝒱.face s 1)))
      (hOXaff (s.1 0) _ (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 _) hsU0)
      (OX (s.1 0) (𝒱.inter s)) hOs
      ((𝒱.comap j₀).inter (𝒱.face s 1)) ((𝒱.comap j₀).inter s)
      (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) _) (Scheme.OrderedAffineCover.isAffineOpen_inter fXk (𝒱.comap j₀) s)
      ((𝒱.comap j₀).inter_le_inter_face s 1)
      (Xk.homOfLE (𝒱.comap_inter_le j₀ (𝒱.face s 1)) ≫ (j₀ ∣_ 𝒱.inter (𝒱.face s 1)) ≫ X₀.homOfLE hsU0 ≫ gZ (s.1 0))
      resuw (σX (𝒱.face s 1)) (σX s) hpin (hσX₂ _) (hσX₂ s) ?_ (βuw x ξ')
    · change σX s ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resuw) (βuw x ξ')) = _
      rw [hST]
      show (Xk.presheaf.map _).hom _ = (Xk.presheaf.map _).hom _
      congr 1
      exact hBuw x ξ'
    · rw [show Spec.map (CommRingCat.ofHom resuw.toRingHom) =
          Spec.map ((Z (s.1 0)).presheaf.map (homOfLE (hOXm (s.1 0) (𝒱.inter_le_inter_face s 1))).op) from rfl,
        IsAffineOpen.map_fromSpec _ hOs, hσX₁ s]
      simp only [← Category.assoc]
      congr 1
      rw [← cancel_mono (𝒱.U (s.1 0)).ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc]

  have D12 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)) M1 M2 fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))) ((i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))) Ue
      (-(fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resuw).toLinearMap ∘ₗ βuw x) +
        (fun a => csX ((Xk.presheaf.map (homOfLE hUX).op).hom ((hk.app Ue).hom a))) +
        (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hvw).toLinearMap ∘ₗ βvw x) +
        (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resuv).toLinearMap ∘ₗ βuv x)) := by

    have L2 : ∀ (x y : 𝒱.ι) (h : x < y) (W : X₀.Opens) (hW' : W ≤ 𝒱.U x ⊓ 𝒱.U y),
        (ΦX x y h W hW').hom ≫ (OX y W).ι = (Z x).homOfLE (hOXm x hW') ≫ (φX x y h).hom ≫ (OX y (𝒱.U x ⊓ 𝒱.U y)).ι := by
      intro x y h W hW'
      rw [← Scheme.homOfLE_ι (Z y) (hOXm y hW'), ← Category.assoc, hΦX, Category.assoc]
    have Tℓ : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens) (h : WX ≤ h₀ ⁻¹ᵁ WA),
        ℓ x WX WA h ≫ (O (lam x) WA).ι ≫ q (lam x) = (OX x WX).ι ≫ qZ x := by
      intro x WX WA h
      rw [← Category.assoc, hℓ, Category.assoc, hhZq]
    have TΦX : ∀ (x y : 𝒱.ι) (h : x < y) (W : X₀.Opens) (hW' : W ≤ 𝒱.U x ⊓ 𝒱.U y),
        (ΦX x y h W hW').hom ≫ (OX y W).ι ≫ qZ y = (OX x W).ι ≫ qZ x := by
      intro x y h W hW'
      rw [reassoc_of% (L2 x y h W hW'), hφXq, Scheme.homOfLE_ι_assoc]
    have hbase : hOs.isoSpec.inv ≫ (OX (s.1 0) (𝒱.inter s)).ι ≫ qZ (s.1 0) =
        Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) := by
      rw [IsAffineOpen.isoSpec_inv_ι_assoc, fromSpec_comp_eq]
    have hT1 : M1 ≫ q (lam (s.1 2)) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) := by
      simp only [M1, Category.assoc]; rw [hΦq, Tℓ, hbase]
    have hT2 : M2 ≫ q (lam (s.1 2)) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) := by
      simp only [M2, Category.assoc]; rw [hΦq, hΦq, Tℓ, hbase]
    have hT3 : M3 ≫ q (lam (s.1 2)) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) := by
      simp only [M3, Category.assoc]; rw [hΦq, Tℓ, TΦX, hbase]
    have hT4 : M4 ≫ q (lam (s.1 2)) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) := by
      simp only [M4, Category.assoc]; rw [Tℓ, TΦX, hbase]
    have hT5 : M5 ≫ q (lam (s.1 2)) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Z (s.1 0), OX (s.1 0) (𝒱.inter s)))) := by
      simp only [M5, Category.assoc]; rw [Tℓ, TΦX, TΦX, hbase]

    have haWγ : IsPullback ((i₀ ∣_ 𝒰.U (lam (s.1 2))) ≫ g (lam (s.1 2))) ((i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))).ι ≫ fk) (q (lam (s.1 2)))
        (Spec.map (CommRingCat.ofHom (residue T'))) := by
      have h1 : IsPullback (i₀ ∣_ 𝒰.U (lam (s.1 2))) ((i₀ ⁻¹ᵁ 𝒰.U (lam (s.1 2))).ι ≫ fk) ((𝒰.U (lam (s.1 2))).ι ≫ f₀)
          (Spec.map (CommRingCat.ofHom ρ)) :=
        IsPullback.paste_vert (isPullback_morphismRestrict i₀ (𝒰.U (lam (s.1 2)))) hi₀
      have h2 := IsPullback.paste_horiz h1 (hg (lam (s.1 2)))
      rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ] at h2

    have c41 := specMap_mk_comp_eq_of_isTangentCoordsOfPairAtVia (RingHom.ker π) V ι _ _ _ fk Lk _ _ Ue _ Fuw
    have c45 := specMap_mk_comp_eq_of_isTangentCoordsOfPairAtVia (RingHom.ker π) V ι _ _ _ fk Lk _ _ Ue _ X45
    have c53 := specMap_mk_comp_eq_of_isTangentCoordsOfPairAtVia (RingHom.ker π) V ι _ _ _ fk Lk _ _ Ue _ Fvw
    have c32 := specMap_mk_comp_eq_of_isTangentCoordsOfPairAtVia (RingHom.ker π) V ι _ _ _ fk Lk _ _ Ue _ Fuv

    have V14 := ViaTorsor.via_symm (RingHom.ker π) hI hsmall V ι hι hιI ((Z (s.1 0)).presheaf.obj (Opposite.op (OX (s.1 0) (𝒱.inter s))))
      (q (lam (s.1 2))) fk Lk _ _ haWγ Ue hUe e₁ he₁ M4 M1 hT4 hT1 c41 Fuw
    have V15 := ViaTorsor.via_trans (RingHom.ker π) hI hsmall V ι hι hιI ((Z (s.1 0)).presheaf.obj (Opposite.op (OX (s.1 0) (𝒱.inter s))))
      (q (lam (s.1 2))) fk Lk _ _ haWγ Ue hUe e₁ he₁ M1 M4 M5 hT1 hT4 hT5 c41.symm c45 V14 X45
    have V13 := ViaTorsor.via_trans (RingHom.ker π) hI hsmall V ι hι hιI ((Z (s.1 0)).presheaf.obj (Opposite.op (OX (s.1 0) (𝒱.inter s))))
      (q (lam (s.1 2))) fk Lk _ _ haWγ Ue hUe e₁ he₁ M1 M5 M3 hT1 hT5 hT3 (c41.symm.trans c45) c53 V15 Fvw
    exact ViaTorsor.via_trans (RingHom.ker π) hI hsmall V ι hι hιI ((Z (s.1 0)).presheaf.obj (Opposite.op (OX (s.1 0) (𝒱.inter s))))
      (q (lam (s.1 2))) fk Lk _ _ haWγ Ue hUe e₁ he₁ M1 M3 M2 hT1 hT3 hT2 ((c41.symm.trans c45).trans c53) c32 V13 Fuv

  have A12 : ∀ (x : Γ(Ak, Ue)) (ξ' : Module.Dual (ResidueField T') V),
      σX s ((-(fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resuw).toLinearMap ∘ₗ βuw x) +
        (fun a => csX ((Xk.presheaf.map (homOfLE hUX).op).hom ((hk.app Ue).hom a))) +
        (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hvw).toLinearMap ∘ₗ βvw x) +
        (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resuv).toLinearMap ∘ₗ βuv x)) x ξ') =
      OModulePresheaf.unitPullback (πX := fXk) hk (𝒱.comap j₀) (𝒰.comap i₀) lam hlamk 2 (ω.1 x ξ') s :=
    N2G.aread T' T π hπ hker hsmall hI ρ hρ V ι hι hιI f₀ 𝒰 Y q hq g hg fk Lk i₀ hi₀ Ue hUe e₁ he₁ O hO hOm hOtop hOinf hOaff σ hσ₁ hσ₂ φ hφq hφg hφO ρab ρbc ρac hρab hρbc hρac ω hω hωZ fX₀ 𝒱 Z qZ hqZ gZ hgZ fXk LX j₀ hj₀ UXe hUXe eX₁ heX₁ OX hOX hOXm hOXtop hOXinf hOXaff σX hσX₁ hσX₂ φX hφXq hφXg hφXO ρXab ρXbc ρXac hρXab hρXbc hρXac ωX hωX hωXZ h₀ hh₀ lam hlam₀ hk hhk hhkf hhom hUX hlamk hZ hhZq hhZg Φ hΦq hΦg hΦres hΦrefl hΦsymm hΦφ ΦX hΦX ℓ hℓ s _ D12

  rw [← A12 a ξ, ← hpX, OModulePresheaf.d_apply, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_one_smul, neg_one_sq,
    Pi.add_apply, Pi.neg_apply, LinearMap.add_apply, LinearMap.neg_apply, map_add, map_neg, map_sub, Suv, Svw, Suw]
  abel

end S_AlgebraicGeometry_SmallExtension_unitPullback_obstruction_two_cocycle_sub_eq_d_of_one_cochain_pin
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_unitPullback_obstruction_two_cocycle_sub_eq_d_of_one_cochain_pin (solution)
