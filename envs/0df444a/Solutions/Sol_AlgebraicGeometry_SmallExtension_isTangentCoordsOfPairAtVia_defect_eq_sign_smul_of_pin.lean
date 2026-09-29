-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_defect_eq_sign_smul_of_pin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/cf43adbd-f050-5c52-8b1a-17e1df7cb6c9

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_add
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_of_isPullback_of_comp_mono
import Theorems.Thm_AlgebraicGeometry_exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_defect_eq_sign_smul_of_pin

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 800000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u
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

namespace AltReadAux

theorem haW_chart {T' T : Type u} [CommRing T'] [IsLocalRing T'] [CommRing T] (π : T' →+* T)
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) {U : A₀.Opens} {Yz : Scheme.{u}} (qz : Yz ⟶ Spec (CommRingCat.of T'))
    (gz : (↑U : Scheme.{u}) ⟶ Yz) (hg : IsPullback gz (U.ι ≫ f₀) qz (Spec.map (CommRingCat.ofHom π)))
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (i₀ : Ak ⟶ A₀)
    (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ))) :
    IsPullback ((i₀ ∣_ U) ≫ gz) ((i₀ ⁻¹ᵁ U).ι ≫ fk) qz (Spec.map (CommRingCat.ofHom (residue T'))) := by
  have h1 : IsPullback (i₀ ∣_ U) ((i₀ ⁻¹ᵁ U).ι ≫ fk) (U.ι ≫ f₀) (Spec.map (CommRingCat.ofHom ρ)) :=
    (isPullback_morphismRestrict i₀ U).paste_vert hi₀
  have h2 := h1.paste_horiz hg
  have hρπ : Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom π) = Spec.map (CommRingCat.ofHom (residue T')) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  rwa [hρπ] at h2

theorem resNat {A₀ Ak : Scheme.{u}} (i₀ : Ak ⟶ A₀) {W₁ W₂ : A₀.Opens} (h : W₁ ≤ W₂) :
    Ak.homOfLE (i₀.preimage_mono h) ≫ (i₀ ∣_ W₂) = (i₀ ∣_ W₁) ≫ A₀.homOfLE h := by
  rw [← cancel_mono W₂.ι]
  simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]

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

end AltReadAux

namespace AltReadAux

theorem transport
    {T' T : Type u} [CommRing T'] [IsLocalRing T'] [CommRing T] (π : T' →+* T)
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥) (hI : RingHom.ker π ≤ maximalIdeal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T')
    {A₀ : Scheme.{u}} {Uy Uz : A₀.Opens} {Yy Yz : Scheme.{u}}
    (gy : (↑Uy : Scheme.{u}) ⟶ Yy) (gz : (↑Uz : Scheme.{u}) ⟶ Yz)
    (Oy : A₀.Opens → Yy.Opens) (Oz : A₀.Opens → Yz.Opens)
    (hOy : ∀ W : A₀.Opens, gy ⁻¹ᵁ Oy W = Uy.ι ⁻¹ᵁ W) (hOz : ∀ W : A₀.Opens, gz ⁻¹ᵁ Oz W = Uz.ι ⁻¹ᵁ W)
    {W : A₀.Opens} (hWy : W ≤ Uy) (hWz : W ≤ Uz)
    (Φh : (↑(Oy W) : Scheme.{u}) ⟶ ↑(Oz W))
    (hΦg : ∀ (γ : (↑W : Scheme.{u}) ⟶ ↑(Oy W)) (γ' : (↑W : Scheme.{u}) ⟶ ↑(Oz W)),
      γ ≫ (Oy W).ι = A₀.homOfLE hWy ≫ gy → γ' ≫ (Oz W).ι = A₀.homOfLE hWz ≫ gz → γ ≫ Φh = γ')
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) (Ue : Ak.Opens)
    (C : Type u) [CommRing C] [Algebra T' C]
    (m m' : Spec (CommRingCat.of C) ⟶ ↑(Oy W))
    (E : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] C)))
    (hE : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C (m ≫ (Oy W).ι) (m' ≫ (Oy W).ι) fk Lk (i₀ ⁻¹ᵁ Uy) ((i₀ ∣_ Uy) ≫ gy) Ue E) :
    IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C (m ≫ Φh ≫ (Oz W).ι) (m' ≫ Φh ≫ (Oz W).ι) fk Lk (i₀ ⁻¹ᵁ Uz) ((i₀ ∣_ Uz) ≫ gz) Ue E := by
  obtain ⟨aWy, haWyι, hsqy⟩ := AlgebraicGeometry.exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift Uy gy Oy hOy i₀ W hWy

  have hfac := isTangentCoordsOfPairAtVia_of_isPullback_of_comp_mono (RingHom.ker π) hI hsmall V ι C (Oy W).ι m m' fk Lk
    (i₀ ⁻¹ᵁ Uy) (i₀ ⁻¹ᵁ W) (i₀.preimage_mono hWy) ((i₀ ∣_ Uy) ≫ gy) aWy hsqy Ue E hE

  obtain ⟨γy, hγy⟩ := exists_gamma Uy gy Oy hOy W hWy
  obtain ⟨γz, hγz⟩ := exists_gamma Uz gz Oz hOz W hWz
  have e1 : aWy = (i₀ ∣_ W) ≫ γy := by
    rw [← cancel_mono (Oy W).ι, haWyι, Category.assoc, hγy, ← Category.assoc, resNat i₀ hWy, Category.assoc]
  have haW : Ak.homOfLE (i₀.preimage_mono hWz) ≫ ((i₀ ∣_ Uz) ≫ gz) = aWy ≫ (Φh ≫ (Oz W).ι) := by
    rw [e1, Category.assoc, ← Category.assoc γy, hΦg γy γz hγy hγz, hγz, ← Category.assoc (Ak.homOfLE _), resNat i₀ hWz, Category.assoc]
  have hpost := isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq (RingHom.ker π) V ι C (Φh ≫ (Oz W).ι) m m' fk Lk
    (i₀ ⁻¹ᵁ W) (i₀ ⁻¹ᵁ Uz) (i₀.preimage_mono hWz) aWy ((i₀ ∣_ Uz) ≫ gz) haW Ue E hfac
  simpa only [Category.assoc] using hpost

end AltReadAux

namespace AltReadAux

theorem modI_of_via {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]
    {Y : Scheme.{u}} {u v : Spec (CommRingCat.of C) ⟶ Y}
    {Ak : Scheme.{u}} {xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))} {Lk : RelativeGroupLaw (ResidueField T') xk}
    {W : Ak.Opens} {aW : (W : Scheme.{u}) ⟶ Y} {Ue : Ak.Opens}
    {c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))}
    (h : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue c) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v := by
  obtain ⟨w₀, hw₀, w₁, ⟨ϑ, _, φ, hu, hv, _⟩, -, -⟩ := h
  rw [← hu, ← hv, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact x.2

end AltReadAux

open AltReadAux ViaTorsor

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀]
    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))

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

    (f : Fin 3 → 𝒰.ι) (W : A₀.Opens) (hW : ∀ j, W ≤ 𝒰.U (f j))
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    (ℓ : Spec (CommRingCat.of C) ⟶ ↑(O (f 0) W))
    (hℓ : ℓ ≫ (O (f 0) W).ι ≫ q (f 0) = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (D : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] C)))
    (hD : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C
      (ℓ ≫ (Φ (f 0) (f 2) W (hW 0) (hW 2)).hom ≫ (O (f 2) W).ι)
      (ℓ ≫ (Φ (f 0) (f 1) W (hW 0) (hW 1)).hom ≫ (Φ (f 1) (f 2) W (hW 1) (hW 2)).hom ≫ (O (f 2) W).ι)
      fk Lk (i₀ ⁻¹ᵁ 𝒰.U (f 2)) ((i₀ ∣_ 𝒰.U (f 2)) ≫ g (f 2)) Ue D) :
    (¬ Function.Injective f → ∀ a : Γ(Ak, Ue), D a = 0) ∧
    (∀ (hinj : Function.Injective f) (r : 𝒰.Idx 2) (hr : ∀ j, r.1 j = f ((Tuple.sort f) j))
      (hWr : W ≤ 𝒰.inter r),
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      ∀ (cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))
        (hcs : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (Φ (r.1 0) (r.1 2) (𝒰.inter r) (𝒰.inter_le r 0) (𝒰.inter_le r 2)).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (Φ (r.1 0) (r.1 1) (𝒰.inter r) (𝒰.inter_le r 0) (𝒰.inter_le r 1)).hom ≫
              (Φ (r.1 1) (r.1 2) (𝒰.inter r) (𝒰.inter_le r 1) (𝒰.inter_le r 2)).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs)
        (θ : Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) →ₐ[T'] C)
        (hθ : Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
            (hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv =
          ℓ ≫ (Φ (f 0) (r.1 0) W (hW 0) ((hWr.trans (𝒰.inter_le r 0)))).hom ≫
            (Y (r.1 0)).homOfLE (hOm (r.1 0) hWr)),
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        D a ξ = ((Equiv.Perm.sign (Tuple.sort f) : ℤˣ) : ℤ) •
          (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) θ) (cs a ξ)) := by
  classical

  have haWz : ∀ z : 𝒰.ι, IsPullback ((i₀ ∣_ 𝒰.U z) ≫ g z) ((i₀ ⁻¹ᵁ 𝒰.U z).ι ≫ fk) (q z)
      (Spec.map (CommRingCat.ofHom (residue T'))) := fun z => haW_chart π ρ hρ f₀ (q z) (g z) (hg z) fk i₀ hi₀
  have hΦsymm' : ∀ (a b : 𝒰.ι) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) {Z : Scheme.{u}} (h : (↑(O a W) : Scheme.{u}) ⟶ Z),
      (Φ a b W ha hb).hom ≫ (Φ b a W hb ha).hom ≫ h = h := by
    intro a b ha hb Z h
    rw [← Category.assoc, hΦsymm, Category.id_comp]

  have hT : ∀ (y z : 𝒰.ι) (hy : W ≤ 𝒰.U y) (hz : W ≤ 𝒰.U z) (m m' : Spec (CommRingCat.of C) ⟶ ↑(O y W))
      (E : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] C))),
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C (m ≫ (O y W).ι) (m' ≫ (O y W).ι) fk Lk (i₀ ⁻¹ᵁ 𝒰.U y) ((i₀ ∣_ 𝒰.U y) ≫ g y) Ue E →
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C (m ≫ (Φ y z W hy hz).hom ≫ (O z W).ι) (m' ≫ (Φ y z W hy hz).hom ≫ (O z W).ι)
        fk Lk (i₀ ⁻¹ᵁ 𝒰.U z) ((i₀ ∣_ 𝒰.U z) ≫ g z) Ue E :=
    fun y z hy hz m m' E hE => transport π hsmall hI V ι (g y) (g z) (O y) (O z) (hO y) (hO z) hy hz (Φ y z W hy hz).hom
      (hΦg y z W hy hz) fk Lk i₀ Ue C m m' E hE

  have hU : ∀ (z : 𝒰.ι) (u v : Spec (CommRingCat.of C) ⟶ Y z)
      (hu : u ≫ q z = Spec.map (CommRingCat.ofHom (algebraMap T' C))) (hv : v ≫ q z = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
      {E E' : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] C))},
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C u v fk Lk (i₀ ⁻¹ᵁ 𝒰.U z) ((i₀ ∣_ 𝒰.U z) ≫ g z) Ue E →
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C u v fk Lk (i₀ ⁻¹ᵁ 𝒰.U z) ((i₀ ∣_ 𝒰.U z) ≫ g z) Ue E' → E = E' :=
    fun z u v hu hv E E' hE hE' => via_unique (RingHom.ker π) hI hsmall V ι hι hιI C (q z) fk Lk (i₀ ⁻¹ᵁ 𝒰.U z)
      ((i₀ ∣_ 𝒰.U z) ≫ g z) (haWz z) Ue hUe e₁ he₁ u v hu hv (modI_of_via _ V ι C hE) hE hE'
  have hS : ∀ (z : 𝒰.ι) (u v : Spec (CommRingCat.of C) ⟶ Y z)
      (hu : u ≫ q z = Spec.map (CommRingCat.ofHom (algebraMap T' C))) (hv : v ≫ q z = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
      {E : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] C))},
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C u v fk Lk (i₀ ⁻¹ᵁ 𝒰.U z) ((i₀ ∣_ 𝒰.U z) ≫ g z) Ue E →
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C v u fk Lk (i₀ ⁻¹ᵁ 𝒰.U z) ((i₀ ∣_ 𝒰.U z) ≫ g z) Ue (-E) :=
    fun z u v hu hv E hE => via_symm (RingHom.ker π) hI hsmall V ι hι hιI C (q z) fk Lk (i₀ ⁻¹ᵁ 𝒰.U z)
      ((i₀ ∣_ 𝒰.U z) ≫ g z) (haWz z) Ue hUe e₁ he₁ u v hu hv (modI_of_via _ V ι C hE) hE
  have h0 : ∀ (z : 𝒰.ι) (u : Spec (CommRingCat.of C) ⟶ Y z)
      (hu : u ≫ q z = Spec.map (CommRingCat.ofHom (algebraMap T' C))),
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C u u fk Lk (i₀ ⁻¹ᵁ 𝒰.U z) ((i₀ ∣_ 𝒰.U z) ≫ g z) Ue 0 :=
    fun z u hu => via_self (RingHom.ker π) hI hsmall V ι hι hιI C (q z) fk Lk (i₀ ⁻¹ᵁ 𝒰.U z)
      ((i₀ ∣_ 𝒰.U z) ≫ g z) (haWz z) Ue hUe e₁ he₁ u hu
  refine ⟨?_, ?_⟩
  ·
    intro hninj
    have gen : ∀ (a b c : 𝒰.ι) (ha : W ≤ 𝒰.U a) (hb : W ≤ 𝒰.U b) (hc : W ≤ 𝒰.U c)
        (m : Spec (CommRingCat.of C) ⟶ ↑(O a W)) (hm : m ≫ (O a W).ι ≫ q a = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
        (E : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] C))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C (m ≫ (Φ a c W ha hc).hom ≫ (O c W).ι)
          (m ≫ (Φ a b W ha hb).hom ≫ (Φ b c W hb hc).hom ≫ (O c W).ι) fk Lk (i₀ ⁻¹ᵁ 𝒰.U c) ((i₀ ∣_ 𝒰.U c) ≫ g c) Ue E →
        (a = b ∨ b = c ∨ a = c) → E = 0 := by
      intro a b c ha hb hc m hm E hE habc
      rcases habc with rfl | rfl | rfl
      · simp only [hΦrefl, Category.id_comp] at hE
        have hu : (m ≫ (Φ a c W ha hc).hom ≫ (O c W).ι) ≫ q c = Spec.map (CommRingCat.ofHom (algebraMap T' C)) := by
          simp only [Category.assoc, hΦq]; exact hm
        exact hU c _ _ hu hu hE (h0 c _ hu)
      · simp only [hΦrefl, Category.id_comp] at hE
        have hu : (m ≫ (Φ a b W ha hb).hom ≫ (O b W).ι) ≫ q b = Spec.map (CommRingCat.ofHom (algebraMap T' C)) := by
          simp only [Category.assoc, hΦq]; exact hm
        exact hU b _ _ hu hu hE (h0 b _ hu)
      · simp only [hΦrefl, Category.id_comp, hΦsymm'] at hE
        have hu : (m ≫ (O a W).ι) ≫ q a = Spec.map (CommRingCat.ofHom (algebraMap T' C)) := by
          simp only [Category.assoc]; exact hm
        exact hU a _ _ hu hu hE (h0 a _ hu)
    have hE0 : D = 0 := by
      refine gen (f 0) (f 1) (f 2) (hW 0) (hW 1) (hW 2) ℓ hℓ D hD ?_
      by_contra hne
      push Not at hne
      exact hninj fun i j hij => by
        fin_cases i <;> fin_cases j
        · rfl
        · exact absurd hij hne.1
        · exact absurd hij hne.2.2
        · exact absurd hij.symm hne.1
        · rfl
        · exact absurd hij hne.2.1
        · exact absurd hij.symm hne.2.2
        · exact absurd hij.symm hne.2.1
        · rfl
    intro a; rw [hE0]; rfl
  ·
    intro hinj r hr hWr
    letI instR : Algebra T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
    intro cs hcs θ hθ
    set hR0 := hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0) with hR0def

    have hr0 : W ≤ 𝒰.U (r.1 0) := hWr.trans (𝒰.inter_le r 0)
    have hr1 : W ≤ 𝒰.U (r.1 1) := hWr.trans (𝒰.inter_le r 1)
    have hr2 : W ≤ 𝒰.U (r.1 2) := hWr.trans (𝒰.inter_le r 2)

    have hR := isTangentCoordsOfPairAtVia_comp_of_flat (RingHom.ker π) hI hsmall V ι hι hιI Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) C θ
      _ _ fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs hcs
    rw [← Category.assoc (Spec.map _), ← Category.assoc (Spec.map _), hθ] at hR
    simp only [Category.assoc] at hR
    rw [← Category.assoc ((Y (r.1 0)).homOfLE _), ← hΦres (r.1 0) (r.1 2) (𝒰.inter r) W (𝒰.inter_le r 0) (𝒰.inter_le r 2) hr0 hr2 hWr,
      ← Category.assoc ((Y (r.1 0)).homOfLE _), ← hΦres (r.1 0) (r.1 1) (𝒰.inter r) W (𝒰.inter_le r 0) (𝒰.inter_le r 1) hr0 hr1 hWr] at hR
    simp only [Category.assoc] at hR
    rw [← Category.assoc ((Y (r.1 1)).homOfLE _), ← hΦres (r.1 1) (r.1 2) (𝒰.inter r) W (𝒰.inter_le r 1) (𝒰.inter_le r 2) hr1 hr2 hWr] at hR
    simp only [Category.assoc, Scheme.homOfLE_ι] at hR

    set E : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] C)) :=
      fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) θ).toLinearMap ∘ₗ cs a with hEdef

    have hov : ∀ {Z : 𝒰.ι} (m : Spec (CommRingCat.of C) ⟶ ↑(O Z W)) (hz : W ≤ 𝒰.U Z),
        m ≫ (O Z W).ι ≫ q Z = ℓ ≫ (O (f 0) W).ι ≫ q (f 0) → (m ≫ (O Z W).ι) ≫ q Z = Spec.map (CommRingCat.ofHom (algebraMap T' C)) := by
      intro Z m hz h; rw [Category.assoc, h]; exact hℓ

    have core : ∀ (x y z : 𝒰.ι) (hx : W ≤ 𝒰.U x) (hy : W ≤ 𝒰.U y) (hz : W ≤ 𝒰.U z)
        (E : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] C))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C
          (ℓ ≫ (Φ (f 0) x W (hW 0) hx).hom ≫ (Φ x z W hx hz).hom ≫ (O z W).ι)
          (ℓ ≫ (Φ (f 0) x W (hW 0) hx).hom ≫ (Φ x y W hx hy).hom ≫ (Φ y z W hy hz).hom ≫ (O z W).ι)
          fk Lk (i₀ ⁻¹ᵁ 𝒰.U z) ((i₀ ∣_ 𝒰.U z) ≫ g z) Ue E →
        (x = f 0 ∧ y = f 1 ∧ z = f 2 → E = D) ∧
        (x = f 1 ∧ y = f 0 ∧ z = f 2 → E = -D) ∧
        (x = f 0 ∧ y = f 2 ∧ z = f 1 → E = -D) ∧
        (x = f 1 ∧ y = f 2 ∧ z = f 0 → E = D) ∧
        (x = f 2 ∧ y = f 0 ∧ z = f 1 → E = D) ∧
        (x = f 2 ∧ y = f 1 ∧ z = f 0 → E = -D) := by
      intro x y z hx hy hz E hE

      have ov : ∀ (m : Spec (CommRingCat.of C) ⟶ Y (f 2)), m ≫ q (f 2) = ℓ ≫ (O (f 0) W).ι ≫ q (f 0) →
          m ≫ q (f 2) = Spec.map (CommRingCat.ofHom (algebraMap T' C)) := fun m h => h.trans hℓ
      have OV : ∀ (m : Spec (CommRingCat.of C) ⟶ Y (f 2)), m ≫ q (f 2) = ℓ ≫ (O (f 0) W).ι ≫ q (f 0) →
          m ≫ q (f 2) = Spec.map (CommRingCat.ofHom (algebraMap T' C)) := fun m h => h.trans hℓ
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rintro ⟨rfl, rfl, rfl⟩
        simp only [hΦrefl, Category.id_comp] at hE
        exact hU (f 2) _ _ (OV _ (by simp only [Category.assoc, hΦq])) (OV _ (by simp only [Category.assoc, hΦq])) hE hD
      · rintro ⟨rfl, rfl, rfl⟩
        simp only [hΦsymm'] at hE
        exact hU (f 2) _ _ (OV _ (by simp only [Category.assoc, hΦq])) (OV _ (by simp only [Category.assoc, hΦq])) hE
          (hS (f 2) _ _ (OV _ (by simp only [Category.assoc, hΦq])) (OV _ (by simp only [Category.assoc, hΦq])) hD)
      · rintro ⟨rfl, rfl, rfl⟩
        simp only [hΦrefl, Category.id_comp] at hE
        simp only [← Category.assoc] at hE
        have hE' := hT (f 1) (f 2) (hW 1) (hW 2) _ _ E hE
        simp only [Category.assoc, hΦsymm'] at hE'
        exact hU (f 2) _ _ (OV _ (by simp only [Category.assoc, hΦq])) (OV _ (by simp only [Category.assoc, hΦq])) hE'
          (hS (f 2) _ _ (OV _ (by simp only [Category.assoc, hΦq])) (OV _ (by simp only [Category.assoc, hΦq])) hD)
      · rintro ⟨rfl, rfl, rfl⟩
        simp only [hΦsymm'] at hE
        have hE0 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C (ℓ ≫ (O (f 0) W).ι)
            ((((ℓ ≫ (Φ (f 0) (f 1) W (hW 0) hx).hom) ≫ (Φ (f 1) (f 2) W hx hy).hom) ≫ (Φ (f 2) (f 0) W hy hz).hom) ≫ (O (f 0) W).ι)
            fk Lk (i₀ ⁻¹ᵁ 𝒰.U (f 0)) ((i₀ ∣_ 𝒰.U (f 0)) ≫ g (f 0)) Ue E := by simpa only [Category.assoc] using hE
        have hE' := hT (f 0) (f 2) (hW 0) (hW 2) _ _ E hE0
        simp only [Category.assoc, hΦsymm'] at hE'
        exact hU (f 2) _ _ (OV _ (by simp only [Category.assoc, hΦq])) (OV _ (by simp only [Category.assoc, hΦq])) hE' hD
      · rintro ⟨rfl, rfl, rfl⟩
        simp only [hΦsymm'] at hE
        simp only [← Category.assoc] at hE
        have hE' := hT (f 1) (f 2) (hW 1) (hW 2) _ _ E hE
        simp only [Category.assoc, hΦsymm'] at hE'
        exact hU (f 2) _ _ (OV _ (by simp only [Category.assoc, hΦq])) (OV _ (by simp only [Category.assoc, hΦq])) hE' hD
      · rintro ⟨rfl, rfl, rfl⟩
        simp only [hΦsymm'] at hE
        have hE0 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C (ℓ ≫ (O (f 0) W).ι)
            ((((ℓ ≫ (Φ (f 0) (f 2) W (hW 0) hx).hom) ≫ (Φ (f 2) (f 1) W hx hy).hom) ≫ (Φ (f 1) (f 0) W hy hz).hom) ≫ (O (f 0) W).ι)
            fk Lk (i₀ ⁻¹ᵁ 𝒰.U (f 0)) ((i₀ ∣_ 𝒰.U (f 0)) ≫ g (f 0)) Ue E := by simpa only [Category.assoc] using hE
        have hE' := hT (f 0) (f 1) (hW 0) (hW 1) _ _ E hE0
        simp only [Category.assoc, hΦsymm'] at hE'

        have hD0 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι C
            ((ℓ ≫ (Φ (f 0) (f 2) W (hW 0) (hW 2)).hom) ≫ (O (f 2) W).ι)
            (((ℓ ≫ (Φ (f 0) (f 1) W (hW 0) (hW 1)).hom) ≫ (Φ (f 1) (f 2) W (hW 1) (hW 2)).hom) ≫ (O (f 2) W).ι)
            fk Lk (i₀ ⁻¹ᵁ 𝒰.U (f 2)) ((i₀ ∣_ 𝒰.U (f 2)) ≫ g (f 2)) Ue D := by simpa only [Category.assoc] using hD
        have hD' := hT (f 2) (f 1) (hW 2) (hW 1) _ _ D hD0
        simp only [Category.assoc, hΦsymm'] at hD'
        have OV1 : ∀ (m : Spec (CommRingCat.of C) ⟶ Y (f 1)), m ≫ q (f 1) = ℓ ≫ (O (f 0) W).ι ≫ q (f 0) →
            m ≫ q (f 1) = Spec.map (CommRingCat.ofHom (algebraMap T' C)) := fun m h => h.trans hℓ
        exact hU (f 1) _ _ (OV1 _ (by simp only [Category.assoc, hΦq])) (OV1 _ (by simp only [Category.assoc, hΦq])) hE'
          (hS (f 1) _ _ (OV1 _ (by simp only [Category.assoc, hΦq])) (OV1 _ (by simp only [Category.assoc, hΦq])) hD')

    have hne01 : f 0 ≠ f 1 := fun h => absurd (hinj h) (by decide)
    have hne12 : f 1 ≠ f 2 := fun h => absurd (hinj h) (by decide)
    have hne02 : f 0 ≠ f 2 := fun h => absurd (hinj h) (by decide)
    have hcore := core (r.1 0) (r.1 1) (r.1 2) hr0 hr1 hr2 E hR
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcore

    have hsort : ∀ τ : Equiv.Perm (Fin 3), Monotone (f ∘ τ) → Tuple.sort f = τ := by
      intro τ hτ
      symm
      rw [Tuple.eq_sort_iff]
      exact ⟨hτ, fun i j hij hfij => absurd (τ.injective (hinj hfij)) (ne_of_lt hij)⟩
    have hval : ∀ (τ : Equiv.Perm (Fin 3)), Tuple.sort f = τ → ∀ j, r.1 j = f (τ j) := by
      intro τ hτ j; rw [hr j, hτ]
    have mono3 : ∀ (v : Fin 3 → 𝒰.ι), v 0 < v 1 → v 1 < v 2 → Monotone v := by
      intro v h01 h12
      exact (Fin.strictMono_iff_lt_succ.2 (fun k => by fin_cases k <;> assumption)).monotone
    intro a ξ
    have finish_pos : E = D → Tuple.sort f = 1 ∨ Equiv.Perm.sign (Tuple.sort f) = 1 →
        D a ξ = ((Equiv.Perm.sign (Tuple.sort f) : ℤˣ) : ℤ) •
          (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) θ) (cs a ξ) := by
      intro hED hsgn
      have hs : Equiv.Perm.sign (Tuple.sort f) = 1 := by
        rcases hsgn with h | h
        · rw [h]; exact Equiv.Perm.sign_one
        · exact h
      rw [hs, Units.val_one, one_smul, ← hED]; rfl
    have finish_neg : E = -D → Equiv.Perm.sign (Tuple.sort f) = -1 →
        D a ξ = ((Equiv.Perm.sign (Tuple.sort f) : ℤˣ) : ℤ) •
          (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) θ) (cs a ξ) := by
      intro hED hs
      rw [hs, Units.val_neg, Units.val_one, neg_one_smul]
      have : D = -E := by rw [hED, neg_neg]
      rw [this]; rfl
    rcases lt_trichotomy (f 0) (f 1) with h01 | h01 | h10
    · rcases lt_trichotomy (f 1) (f 2) with h12 | h12 | h21
      ·
        have hτ : Tuple.sort f = 1 := hsort 1 (mono3 _ h01 h12)
        have hv := hval 1 hτ
        exact finish_pos (c1 ⟨hv 0, hv 1, hv 2⟩) (Or.inl hτ)
      · exact absurd h12 hne12
      · rcases lt_trichotomy (f 0) (f 2) with h02 | h02 | h20
        ·
          have hτ : Tuple.sort f = Equiv.swap 1 2 :=
            hsort _ (mono3 (fun j => f (Equiv.swap (1 : Fin 3) 2 j)) (by simpa [Equiv.swap_apply_of_ne_of_ne] using h02) (by simpa using h21))
          have hv := hval _ hτ
          refine finish_neg (c3 ⟨by simpa [Equiv.swap_apply_of_ne_of_ne] using hv 0, by simpa using hv 1, by simpa using hv 2⟩) ?_
          rw [hτ]; exact Equiv.Perm.sign_swap (by decide)
        · exact absurd h02 hne02
        ·
          have hτ : Tuple.sort f = Equiv.swap 1 2 * Equiv.swap 0 1 :=
            hsort _ (mono3 (fun j => f ((Equiv.swap (1 : Fin 3) 2 * Equiv.swap 0 1 : Equiv.Perm (Fin 3)) j))
              (by simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left, Equiv.swap_apply_right] using h20)
              (by simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left, Equiv.swap_apply_right] using h01))
          have hv := hval _ hτ
          refine finish_pos (c5 ⟨by simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne] using hv 0,
            by simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne] using hv 1,
            by simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne] using hv 2⟩) (Or.inr ?_)
          rw [hτ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide), neg_mul_neg, one_mul]
    · exact absurd h01 hne01
    · rcases lt_trichotomy (f 1) (f 2) with h12 | h12 | h21
      · rcases lt_trichotomy (f 0) (f 2) with h02 | h02 | h20
        ·
          have hτ : Tuple.sort f = Equiv.swap 0 1 :=
            hsort _ (mono3 (fun j => f (Equiv.swap (0 : Fin 3) 1 j)) (by simpa using h10) (by simpa [Equiv.swap_apply_of_ne_of_ne] using h02))
          have hv := hval _ hτ
          refine finish_neg (c2 ⟨by simpa using hv 0, by simpa using hv 1, by simpa [Equiv.swap_apply_of_ne_of_ne] using hv 2⟩) ?_
          rw [hτ]; exact Equiv.Perm.sign_swap (by decide)
        · exact absurd h02 hne02
        ·
          have hτ : Tuple.sort f = Equiv.swap 0 1 * Equiv.swap 1 2 :=
            hsort _ (mono3 (fun j => f ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) j))
              (by simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left, Equiv.swap_apply_right] using h12)
              (by simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left, Equiv.swap_apply_right] using h20))
          have hv := hval _ hτ
          refine finish_pos (c4 ⟨by simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne] using hv 0,
            by simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne] using hv 1,
            by simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne] using hv 2⟩) (Or.inr ?_)
          rw [hτ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide), neg_mul_neg, one_mul]
      · exact absurd h12 hne12
      ·
        have hτ : Tuple.sort f = Equiv.swap 0 2 :=
          hsort _ (mono3 (fun j => f (Equiv.swap (0 : Fin 3) 2 j)) (by simpa [Equiv.swap_apply_of_ne_of_ne] using h21) (by simpa [Equiv.swap_apply_of_ne_of_ne] using h10))
        have hv := hval _ hτ
        refine finish_neg (c6 ⟨by simpa using hv 0, by simpa [Equiv.swap_apply_of_ne_of_ne] using hv 1, by simpa using hv 2⟩) ?_
        rw [hτ]; exact Equiv.Perm.sign_swap (by decide)

end S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_defect_eq_sign_smul_of_pin
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_defect_eq_sign_smul_of_pin (solution)
