-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c408145a-d3fb-5339-8e84-761bfb091eab

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations

import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_add
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_eq_of_isTangentCoordsOfPairAtVia_of_isTangentCoordsOfPairAtVia
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_of_isPullback_of_comp_mono
import Theorems.Thm_AlgebraicGeometry_exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 256000000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace OB4aAux

p2m_open "AlgebraicGeometry.Scheme.OrderedAffineCover"

def edge {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (a b : 𝒰.ι) (h : a < b) : 𝒰.Idx 1 :=
  ⟨![a, b], Fin.strictMono_iff_lt_succ.mpr (fun i => by fin_cases i; simpa using h)⟩

@[scoped simp] theorem edge_zero {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (a b : 𝒰.ι) (h : a < b) : (edge 𝒰 a b h).1 0 = a := rfl
@[scoped simp] theorem edge_one {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (a b : 𝒰.ι) (h : a < b) : (edge 𝒰 a b h).1 1 = b := rfl

theorem inter_edge {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (a b : 𝒰.ι) (h : a < b) :
    𝒰.inter (edge 𝒰 a b h) = 𝒰.U a ⊓ 𝒰.U b :=
  le_antisymm (le_inf (𝒰.inter_le _ 0) (𝒰.inter_le _ 1))
    (le_iInf fun j => by fin_cases j <;> simp [edge, inf_le_left, inf_le_right])

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

end OB4aAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary.OB4aAux"

open OB4aAux

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

theorem flat_sections {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [hf : Flat f] {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    Module.Flat R Γ(X, U) := by
  have h := HasRingHomProperty.appLE @Flat f hf ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  have h' : RingHom.Flat ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact h'

theorem fromSpec_comp_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := algebraOfHom f U
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU
    (show U ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

end OB4aGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmallExtension_exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary.OB4aAux"

open OB4aGlue

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

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

    (η : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 1)))
    (hη : letI := algebraOfHom fk Ue
      ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit fk).d (𝒰.comap i₀) 1 (η.1 a ξ) = ω.1 a ξ)
    :
    ∃ (φ' : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
      (hφq' : ∀ (a b : 𝒰.ι) (h : a < b),
        (φ' a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
      (hφg' : ∀ (a b : 𝒰.ι) (h : a < b),
        ∃ (γ₁ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
          (γ₂ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
          γ₁ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
          γ₂ ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
          γ₁ ≫ (φ' a b h).hom = γ₂)
      (hφO' : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
        (φ' a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)
      (ρab' : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
      (ρbc' : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
      (ρac' : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
      (hρab' : ∀ r : 𝒰.Idx 2,
        (ρab' r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
          (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
            (φ' (r.1 0) (r.1 1) (r.2 (by decide))).hom)
      (hρbc' : ∀ r : 𝒰.Idx 2,
        (ρbc' r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
          (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
            (φ' (r.1 1) (r.1 2) (r.2 (by decide))).hom)
      (hρac' : ∀ r : 𝒰.Idx 2,
        (ρac' r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
          (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
            (φ' (r.1 0) (r.1 2) (r.2 (by decide))).hom),
      ∀ r : 𝒰.Idx 2, (ρac' r).hom = (ρab' r).hom ≫ (ρbc' r).hom := by
  classical
  letI instE : Algebra (ResidueField T') Γ(Ak, Ue) := algebraOfHom fk Ue
  have hI2 : RingHom.ker π * RingHom.ker π = ⊥ := le_bot_iff.mp ((Ideal.mul_mono_right hI).trans hsmall.le)

  have haW : ∀ c : 𝒰.ι,
      IsPullback ((i₀ ∣_ 𝒰.U c) ≫ g c) ((i₀ ⁻¹ᵁ 𝒰.U c).ι ≫ fk) (q c) (Spec.map (CommRingCat.ofHom (residue T'))) := by
    intro c
    have h1 : IsPullback (i₀ ∣_ 𝒰.U c) ((i₀ ⁻¹ᵁ 𝒰.U c).ι ≫ fk) ((𝒰.U c).ι ≫ f₀) (Spec.map (CommRingCat.ofHom ρ)) :=
      IsPullback.paste_vert (isPullback_morphismRestrict i₀ (𝒰.U c)) hi₀
    have h2 := IsPullback.paste_horiz h1 (hg c)
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ] at h2

  have σk : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
      { e : (ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)) ≃ₐ[ResidueField T'] Γ(Ak, (𝒰.comap i₀).inter s) //
        (e : _ ≃+* _) = σ s } := fun s => by
    letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
    letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
    exact ⟨AlgEquiv.ofRingEquiv (f := σ s) (fun x => by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        exact hσ₂ s x), rfl⟩

  let ℓf : ∀ (a b : 𝒰.ι) (h : a < b),
      letI := algebraOfHom (q a) (O a (𝒰.U a ⊓ 𝒰.U b))
      (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 1 →ₗ[ResidueField T'] (ResidueField T') ⊗[T'] Γ(Y a, O a (𝒰.U a ⊓ 𝒰.U b)) :=
    fun a b h => by
      letI instab : Algebra T' Γ(Y a, O a (𝒰.U a ⊓ 𝒰.U b)) := algebraOfHom (q a) (O a (𝒰.U a ⊓ 𝒰.U b))
      letI insts : Algebra T' Γ(Y a, O a (𝒰.inter (edge 𝒰 a b h))) := algebraOfHom (q a) (O a (𝒰.inter (edge 𝒰 a b h)))
      letI instk : Algebra (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter (edge 𝒰 a b h)) :=
        algebraOfHom fk ((𝒰.comap i₀).inter (edge 𝒰 a b h))
      exact (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom (q a) (hOm a (inter_edge 𝒰 a b h).ge))).toLinearMap ∘ₗ
        (σk (edge 𝒰 a b h)).1.symm.toLinearMap ∘ₗ LinearMap.proj (edge 𝒰 a b h)
  let δf : ∀ (a b : 𝒰.ι) (h : a < b),
      letI := algebraOfHom (q a) (O a (𝒰.U a ⊓ 𝒰.U b))
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(Y a, O a (𝒰.U a ⊓ 𝒰.U b))))) :=
    fun a b h => by
      letI instab : Algebra T' Γ(Y a, O a (𝒰.U a ⊓ 𝒰.U b)) := algebraOfHom (q a) (O a (𝒰.U a ⊓ 𝒰.U b))
      exact Algebra.PointDerivations.map (k := ResidueField T') (A := Γ(Ak, Ue))
        ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
        (LinearMap.llcomp (ResidueField T') (Module.Dual (ResidueField T') V) _ _ (-(ℓf a b h))) η
  have key : ∀ (a b : 𝒰.ι) (h : a < b),
      letI := algebraOfHom (q a) (O a (𝒰.U a ⊓ 𝒰.U b))
      ∃ (φ' : (↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
      φ'.hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a ∧
      (∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
          (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ φ'.hom = γ') ∧
      (∀ W' : A₀.Opens, φ'.hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W') = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W') ∧
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y a, O a (𝒰.U a ⊓ 𝒰.U b))
        ((hOaff a (𝒰.U a ⊓ 𝒰.U b) (by rw [← inter_edge 𝒰 a b h]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_left).isoSpec.inv ≫
          (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι)
        ((hOaff a (𝒰.U a ⊓ 𝒰.U b) (by rw [← inter_edge 𝒰 a b h]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_left).isoSpec.inv ≫
          φ'.hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι)
        fk Lk (i₀ ⁻¹ᵁ 𝒰.U b) ((i₀ ∣_ 𝒰.U b) ≫ g b) Ue
        (fun x => (δf a b h : Γ(Ak, Ue) →ₗ[ResidueField T']
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(Y a, O a (𝒰.U a ⊓ 𝒰.U b))))) x) := by
    intro a b h
    letI instab : Algebra T' Γ(Y a, O a (𝒰.U a ⊓ 𝒰.U b)) := algebraOfHom (q a) (O a (𝒰.U a ⊓ 𝒰.U b))
    exact AlgebraicGeometry.SmallExtension.exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations T' T π hπ hker hsmall hI
      V ι hι hιI f₀ (𝒰.U a) (𝒰.U b) (q a) (q b) (hq a) (g a) (g b) (hg b) (O a) (O b) (hO b)
      (hOaff a (𝒰.U a ⊓ 𝒰.U b) (by rw [← inter_edge 𝒰 a b h]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_left)
      (hOaff b (𝒰.U a ⊓ 𝒰.U b) (by rw [← inter_edge 𝒰 a b h]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_right)
      fk Lk (i₀ ⁻¹ᵁ 𝒰.U b) ((i₀ ∣_ 𝒰.U b) ≫ g b) (haW b) Ue hUe e₁ he₁ (φ a b h) (hφq a b h) (hφg a b h) (hφO a b h) (δf a b h)
  choose φ' hφ' using key
  refine ⟨φ', fun a b h => (hφ' a b h).1, fun a b h => (hφ' a b h).2.1, fun a b h => (hφ' a b h).2.2.1, ?_⟩

  have hle : ∀ (r : 𝒰.Idx 2) (i j : Fin 3), 𝒰.inter r ≤ 𝒰.U (r.1 i) ⊓ 𝒰.U (r.1 j) := fun r i j =>
    le_inf (𝒰.inter_le r i) (𝒰.inter_le r j)
  have RI := fun (a b : 𝒰.ι) (h : a < b) (r : 𝒰.Idx 2) (hZ : 𝒰.inter r ≤ 𝒰.U a ⊓ 𝒰.U b) =>
    AlgebraicGeometry.Scheme.exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq
      (O a (𝒰.U a ⊓ 𝒰.U b)) (O b (𝒰.U a ⊓ 𝒰.U b)) (φ' a b h) (O a (𝒰.inter r)) (O b (𝒰.inter r))
      (hOm a hZ) (hOm b hZ) ((hφ' a b h).2.2.1 (𝒰.inter r))
  choose ρ' hρ'1 hρ'2 using RI
  refine ⟨fun r => ρ' (r.1 0) (r.1 1) (r.2 (by decide)) r (hle r 0 1),
          fun r => ρ' (r.1 1) (r.1 2) (r.2 (by decide)) r (hle r 1 2),
          fun r => ρ' (r.1 0) (r.1 2) (r.2 (by decide)) r (hle r 0 2),
          fun r => hρ'1 _ _ _ r _, fun r => hρ'1 _ _ _ r _, fun r => hρ'1 _ _ _ r _, ?_⟩

  intro r

  have hab : r.1 0 < r.1 1 := r.2 (by decide)
  have hbc : r.1 1 < r.1 2 := r.2 (by decide)
  have hac : r.1 0 < r.1 2 := r.2 (by decide)
  have hr : IsAffineOpen (𝒰.inter r) := Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r
  let hOr : IsAffineOpen (O (r.1 0) (𝒰.inter r)) := hOaff (r.1 0) (𝒰.inter r) hr (𝒰.inter_le r 0)
  letI instCr : Algebra T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
  letI instCab : Algebra T' Γ(Y (r.1 0), O (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 1))) :=
    algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 1)))
  letI instCac : Algebra T' Γ(Y (r.1 0), O (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 2))) :=
    algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 2)))
  letI instCbc : Algebra T' Γ(Y (r.1 1), O (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2))) :=
    algebraOfHom (q (r.1 1)) (O (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2)))

  let u₀ := hOr.isoSpec.inv ≫ (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι
  let u₁ := hOr.isoSpec.inv ≫ (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι
  let u₂ := hOr.isoSpec.inv ≫ (ρ' (r.1 0) (r.1 1) hab r (hle r 0 1)).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι
  let v₀ := hOr.isoSpec.inv ≫ (ρ' (r.1 0) (r.1 2) hac r (hle r 0 2)).hom ≫ (O (r.1 2) (𝒰.inter r)).ι
  let v₁ := hOr.isoSpec.inv ≫ (ρ' (r.1 0) (r.1 1) hab r (hle r 0 1)).hom ≫ (ρ' (r.1 1) (r.1 2) hbc r (hle r 1 2)).hom ≫
    (O (r.1 2) (𝒰.inter r)).ι

  let resab : Γ(Y (r.1 0), O (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 1))) →ₐ[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) :=
    restrictAlgHom (q (r.1 0)) (hOm (r.1 0) (hle r 0 1))
  let resac : Γ(Y (r.1 0), O (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 2))) →ₐ[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) :=
    restrictAlgHom (q (r.1 0)) (hOm (r.1 0) (hle r 0 2))

  have step : ∀ {a b : 𝒰.ι} {W : A₀.Opens} (hWab : W ≤ 𝒰.U a ⊓ 𝒰.U b)
      (θ : (↑(O a W) : Scheme.{u}) ⟶ ↑(O b W)) (Φ : (↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
      θ ≫ (Y b).homOfLE (hOm b hWab) = (Y a).homOfLE (hOm a hWab) ≫ Φ →
      Φ ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a →
      θ ≫ (O b W).ι ≫ q b = (O a W).ι ≫ q a := by
    intro a b W hWab θ Φ hθ hΦ
    rw [← Scheme.homOfLE_ι (Y b) (hOm b hWab), Category.assoc, reassoc_of% hθ, hΦ, Scheme.homOfLE_ι_assoc]
  have t_ab : (ρab r).hom ≫ (O (r.1 1) (𝒰.inter r)).ι ≫ q (r.1 1) = (O (r.1 0) (𝒰.inter r)).ι ≫ q (r.1 0) :=
    step (hle r 0 1) _ _ (hρab r) (hφq _ _ hab)
  have t_bc : (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι ≫ q (r.1 2) = (O (r.1 1) (𝒰.inter r)).ι ≫ q (r.1 1) :=
    step (hle r 1 2) _ _ (hρbc r) (hφq _ _ hbc)
  have t_ac : (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι ≫ q (r.1 2) = (O (r.1 0) (𝒰.inter r)).ι ≫ q (r.1 0) :=
    step (hle r 0 2) _ _ (hρac r) (hφq _ _ hac)
  have t'_ab : (ρ' (r.1 0) (r.1 1) hab r (hle r 0 1)).hom ≫ (O (r.1 1) (𝒰.inter r)).ι ≫ q (r.1 1) =
      (O (r.1 0) (𝒰.inter r)).ι ≫ q (r.1 0) :=
    step (hle r 0 1) _ _ (hρ'1 (r.1 0) (r.1 1) hab r (hle r 0 1)) (hφ' _ _ hab).1
  have t'_bc : (ρ' (r.1 1) (r.1 2) hbc r (hle r 1 2)).hom ≫ (O (r.1 2) (𝒰.inter r)).ι ≫ q (r.1 2) =
      (O (r.1 1) (𝒰.inter r)).ι ≫ q (r.1 1) :=
    step (hle r 1 2) _ _ (hρ'1 (r.1 1) (r.1 2) hbc r (hle r 1 2)) (hφ' _ _ hbc).1
  have t'_ac : (ρ' (r.1 0) (r.1 2) hac r (hle r 0 2)).hom ≫ (O (r.1 2) (𝒰.inter r)).ι ≫ q (r.1 2) =
      (O (r.1 0) (𝒰.inter r)).ι ≫ q (r.1 0) :=
    step (hle r 0 2) _ _ (hρ'1 (r.1 0) (r.1 2) hac r (hle r 0 2)) (hφ' _ _ hac).1
  have hbase : hOr.isoSpec.inv ≫ (O (r.1 0) (𝒰.inter r)).ι ≫ q (r.1 0) =
      Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))) := by
    rw [IsAffineOpen.isoSpec_inv_ι_assoc, fromSpec_comp_eq]
  haveI := hq (r.1 0)
  haveI : Module.Flat T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) := by
    have h1 : ((q (r.1 0)).appLE ⊤ (O (r.1 0) (𝒰.inter r)) le_top).hom.Flat :=
      HasRingHomProperty.appLE @Flat (q (r.1 0)) inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨O (r.1 0) (𝒰.inter r), hOr⟩ le_top
    have h2 : ((Scheme.ΓSpecIso (CommRingCat.of T')).inv ≫ (q (r.1 0)).appLE ⊤ (O (r.1 0) (𝒰.inter r)) le_top).hom.Flat :=
      RingHom.Flat.comp (.of_bijective (Scheme.ΓSpecIso (CommRingCat.of T')).symm.commRingCatIsoToRingEquiv.bijective) h1
    exact h2

  have H0 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) u₀ v₀ fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue
      (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resac).toLinearMap ∘ₗ
        (δf (r.1 0) (r.1 2) hac : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) := by
    have hv := (hφ' (r.1 0) (r.1 2) hac).2.2.2
    have hR := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat (RingHom.ker π) hI hsmall V ι hι hιI
      ((Y (r.1 0)).presheaf.obj (Opposite.op (O (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 2)))))
      ((Y (r.1 0)).presheaf.obj (Opposite.op (O (r.1 0) (𝒰.inter r)))) resac _ _ fk Lk _ _ Ue _ hv
    have hsp : Spec.map (CommRingCat.ofHom resac.toRingHom) ≫
        (hOaff (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 2)) (by rw [← inter_edge 𝒰 (r.1 0) (r.1 2) hac]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_left).isoSpec.inv =
        hOr.isoSpec.inv ≫ (Y (r.1 0)).homOfLE (hOm (r.1 0) (hle r 0 2)) :=
      spec_map_comp_isoSpec_inv _ hOr _
    have e1 : Spec.map (CommRingCat.ofHom resac.toRingHom) ≫
        ((hOaff (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 2)) (by rw [← inter_edge 𝒰 (r.1 0) (r.1 2) hac]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_left).isoSpec.inv ≫
          (φ (r.1 0) (r.1 2) hac).hom ≫ (O (r.1 2) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 2))).ι) = u₀ := by
      rw [← Category.assoc, hsp, Category.assoc, ← Category.assoc ((Y (r.1 0)).homOfLE _), ← hρac r, Category.assoc,
        Scheme.homOfLE_ι]
    have e2 : Spec.map (CommRingCat.ofHom resac.toRingHom) ≫
        ((hOaff (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 2)) (by rw [← inter_edge 𝒰 (r.1 0) (r.1 2) hac]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_left).isoSpec.inv ≫
          (φ' (r.1 0) (r.1 2) hac).hom ≫ (O (r.1 2) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 2))).ι) = v₀ := by
      rw [← Category.assoc, hsp, Category.assoc, ← Category.assoc ((Y (r.1 0)).homOfLE _), ← hρ'1 (r.1 0) (r.1 2) hac r (hle r 0 2),
        Category.assoc, Scheme.homOfLE_ι]
    rw [e1, e2] at hR
    exact hR

  obtain ⟨hbr, hhbr⟩ : ∃ hbr : Γ(Y (r.1 1), O (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2))) →ₐ[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)),
      Spec.map (CommRingCat.ofHom hbr.toRingHom) ≫
        (hOaff (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2)) (by rw [← inter_edge 𝒰 (r.1 1) (r.1 2) hbc]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_left).isoSpec.inv =
        hOr.isoSpec.inv ≫ (ρ' (r.1 0) (r.1 1) hab r (hle r 0 1)).hom ≫
          (Y (r.1 1)).homOfLE (hOm (r.1 1) (hle r 1 2)) := by
    have hObc : IsAffineOpen (O (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2))) :=
      hOaff (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2)) (by rw [← inter_edge 𝒰 (r.1 1) (r.1 2) hbc]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_left
    let θ : (↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ⟶ ↑(O (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2))) :=
      (ρ' (r.1 0) (r.1 1) hab r (hle r 0 1)).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (hle r 1 2))
    have hθ : θ ≫ (O (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2))).ι ≫ q (r.1 1) = (O (r.1 0) (𝒰.inter r)).ι ≫ q (r.1 0) := by
      simp only [θ, Category.assoc, Scheme.homOfLE_ι_assoc, t'_ab]
    have key : CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 1), O (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2)))) ≫ rmap _ _ θ =
        CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))) := by
      apply Spec.map_injective
      rw [Spec.map_comp, ← fromSpec_comp_eq (q (r.1 1)) hObc, ← fromSpec_comp_eq (q (r.1 0)) hOr,
        ← IsAffineOpen.isoSpec_inv_ι, ← IsAffineOpen.isoSpec_inv_ι]
      simp only [Category.assoc]
      rw [specMap_rmap_isoSpec_inv_assoc hOr hObc θ, hθ]
    refine ⟨{ (rmap _ _ θ).hom with commutes' := fun t => congrArg (fun φ : CommRingCat.of T' ⟶ _ => φ.hom t) key }, ?_⟩
    exact specMap_rmap_isoSpec_inv hOr hObc θ

  have H1 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) u₁ u₂ fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue
      (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resab).toLinearMap ∘ₗ
        (δf (r.1 0) (r.1 1) hab : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) := by
    have hOab : IsAffineOpen (O (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 1))) :=
      hOaff (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 1)) (by rw [← inter_edge 𝒰 (r.1 0) (r.1 1) hab]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_left
    have hv := (hφ' (r.1 0) (r.1 1) hab).2.2.2

    have V1 := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat (RingHom.ker π) hI hsmall V ι hι hιI
      ((Y (r.1 0)).presheaf.obj (Opposite.op (O (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 1)))))
      ((Y (r.1 0)).presheaf.obj (Opposite.op (O (r.1 0) (𝒰.inter r)))) resab _ _ fk Lk _ _ Ue _ hv
    have hsp : Spec.map (CommRingCat.ofHom resab.toRingHom) ≫ hOab.isoSpec.inv =
        hOr.isoSpec.inv ≫ (Y (r.1 0)).homOfLE (hOm (r.1 0) (hle r 0 1)) :=
      spec_map_comp_isoSpec_inv _ hOr _
    have e1 : Spec.map (CommRingCat.ofHom resab.toRingHom) ≫
        (hOab.isoSpec.inv ≫ (φ (r.1 0) (r.1 1) hab).hom ≫ (O (r.1 1) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 1))).ι) =
        (hOr.isoSpec.inv ≫ (ρab r).hom) ≫ (O (r.1 1) (𝒰.inter r)).ι := by
      rw [← Category.assoc, hsp, Category.assoc, ← Category.assoc ((Y (r.1 0)).homOfLE _), ← hρab r, Category.assoc,
        Scheme.homOfLE_ι, Category.assoc]
    have e2 : Spec.map (CommRingCat.ofHom resab.toRingHom) ≫
        (hOab.isoSpec.inv ≫ (φ' (r.1 0) (r.1 1) hab).hom ≫ (O (r.1 1) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 1))).ι) =
        (hOr.isoSpec.inv ≫ (ρ' (r.1 0) (r.1 1) hab r (hle r 0 1)).hom) ≫ (O (r.1 1) (𝒰.inter r)).ι := by
      rw [← Category.assoc, hsp, Category.assoc, ← Category.assoc ((Y (r.1 0)).homOfLE _),
        ← hρ'1 (r.1 0) (r.1 1) hab r (hle r 0 1), Category.assoc, Scheme.homOfLE_ι, Category.assoc]
    rw [e1, e2] at V1

    obtain ⟨aW₀, haW₀, hsq⟩ := AlgebraicGeometry.exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift
      (𝒰.U (r.1 1)) (g (r.1 1)) (O (r.1 1)) (hO (r.1 1)) i₀ (𝒰.inter r) (𝒰.inter_le r 1)
    have V2 := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_of_isPullback_of_comp_mono (RingHom.ker π) hI hsmall
      V ι ((Y (r.1 0)).presheaf.obj (Opposite.op (O (r.1 0) (𝒰.inter r)))) (O (r.1 1) (𝒰.inter r)).ι _ _ fk Lk
      _ _ (i₀.preimage_mono (𝒰.inter_le r 1)) _ aW₀ hsq Ue _ V1

    obtain ⟨γ, γ', hγ, hγ', hγφ⟩ := hφg (r.1 1) (r.1 2) hbc
    have resnat : ∀ {W W' : A₀.Opens} (h : W ≤ W'),
        Ak.homOfLE (i₀.preimage_mono h) ≫ (i₀ ∣_ W') = (i₀ ∣_ W) ≫ A₀.homOfLE h := by
      intro W W' h
      rw [← cancel_mono W'.ι]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]
    have clA : aW₀ ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (hle r 1 2)) =
        ((i₀ ∣_ 𝒰.inter r) ≫ A₀.homOfLE (hle r 1 2)) ≫ γ := by
      rw [← cancel_mono (O (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2))).ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, hγ, Scheme.homOfLE_homOfLE_assoc]
      rw [haW₀, reassoc_of% (resnat (𝒰.inter_le r 1))]
    have haWc : Ak.homOfLE (i₀.preimage_mono (𝒰.inter_le r 2)) ≫ ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) =
        aW₀ ≫ ((ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) := by
      rw [reassoc_of% (resnat (𝒰.inter_le r 2)),
        ← Scheme.homOfLE_ι (Y (r.1 2)) (hOm (r.1 2) (hle r 1 2)), reassoc_of% (hρbc r), reassoc_of% clA]
      try simp only [Category.assoc]
      rw [reassoc_of% hγφ, hγ', Scheme.homOfLE_homOfLE_assoc]
    have V3 := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq (RingHom.ker π) V ι
      ((Y (r.1 0)).presheaf.obj (Opposite.op (O (r.1 0) (𝒰.inter r)))) ((ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) _ _ fk Lk
      _ _ (i₀.preimage_mono (𝒰.inter_le r 2)) aW₀ _ haWc Ue _ V2
    simp only [u₁, u₂]
    simpa only [Category.assoc] using V3

  have H2 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) u₂ v₁ fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue
      (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hbr).toLinearMap ∘ₗ
        (δf (r.1 1) (r.1 2) hbc : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) := by
    have hv := (hφ' (r.1 1) (r.1 2) hbc).2.2.2
    have hR := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat (RingHom.ker π) hI hsmall V ι hι hιI
      ((Y (r.1 1)).presheaf.obj (Opposite.op (O (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2)))))
      ((Y (r.1 0)).presheaf.obj (Opposite.op (O (r.1 0) (𝒰.inter r)))) hbr _ _ fk Lk _ _ Ue _ hv
    have e1 : Spec.map (CommRingCat.ofHom hbr.toRingHom) ≫
        ((hOaff (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2)) (by rw [← inter_edge 𝒰 (r.1 1) (r.1 2) hbc]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_left).isoSpec.inv ≫
          (φ (r.1 1) (r.1 2) hbc).hom ≫ (O (r.1 2) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2))).ι) = u₂ := by
      rw [← Category.assoc, hhbr, Category.assoc, Category.assoc, ← Category.assoc ((Y (r.1 1)).homOfLE _), ← hρbc r,
        Category.assoc, Scheme.homOfLE_ι]
    have e2 : Spec.map (CommRingCat.ofHom hbr.toRingHom) ≫
        ((hOaff (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2)) (by rw [← inter_edge 𝒰 (r.1 1) (r.1 2) hbc]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_left).isoSpec.inv ≫
          (φ' (r.1 1) (r.1 2) hbc).hom ≫ (O (r.1 2) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2))).ι) = v₁ := by
      rw [← Category.assoc, hhbr, Category.assoc, Category.assoc, ← Category.assoc ((Y (r.1 1)).homOfLE _),
        ← hρ'1 (r.1 1) (r.1 2) hbc r (hle r 1 2), Category.assoc, Scheme.homOfLE_ι]
    rw [e1, e2] at hR
    exact hR

  obtain ⟨cs, Hcs, hcsω⟩ := hω r

  have hT₀ : u₀ ≫ q (r.1 2) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))) := by
    simp only [u₀, Category.assoc]; rw [t_ac, hbase]
  have hT₁ : u₁ ≫ q (r.1 2) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))) := by
    simp only [u₁, Category.assoc]; rw [t_bc, t_ab, hbase]
  have hT₂ : u₂ ≫ q (r.1 2) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))) := by
    simp only [u₂, Category.assoc]; rw [t_bc, t'_ab, hbase]
  have hT₃ : v₀ ≫ q (r.1 2) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))) := by
    simp only [v₀, Category.assoc]; rw [t'_ac, hbase]
  have hT₄ : v₁ ≫ q (r.1 2) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))) := by
    simp only [v₁, Category.assoc]; rw [t'_bc, t'_ab, hbase]

  have hcong : ∀ (w w' : Spec Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) ⟶ Y (r.1 2))
      (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))))),
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) w w' fk Lk
        (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue c →
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))) ≫ w =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))) ≫ w' :=
    fun w w' c hc => specMap_mk_comp_eq_of_isTangentCoordsOfPairAtVia (RingHom.ker π) V ι _ w w' fk Lk _ _ Ue c hc

  have H6 : (fun x => cs x +
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resab).toLinearMap ∘ₗ
          (δf (r.1 0) (r.1 1) hab : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x +
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hbr).toLinearMap ∘ₗ
          (δf (r.1 1) (r.1 2) hbc : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) =
      (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resac).toLinearMap ∘ₗ
        (δf (r.1 0) (r.1 2) hac : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) := by
    letI instk_r : Algebra (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter r) := algebraOfHom fk ((𝒰.comap i₀).inter r)

    have hrs : ∀ s : 𝒰.Idx 1, (∀ j : Fin 2, ∃ i : Fin 3, s.1 j = r.1 i) → (𝒰.comap i₀).inter r ≤ (𝒰.comap i₀).inter s := by
      intro s hs
      refine le_iInf fun j => ?_
      obtain ⟨i, hi⟩ := hs j
      rw [hi]
      exact (𝒰.comap i₀).inter_le r i
    have hs_ab : ∀ j : Fin 2, ∃ i : Fin 3, (edge 𝒰 (r.1 0) (r.1 1) hab).1 j = r.1 i := by
      intro j; fin_cases j; exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
    have hs_bc : ∀ j : Fin 2, ∃ i : Fin 3, (edge 𝒰 (r.1 1) (r.1 2) hbc).1 j = r.1 i := by
      intro j; fin_cases j; exacts [⟨1, rfl⟩, ⟨2, rfl⟩]
    have hs_ac : ∀ j : Fin 2, ∃ i : Fin 3, (edge 𝒰 (r.1 0) (r.1 2) hac).1 j = r.1 i := by
      intro j; fin_cases j; exacts [⟨0, rfl⟩, ⟨2, rfl⟩]
    let Res : ∀ (s : 𝒰.Idx 1), (∀ j : Fin 2, ∃ i : Fin 3, s.1 j = r.1 i) → (Γ(Ak, (𝒰.comap i₀).inter s) → Γ(Ak, (𝒰.comap i₀).inter r)) :=
      fun s hs => (Ak.presheaf.map (homOfLE (hrs s hs)).op).hom

    have S1 : ∀ (x : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        σ r (((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resab).toLinearMap ∘ₗ
          (δf (r.1 0) (r.1 1) hab : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) ξ) =
        - Res _ hs_ab (η.1 x ξ (edge 𝒰 (r.1 0) (r.1 1) hab)) := by
      intro x ξ

      have hrs' : 𝒰.inter r ≤ 𝒰.inter (edge 𝒰 (r.1 0) (r.1 1) hab) := by
        refine le_iInf fun j => ?_
        obtain ⟨i, hi⟩ := hs_ab j
        rw [hi]; exact 𝒰.inter_le r i
      letI insts : Algebra T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 1) hab))) :=
        algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 1) hab)))
      letI instks : Algebra (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter (edge 𝒰 (r.1 0) (r.1 1) hab)) :=
        algebraOfHom fk ((𝒰.comap i₀).inter (edge 𝒰 (r.1 0) (r.1 1) hab))
      let ressr : Γ(Y (r.1 0), O (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 1) hab))) →ₐ[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) :=
        restrictAlgHom (q (r.1 0)) (hOm (r.1 0) hrs')

      have hδ : ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resab).toLinearMap ∘ₗ
          (δf (r.1 0) (r.1 1) hab : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) ξ =
          - Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) ressr
              ((σk (edge 𝒰 (r.1 0) (r.1 1) hab)).1.symm (η.1 x ξ (edge 𝒰 (r.1 0) (r.1 1) hab))) := by
        change Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resab
          (-(Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
              (restrictAlgHom (q (r.1 0)) (hOm (r.1 0) (inter_edge 𝒰 (r.1 0) (r.1 1) hab).ge))
            ((σk (edge 𝒰 (r.1 0) (r.1 1) hab)).1.symm (η.1 x ξ (edge 𝒰 (r.1 0) (r.1 1) hab))))) = _
        rw [map_neg, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
        have hce : ∀ (W₁ W₂ W₃ : (Y (r.1 0)).Opens) (h₁₂ : W₁ ≤ W₂) (h₂₃ : W₂ ≤ W₃) (h₁₃ : W₁ ≤ W₃),
            letI := algebraOfHom (q (r.1 0)) W₁; letI := algebraOfHom (q (r.1 0)) W₂; letI := algebraOfHom (q (r.1 0)) W₃
            (restrictAlgHom (q (r.1 0)) h₁₂).comp (restrictAlgHom (q (r.1 0)) h₂₃) = restrictAlgHom (q (r.1 0)) h₁₃ := by
          intro W₁ W₂ W₃ h₁₂ h₂₃ h₁₃
          letI := algebraOfHom (q (r.1 0)) W₁; letI := algebraOfHom (q (r.1 0)) W₂; letI := algebraOfHom (q (r.1 0)) W₃
          apply AlgHom.ext
          intro z
          change ((Y (r.1 0)).presheaf.map (homOfLE h₂₃).op ≫ (Y (r.1 0)).presheaf.map (homOfLE h₁₂).op).hom z =
            ((Y (r.1 0)).presheaf.map (homOfLE h₁₃).op).hom z
          rw [← Functor.map_comp]
          rfl
        rw [hce]
      rw [hδ, map_neg]
      congr 1

      have hsU0 : 𝒰.inter (edge 𝒰 (r.1 0) (r.1 1) hab) ≤ 𝒰.U (r.1 0) := 𝒰.inter_le (edge 𝒰 (r.1 0) (r.1 1) hab) 0
      have hpin : (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) (edge 𝒰 (r.1 0) (r.1 1) hab)).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σ (edge 𝒰 (r.1 0) (r.1 1) hab)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y (r.1 0), O (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 1) hab))) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 1) hab)))).toRingHom) ≫
          (hOaff (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 1) hab)) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) hsU0).fromSpec =
          Ak.homOfLE (𝒰.comap_inter_le i₀ (edge 𝒰 (r.1 0) (r.1 1) hab)) ≫ (i₀ ∣_ 𝒰.inter (edge 𝒰 (r.1 0) (r.1 1) hab)) ≫
            A₀.homOfLE hsU0 ≫ g (r.1 0) :=
        hσ₁ (edge 𝒰 (r.1 0) (r.1 1) hab)

      have hST := AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
        (q (r.1 0)) (q (r.1 0)) fk (O (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 1) hab)))
        (hOaff (r.1 0) _ (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) hsU0)
        (O (r.1 0) (𝒰.inter r)) hOr
        ((𝒰.comap i₀).inter (edge 𝒰 (r.1 0) (r.1 1) hab)) ((𝒰.comap i₀).inter r)
        (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) _) (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) r)
        (hrs _ hs_ab)
        (Ak.homOfLE (𝒰.comap_inter_le i₀ (edge 𝒰 (r.1 0) (r.1 1) hab)) ≫ (i₀ ∣_ 𝒰.inter (edge 𝒰 (r.1 0) (r.1 1) hab)) ≫
          A₀.homOfLE (hsU0 : 𝒰.inter (edge 𝒰 (r.1 0) (r.1 1) hab) ≤ 𝒰.U (r.1 0)) ≫ g (r.1 0))
        ressr (σ (edge 𝒰 (r.1 0) (r.1 1) hab)) (σ r) hpin (hσ₂ _) (hσ₂ r) ?_
        ((σk (edge 𝒰 (r.1 0) (r.1 1) hab)).1.symm (η.1 x ξ (edge 𝒰 (r.1 0) (r.1 1) hab)))
      · rw [hST]
        have happ : ∀ y, σ (edge 𝒰 (r.1 0) (r.1 1) hab) ((σk (edge 𝒰 (r.1 0) (r.1 1) hab)).1.symm y) = y := fun y => by
          have h3 : (σk (edge 𝒰 (r.1 0) (r.1 1) hab)).1.symm y = (σ (edge 𝒰 (r.1 0) (r.1 1) hab)).symm y :=
            congrArg (fun e : _ ≃+* _ => e.symm y) (σk (edge 𝒰 (r.1 0) (r.1 1) hab)).2
          rw [h3]
          exact (σ (edge 𝒰 (r.1 0) (r.1 1) hab)).apply_symm_apply y
        show (Ak.presheaf.map _).hom _ = (Ak.presheaf.map _).hom _
        congr 1
        exact happ _
      ·
        rw [show Spec.map (CommRingCat.ofHom ressr.toRingHom) = Spec.map ((Y (r.1 0)).presheaf.map (homOfLE (hOm (r.1 0) hrs')).op) from rfl,
          IsAffineOpen.map_fromSpec _ hOr, hσ₁ r]
        simp only [← Category.assoc]
        congr 1
        rw [← cancel_mono (𝒰.U (r.1 0)).ι]
        simp only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc]
    have S2 : ∀ (x : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        σ r (((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hbr).toLinearMap ∘ₗ
          (δf (r.1 1) (r.1 2) hbc : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) ξ) =
        - Res _ hs_bc (η.1 x ξ (edge 𝒰 (r.1 1) (r.1 2) hbc)) := by
      intro x ξ
      have hrs' : 𝒰.inter r ≤ 𝒰.inter (edge 𝒰 (r.1 1) (r.1 2) hbc) := by
        refine le_iInf fun j => ?_
        obtain ⟨i, hi⟩ := hs_bc j
        rw [hi]; exact 𝒰.inter_le r i
      have hObc : IsAffineOpen (O (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2))) :=
        hOaff (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2)) (by rw [← inter_edge 𝒰 (r.1 1) (r.1 2) hbc]; exact Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) inf_le_left
      letI insts : Algebra T' Γ(Y (r.1 1), O (r.1 1) (𝒰.inter (edge 𝒰 (r.1 1) (r.1 2) hbc))) :=
        algebraOfHom (q (r.1 1)) (O (r.1 1) (𝒰.inter (edge 𝒰 (r.1 1) (r.1 2) hbc)))
      letI instks : Algebra (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter (edge 𝒰 (r.1 1) (r.1 2) hbc)) :=
        algebraOfHom fk ((𝒰.comap i₀).inter (edge 𝒰 (r.1 1) (r.1 2) hbc))

      let res' : Γ(Y (r.1 1), O (r.1 1) (𝒰.inter (edge 𝒰 (r.1 1) (r.1 2) hbc))) →ₐ[T']
          Γ(Y (r.1 1), O (r.1 1) (𝒰.U (r.1 1) ⊓ 𝒰.U (r.1 2))) :=
        restrictAlgHom (q (r.1 1)) (hOm (r.1 1) (inter_edge 𝒰 (r.1 1) (r.1 2) hbc).ge)
      let hres : Γ(Y (r.1 1), O (r.1 1) (𝒰.inter (edge 𝒰 (r.1 1) (r.1 2) hbc))) →ₐ[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) :=
        hbr.comp res'

      have hδ : ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hbr).toLinearMap ∘ₗ
          (δf (r.1 1) (r.1 2) hbc : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) ξ =
          - Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hres
              ((σk (edge 𝒰 (r.1 1) (r.1 2) hbc)).1.symm (η.1 x ξ (edge 𝒰 (r.1 1) (r.1 2) hbc))) := by
        change Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) hbr
          (-(Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) res'
            ((σk (edge 𝒰 (r.1 1) (r.1 2) hbc)).1.symm (η.1 x ξ (edge 𝒰 (r.1 1) (r.1 2) hbc))))) = _
        rw [map_neg, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
      rw [hδ, map_neg]
      congr 1

      obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hγφ'⟩ := (hφ' (r.1 0) (r.1 1) hab).2.1
      have resnat : ∀ {W W' : A₀.Opens} (h : W ≤ W'),
          Ak.homOfLE (i₀.preimage_mono h) ≫ (i₀ ∣_ W') = (i₀ ∣_ W) ≫ A₀.homOfLE h := by
        intro W W' h
        rw [← cancel_mono W'.ι]
        simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]
      have claimP : ((Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) r).isoSpec.hom ≫
            Spec.map (CommRingCat.ofHom (σ r).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
              Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))).toRingHom) ≫
            hOr.isoSpec.inv) ≫ (Y (r.1 0)).homOfLE (hOm (r.1 0) (hle r 0 1)) =
          (Ak.homOfLE (𝒰.comap_inter_le i₀ r) ≫ (i₀ ∣_ 𝒰.inter r) ≫ A₀.homOfLE (hle r 0 1)) ≫ γ₁ := by
        rw [← cancel_mono (O (r.1 0) (𝒰.U (r.1 0) ⊓ 𝒰.U (r.1 1))).ι]
        simp only [Category.assoc, Scheme.homOfLE_ι, hγ₁, Scheme.homOfLE_homOfLE_assoc, IsAffineOpen.isoSpec_inv_ι]
        rw [hσ₁ r]

      have hST := AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
        (q (r.1 1)) (q (r.1 0)) fk (O (r.1 1) (𝒰.inter (edge 𝒰 (r.1 1) (r.1 2) hbc)))
        (hOaff (r.1 1) _ (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) (𝒰.inter_le _ 0))
        (O (r.1 0) (𝒰.inter r)) hOr
        ((𝒰.comap i₀).inter (edge 𝒰 (r.1 1) (r.1 2) hbc)) ((𝒰.comap i₀).inter r)
        (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) _) (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) r)
        (hrs _ hs_bc)
        (Ak.homOfLE (𝒰.comap_inter_le i₀ _) ≫ (i₀ ∣_ 𝒰.inter (edge 𝒰 (r.1 1) (r.1 2) hbc)) ≫ A₀.homOfLE (𝒰.inter_le _ 0) ≫ g (r.1 1))
        hres (σ (edge 𝒰 (r.1 1) (r.1 2) hbc)) (σ r) (hσ₁ _) (hσ₂ _) (hσ₂ r) ?_
        ((σk (edge 𝒰 (r.1 1) (r.1 2) hbc)).1.symm (η.1 x ξ (edge 𝒰 (r.1 1) (r.1 2) hbc)))
      · rw [hST]
        have happ : ∀ y, σ (edge 𝒰 (r.1 1) (r.1 2) hbc) ((σk (edge 𝒰 (r.1 1) (r.1 2) hbc)).1.symm y) = y := fun y => by
          have h3 : (σk (edge 𝒰 (r.1 1) (r.1 2) hbc)).1.symm y = (σ (edge 𝒰 (r.1 1) (r.1 2) hbc)).symm y :=
            congrArg (fun e : _ ≃+* _ => e.symm y) (σk (edge 𝒰 (r.1 1) (r.1 2) hbc)).2
          rw [h3]
          exact (σ (edge 𝒰 (r.1 1) (r.1 2) hbc)).apply_symm_apply y
        show (Ak.presheaf.map _).hom _ = (Ak.presheaf.map _).hom _
        congr 1
        exact happ _
      ·
        rw [show CommRingCat.ofHom hres.toRingHom =
            (Y (r.1 1)).presheaf.map (homOfLE (hOm (r.1 1) (inter_edge 𝒰 (r.1 1) (r.1 2) hbc).ge)).op ≫
              CommRingCat.ofHom hbr.toRingHom from rfl, Spec.map_comp]
        simp only [Category.assoc]
        rw [IsAffineOpen.map_fromSpec _ hObc, ← IsAffineOpen.isoSpec_inv_ι, reassoc_of% hhbr, Scheme.homOfLE_ι,
          ← Scheme.homOfLE_ι (Y (r.1 1)) (hOm (r.1 1) (hle r 0 1)),
          reassoc_of% (hρ'1 (r.1 0) (r.1 1) hab r (hle r 0 1))]

        have claimP' := reassoc_of% claimP
        rw [claimP', reassoc_of% hγφ', hγ₂, Scheme.homOfLE_homOfLE_assoc,
          ← reassoc_of% (resnat (𝒰.inter_le r 1)), Scheme.homOfLE_homOfLE_assoc,
          ← reassoc_of% (resnat (𝒰.inter_le (edge 𝒰 (r.1 1) (r.1 2) hbc) 0)),
          Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_homOfLE_assoc]
        rfl
    have S3 : ∀ (x : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        σ r (((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resac).toLinearMap ∘ₗ
          (δf (r.1 0) (r.1 2) hac : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) ξ) =
        - Res _ hs_ac (η.1 x ξ (edge 𝒰 (r.1 0) (r.1 2) hac)) := by
      intro x ξ

      have hrs' : 𝒰.inter r ≤ 𝒰.inter (edge 𝒰 (r.1 0) (r.1 2) hac) := by
        refine le_iInf fun j => ?_
        obtain ⟨i, hi⟩ := hs_ac j
        rw [hi]; exact 𝒰.inter_le r i
      letI insts : Algebra T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 2) hac))) :=
        algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 2) hac)))
      letI instks : Algebra (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter (edge 𝒰 (r.1 0) (r.1 2) hac)) :=
        algebraOfHom fk ((𝒰.comap i₀).inter (edge 𝒰 (r.1 0) (r.1 2) hac))
      let ressr : Γ(Y (r.1 0), O (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 2) hac))) →ₐ[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) :=
        restrictAlgHom (q (r.1 0)) (hOm (r.1 0) hrs')

      have hδ : ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resac).toLinearMap ∘ₗ
          (δf (r.1 0) (r.1 2) hac : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) ξ =
          - Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) ressr
              ((σk (edge 𝒰 (r.1 0) (r.1 2) hac)).1.symm (η.1 x ξ (edge 𝒰 (r.1 0) (r.1 2) hac))) := by
        change Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resac
          (-(Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
              (restrictAlgHom (q (r.1 0)) (hOm (r.1 0) (inter_edge 𝒰 (r.1 0) (r.1 2) hac).ge))
            ((σk (edge 𝒰 (r.1 0) (r.1 2) hac)).1.symm (η.1 x ξ (edge 𝒰 (r.1 0) (r.1 2) hac))))) = _
        rw [map_neg, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
        have hce : ∀ (W₁ W₂ W₃ : (Y (r.1 0)).Opens) (h₁₂ : W₁ ≤ W₂) (h₂₃ : W₂ ≤ W₃) (h₁₃ : W₁ ≤ W₃),
            letI := algebraOfHom (q (r.1 0)) W₁; letI := algebraOfHom (q (r.1 0)) W₂; letI := algebraOfHom (q (r.1 0)) W₃
            (restrictAlgHom (q (r.1 0)) h₁₂).comp (restrictAlgHom (q (r.1 0)) h₂₃) = restrictAlgHom (q (r.1 0)) h₁₃ := by
          intro W₁ W₂ W₃ h₁₂ h₂₃ h₁₃
          letI := algebraOfHom (q (r.1 0)) W₁; letI := algebraOfHom (q (r.1 0)) W₂; letI := algebraOfHom (q (r.1 0)) W₃
          apply AlgHom.ext
          intro z
          change ((Y (r.1 0)).presheaf.map (homOfLE h₂₃).op ≫ (Y (r.1 0)).presheaf.map (homOfLE h₁₂).op).hom z =
            ((Y (r.1 0)).presheaf.map (homOfLE h₁₃).op).hom z
          rw [← Functor.map_comp]
          rfl
        rw [hce]
      rw [hδ, map_neg]
      congr 1

      have hsU0 : 𝒰.inter (edge 𝒰 (r.1 0) (r.1 2) hac) ≤ 𝒰.U (r.1 0) := 𝒰.inter_le (edge 𝒰 (r.1 0) (r.1 2) hac) 0
      have hpin : (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) (edge 𝒰 (r.1 0) (r.1 2) hac)).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σ (edge 𝒰 (r.1 0) (r.1 2) hac)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y (r.1 0), O (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 2) hac))) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 2) hac)))).toRingHom) ≫
          (hOaff (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 2) hac)) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) hsU0).fromSpec =
          Ak.homOfLE (𝒰.comap_inter_le i₀ (edge 𝒰 (r.1 0) (r.1 2) hac)) ≫ (i₀ ∣_ 𝒰.inter (edge 𝒰 (r.1 0) (r.1 2) hac)) ≫
            A₀.homOfLE hsU0 ≫ g (r.1 0) :=
        hσ₁ (edge 𝒰 (r.1 0) (r.1 2) hac)

      have hST := AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
        (q (r.1 0)) (q (r.1 0)) fk (O (r.1 0) (𝒰.inter (edge 𝒰 (r.1 0) (r.1 2) hac)))
        (hOaff (r.1 0) _ (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 _) hsU0)
        (O (r.1 0) (𝒰.inter r)) hOr
        ((𝒰.comap i₀).inter (edge 𝒰 (r.1 0) (r.1 2) hac)) ((𝒰.comap i₀).inter r)
        (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) _) (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) r)
        (hrs _ hs_ac)
        (Ak.homOfLE (𝒰.comap_inter_le i₀ (edge 𝒰 (r.1 0) (r.1 2) hac)) ≫ (i₀ ∣_ 𝒰.inter (edge 𝒰 (r.1 0) (r.1 2) hac)) ≫
          A₀.homOfLE (hsU0 : 𝒰.inter (edge 𝒰 (r.1 0) (r.1 2) hac) ≤ 𝒰.U (r.1 0)) ≫ g (r.1 0))
        ressr (σ (edge 𝒰 (r.1 0) (r.1 2) hac)) (σ r) hpin (hσ₂ _) (hσ₂ r) ?_
        ((σk (edge 𝒰 (r.1 0) (r.1 2) hac)).1.symm (η.1 x ξ (edge 𝒰 (r.1 0) (r.1 2) hac)))
      · rw [hST]
        have happ : ∀ y, σ (edge 𝒰 (r.1 0) (r.1 2) hac) ((σk (edge 𝒰 (r.1 0) (r.1 2) hac)).1.symm y) = y := fun y => by
          have h3 : (σk (edge 𝒰 (r.1 0) (r.1 2) hac)).1.symm y = (σ (edge 𝒰 (r.1 0) (r.1 2) hac)).symm y :=
            congrArg (fun e : _ ≃+* _ => e.symm y) (σk (edge 𝒰 (r.1 0) (r.1 2) hac)).2
          rw [h3]
          exact (σ (edge 𝒰 (r.1 0) (r.1 2) hac)).apply_symm_apply y
        show (Ak.presheaf.map _).hom _ = (Ak.presheaf.map _).hom _
        congr 1
        exact happ _
      ·
        rw [show Spec.map (CommRingCat.ofHom ressr.toRingHom) = Spec.map ((Y (r.1 0)).presheaf.map (homOfLE (hOm (r.1 0) hrs')).op) from rfl,
          IsAffineOpen.map_fromSpec _ hOr, hσ₁ r]
        simp only [← Category.assoc]
        congr 1
        rw [← cancel_mono (𝒰.U (r.1 0)).ι]
        simp only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc]

    have S4 : ∀ (x : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        σ r (cs x ξ) = Res _ hs_bc (η.1 x ξ (edge 𝒰 (r.1 1) (r.1 2) hbc)) - Res _ hs_ac (η.1 x ξ (edge 𝒰 (r.1 0) (r.1 2) hac))
          + Res _ hs_ab (η.1 x ξ (edge 𝒰 (r.1 0) (r.1 1) hab)) := by
      intro x ξ

      have hres : ∀ (j : Fin 3) (s : 𝒰.Idx 1) (hs : ∀ j : Fin 2, ∃ i : Fin 3, s.1 j = r.1 i), (𝒰.comap i₀).face r j = s →
          (OModulePresheaf.unit fk).res ((𝒰.comap i₀).inter_le_inter_face r j) (η.1 x ξ ((𝒰.comap i₀).face r j)) =
            Res s hs (η.1 x ξ s) := by
        rintro j s hs rfl
        rfl
      have hf0 : (𝒰.comap i₀).face r 0 = edge 𝒰 (r.1 1) (r.1 2) hbc := Subtype.ext (funext fun j => by fin_cases j <;> rfl)
      have hf1 : (𝒰.comap i₀).face r 1 = edge 𝒰 (r.1 0) (r.1 2) hac := Subtype.ext (funext fun j => by fin_cases j <;> rfl)
      have hf2 : (𝒰.comap i₀).face r 2 = edge 𝒰 (r.1 0) (r.1 1) hab := Subtype.ext (funext fun j => by fin_cases j <;> rfl)
      rw [hcsω x ξ, ← hη x ξ, OModulePresheaf.d_apply, Fin.sum_univ_three, hres 0 _ hs_bc hf0, hres 1 _ hs_ac hf1, hres 2 _ hs_ab hf2]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_one_smul, neg_one_sq]
      abel

    funext x
    apply LinearMap.ext
    intro ξ
    apply (σ r).injective
    rw [S3]
    simp only [LinearMap.add_apply, map_add]
    rw [S4, S1, S2]
    abel

  have H5 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) u₀ v₁ fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue
      (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resac).toLinearMap ∘ₗ
        (δf (r.1 0) (r.1 2) hac : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) := by
    have hc01 := hcong _ _ _ Hcs
    have hc12 := hcong _ _ _ H1
    have hc23 := hcong _ _ _ H2
    obtain ⟨c₀₂, h₀₂⟩ := AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia (RingHom.ker π) hI hsmall V ι hι hιI
      (((Y (r.1 0)).presheaf.obj (Opposite.op (O (r.1 0) (𝒰.inter r))))) (q (r.1 2)) u₀ hT₀ fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) (haW (r.1 2)) Ue hUe e₁ he₁ u₂ hT₂ (hc01.trans hc12)
    have hadd₁ := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_add (RingHom.ker π) hI hsmall V ι hι hιI
      (((Y (r.1 0)).presheaf.obj (Opposite.op (O (r.1 0) (𝒰.inter r))))) (q (r.1 2)) u₀ u₁ u₂ hT₀ hT₁ hT₂ hc01 hc12 fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) (haW (r.1 2)) Ue hUe e₁ he₁ _ _ _ Hcs H1 h₀₂
    obtain ⟨c₀₃, h₀₃⟩ := AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia (RingHom.ker π) hI hsmall V ι hι hιI
      (((Y (r.1 0)).presheaf.obj (Opposite.op (O (r.1 0) (𝒰.inter r))))) (q (r.1 2)) u₀ hT₀ fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) (haW (r.1 2)) Ue hUe e₁ he₁ v₁ hT₄ ((hc01.trans hc12).trans hc23)
    have hadd₂ := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_add (RingHom.ker π) hI hsmall V ι hι hιI
      (((Y (r.1 0)).presheaf.obj (Opposite.op (O (r.1 0) (𝒰.inter r))))) (q (r.1 2)) u₀ u₂ v₁ hT₀ hT₂ hT₄ (hc01.trans hc12) hc23 fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) (haW (r.1 2)) Ue hUe e₁ he₁ _ _ _ h₀₂ H2 h₀₃
    rw [hadd₁] at hadd₂
    have hc : c₀₃ = (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) resac).toLinearMap ∘ₗ
        (δf (r.1 0) (r.1 2) hac : Γ(Ak, Ue) →ₗ[ResidueField T'] _) x) := by
      rw [hadd₂, ← H6]
      funext x
      simp only [Pi.add_apply]
    rw [hc] at h₀₃
    exact h₀₃

  have H7 : v₀ = v₁ :=
    AlgebraicGeometry.SmallExtension.eq_of_isTangentCoordsOfPairAtVia_of_isTangentCoordsOfPairAtVia (RingHom.ker π) hI hsmall
      V ι hι hιI (((Y (r.1 0)).presheaf.obj (Opposite.op (O (r.1 0) (𝒰.inter r))))) (q (r.1 2)) u₀ hT₀ fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) (haW (r.1 2)) Ue hUe e₁ he₁ v₀ v₁ hT₃ hT₄
      (hcong _ _ _ H0) (hcong _ _ _ H5) _ H0 H5

  have := H7
  simp only [v₀, v₁] at this
  rw [← cancel_epi hOr.isoSpec.inv, ← cancel_mono (O (r.1 2) (𝒰.inter r)).ι]
  simpa only [Category.assoc] using this

end S_AlgebraicGeometry_SmallExtension_exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary (solution)
