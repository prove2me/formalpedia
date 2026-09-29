-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fa798198-ed41-579a-b139-5f3a7c253aba

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
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq
import Theorems.Thm_AlgebraicGeometry_exists_comp_openInclusion_eq_openInclusion_comp_of_local_lift
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_transitions_any_pair
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_one_cochain_isTangentCoordsOfPairAtVia_pin_of_local_lifts_hom
import Theorems.Thm_AlgebraicGeometry_SmallExtension_unitPullback_obstruction_two_cocycle_sub_eq_d_of_one_cochain_pin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

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
    (hhZg : ∀ w, gZ w ≫ hZ w = X₀.homOfLE (hlam₀ w) ≫ (h₀ ∣_ 𝒰.U (lam w)) ≫ g (lam w)) :
    letI := algebraOfHom fk Ue
    letI := algebraOfHom fXk UXe
    ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
      ∃ b : (OModulePresheaf.unit fXk).cochain (𝒱.comap j₀) 1,
        OModulePresheaf.unitPullback (πX := fXk) hk (𝒱.comap j₀) (𝒰.comap i₀) lam hlamk 2 (ω.1 a ξ) -
            ωX.1 ((Xk.presheaf.map (homOfLE hUX).op).hom ((hk.app Ue).hom a)) ξ =
          (OModulePresheaf.unit fXk).d (𝒱.comap j₀) 1 b := by
  intro a ξ

  obtain ⟨Φ, hΦq, hΦg, hΦres, hΦrefl, hΦsymm, hΦφ⟩ :=
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_transitions_any_pair 𝒰 Y q g O hOm φ hφq hφg hφO

  have hΦX' : ∀ (x y : 𝒱.ι) (h : x < y) (W : X₀.Opens) (hW : W ≤ 𝒱.U x ⊓ 𝒱.U y),
      ∃ τ : ((↑(OX x W) : Scheme.{u}) ≅ ↑(OX y W)),
        τ.hom ≫ (Z y).homOfLE (hOXm y hW) = (Z x).homOfLE (hOXm x hW) ≫ (φX x y h).hom := by
    intro x y h W hW
    obtain ⟨τ, h1, -⟩ := AlgebraicGeometry.Scheme.exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq
      (OX x (𝒱.U x ⊓ 𝒱.U y)) (OX y (𝒱.U x ⊓ 𝒱.U y)) (φX x y h) (OX x W) (OX y W) (hOXm x hW) (hOXm y hW) (hφXO x y h W)
    exact ⟨τ, h1⟩
  choose ΦX hΦX using hΦX'

  have hℓ' : ∀ (x : 𝒱.ι) (WX : X₀.Opens) (WA : A₀.Opens) (h : WX ≤ h₀ ⁻¹ᵁ WA),
      ∃ η : (↑(OX x WX) : Scheme.{u}) ⟶ ↑(O (lam x) WA), η ≫ (O (lam x) WA).ι = (OX x WX).ι ≫ hZ x :=
    fun x WX WA h =>
      AlgebraicGeometry.exists_comp_openInclusion_eq_openInclusion_comp_of_local_lift π hπ hker
        (𝒰.U (lam x)) (g (lam x)) (O (lam x)) (hO (lam x)) fX₀ (𝒱.U x) (gZ x) (qZ x) (hgZ x) (OX x) (hOX x)
        h₀ (hlam₀ x) (hZ x) (hhZg x) WX WA h
  choose ℓ hℓ using hℓ'

  obtain ⟨B, hB⟩ :=
    AlgebraicGeometry.SmallExtension.exists_one_cochain_isTangentCoordsOfPairAtVia_pin_of_local_lifts_hom
      T' T π hπ hker hsmall hI ρ hρ V ι hι hιI f₀ 𝒰 Y q hq g hg fk Lk i₀ hi₀ Ue hUe e₁ he₁ O hO hOm hOtop hOinf hOaff σ hσ₁ hσ₂ φ hφq hφg hφO ρab ρbc ρac hρab hρbc hρac ω hω hωZ fX₀ 𝒱 Z qZ hqZ gZ hgZ fXk LX j₀ hj₀ UXe hUXe eX₁ heX₁ OX hOX hOXm hOXtop hOXinf hOXaff σX hσX₁ hσX₂ φX hφXq hφXg hφXO ρXab ρXbc ρXac hρXab hρXbc hρXac ωX hωX hωXZ h₀ hh₀ lam hlam₀ hk hhk hhkf hhom hUX hlamk hZ hhZq hhZg Φ hΦq hΦg hΦres hΦrefl hΦsymm hΦφ ΦX hΦX ℓ hℓ

  refine ⟨B a ξ, funext fun s => ?_⟩
  rw [Pi.sub_apply]
  exact AlgebraicGeometry.SmallExtension.unitPullback_obstruction_two_cocycle_sub_eq_d_of_one_cochain_pin
    T' T π hπ hker hsmall hI ρ hρ V ι hι hιI f₀ 𝒰 Y q hq g hg fk Lk i₀ hi₀ Ue hUe e₁ he₁ O hO hOm hOtop hOinf hOaff σ hσ₁ hσ₂ φ hφq hφg hφO ρab ρbc ρac hρab hρbc hρac ω hω hωZ fX₀ 𝒱 Z qZ hqZ gZ hgZ fXk LX j₀ hj₀ UXe hUXe eX₁ heX₁ OX hOX hOXm hOXtop hOXinf hOXaff σX hσX₁ hσX₂ φX hφXq hφXg hφXO ρXab ρXbc ρXac hρXab hρXbc hρXac ωX hωX hωXZ h₀ hh₀ lam hlam₀ hk hhk hhkf hhom hUX hlamk hZ hhZq hhZg Φ hΦq hΦg hΦres hΦrefl hΦsymm hΦφ ΦX hΦX ℓ hℓ B hB a ξ s

end S_AlgebraicGeometry_SmallExtension_exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_d_eq_unitPullback_obstruction_two_cocycle_sub_of_local_lifts_hom (solution)
