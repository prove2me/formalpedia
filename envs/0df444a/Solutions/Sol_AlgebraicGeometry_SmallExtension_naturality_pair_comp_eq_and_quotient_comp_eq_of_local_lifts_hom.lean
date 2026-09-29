-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.naturality_pair_comp_eq_and_quotient_comp_eq_of_local_lifts_hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/dbdf4820-4bd3-5c93-864b-be09b12b989a

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
import Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_naturality_pair_comp_eq_and_quotient_comp_eq_of_local_lifts_hom

set_option autoImplicit false
set_option linter.unusedVariables false

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
    :
    (∀ t : 𝒱.Idx 1,
      letI := algebraOfHom (qZ (t.1 0)) (OX (t.1 0) (𝒱.inter t))
      (((hOXaff (t.1 0) (𝒱.inter t) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 t) (𝒱.inter_le t 0)).isoSpec.inv ≫
                (ΦX (t.1 0) (t.1 1) (t.2 (by decide)) (𝒱.inter t) (le_inf (𝒱.inter_le t 0) (𝒱.inter_le t 1))).hom ≫
                ℓ (t.1 1) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (by rw [Scheme.Hom.preimage_inf]; exact le_inf ((𝒱.inter_le t 0).trans (hlam₀ (t.1 0))) ((𝒱.inter_le t 1).trans (hlam₀ (t.1 1)))) ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι)) ≫ q (lam (t.1 1)) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Z (t.1 0), OX (t.1 0) (𝒱.inter t)))) ∧
      (((hOXaff (t.1 0) (𝒱.inter t) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 t) (𝒱.inter_le t 0)).isoSpec.inv ≫
                ℓ (t.1 0) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (by rw [Scheme.Hom.preimage_inf]; exact le_inf ((𝒱.inter_le t 0).trans (hlam₀ (t.1 0))) ((𝒱.inter_le t 1).trans (hlam₀ (t.1 1)))) ≫
                (Φ (lam (t.1 0)) (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) inf_le_left inf_le_right).hom ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι)) ≫ q (lam (t.1 1)) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Z (t.1 0), OX (t.1 0) (𝒱.inter t))))) ∧
    (∀ t : 𝒱.Idx 1,
      letI := algebraOfHom (qZ (t.1 0)) (OX (t.1 0) (𝒱.inter t))
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Z (t.1 0), OX (t.1 0) (𝒱.inter t)))))) ≫
        (((hOXaff (t.1 0) (𝒱.inter t) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 t) (𝒱.inter_le t 0)).isoSpec.inv ≫
                (ΦX (t.1 0) (t.1 1) (t.2 (by decide)) (𝒱.inter t) (le_inf (𝒱.inter_le t 0) (𝒱.inter_le t 1))).hom ≫
                ℓ (t.1 1) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (by rw [Scheme.Hom.preimage_inf]; exact le_inf ((𝒱.inter_le t 0).trans (hlam₀ (t.1 0))) ((𝒱.inter_le t 1).trans (hlam₀ (t.1 1)))) ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Z (t.1 0), OX (t.1 0) (𝒱.inter t)))))) ≫
        (((hOXaff (t.1 0) (𝒱.inter t) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 t) (𝒱.inter_le t 0)).isoSpec.inv ≫
                ℓ (t.1 0) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (by rw [Scheme.Hom.preimage_inf]; exact le_inf ((𝒱.inter_le t 0).trans (hlam₀ (t.1 0))) ((𝒱.inter_le t 1).trans (hlam₀ (t.1 1)))) ≫
                (Φ (lam (t.1 0)) (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) inf_le_left inf_le_right).hom ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι))) := by
  classical
  have L0 : ∀ (x : 𝒱.ι) (U : (Z x).Opens) (hU : IsAffineOpen U),
      letI := algebraOfHom (qZ x) U
      hU.isoSpec.inv ≫ U.ι ≫ qZ x = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Z x, U))) := by
    intro x U hU
    rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι,
      ← IsAffineOpen.SpecMap_appLE_fromSpec (qZ x) (isAffineOpen_top _) hU le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hVW : ∀ t : 𝒱.Idx 1, (𝒱.inter t) ≤ h₀ ⁻¹ᵁ (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) := fun t =>
    (by rw [Scheme.Hom.preimage_inf]; exact le_inf ((𝒱.inter_le t 0).trans (hlam₀ (t.1 0))) ((𝒱.inter_le t 1).trans (hlam₀ (t.1 1))))

  have EU : ∀ t : 𝒱.Idx 1,
      (ΦX (t.1 0) (t.1 1) (t.2 (by decide)) (𝒱.inter t) (le_inf (𝒱.inter_le t 0) (𝒱.inter_le t 1))).hom ≫
        ℓ (t.1 1) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (hVW t) ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι ≫ q (lam (t.1 1)) = (OX (t.1 0) (𝒱.inter t)).ι ≫ qZ (t.1 0) := by
    intro t
    rw [← Category.assoc (ℓ _ _ _ _), hℓ, Category.assoc, hhZq,
      ← Scheme.homOfLE_ι _ (hOXm (t.1 1) (le_inf (𝒱.inter_le t 0) (𝒱.inter_le t 1))), Category.assoc,
      ← Category.assoc (ΦX _ _ _ _ _).hom, hΦX, Category.assoc, hφXq, ← Category.assoc, Scheme.homOfLE_ι]
  have EV : ∀ t : 𝒱.Idx 1,
      ℓ (t.1 0) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (hVW t) ≫ (Φ (lam (t.1 0)) (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) inf_le_left inf_le_right).hom ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι ≫ q (lam (t.1 1)) =
        (OX (t.1 0) (𝒱.inter t)).ι ≫ qZ (t.1 0) := by
    intro t
    rw [hΦq, ← Category.assoc, hℓ, Category.assoc, hhZq]
  refine ⟨fun t => ?_, fun t => ?_⟩
  · constructor
    · simp only [Category.assoc]
      rw [EU t]
      exact L0 (t.1 0) (OX (t.1 0) (𝒱.inter t)) _
    · simp only [Category.assoc]
      rw [EV t]
      exact L0 (t.1 0) (OX (t.1 0) (𝒱.inter t)) _
  ·
    have hW : IsAffineOpen (OX (t.1 0) (𝒱.inter t)) :=
      hOXaff (t.1 0) (𝒱.inter t) (Scheme.OrderedAffineCover.isAffineOpen_inter fX₀ 𝒱 t) (𝒱.inter_le t 0)
    obtain ⟨-, ε, hε⟩ := AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq
      π hπ hker (qZ (t.1 0)) ((𝒱.U (t.1 0)).ι ≫ fX₀) (gZ (t.1 0)) (hgZ (t.1 0)) (OX (t.1 0) (𝒱.inter t)) hW
    have hε' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map
        (letI := algebraOfHom (qZ (t.1 0)) (OX (t.1 0) (𝒱.inter t)); algebraMap T' Γ(Z (t.1 0), OX (t.1 0) (𝒱.inter t)))))) ≫ hW.isoSpec.inv =
        ε.hom ≫ (gZ (t.1 0) ∣_ OX (t.1 0) (𝒱.inter t)) := by
      rw [← hε]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    suffices M : (gZ (t.1 0) ∣_ OX (t.1 0) (𝒱.inter t)) ≫ (ΦX (t.1 0) (t.1 1) (t.2 (by decide)) (𝒱.inter t) (le_inf (𝒱.inter_le t 0) (𝒱.inter_le t 1))).hom ≫
          ℓ (t.1 1) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (hVW t) ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι =
        (gZ (t.1 0) ∣_ OX (t.1 0) (𝒱.inter t)) ≫ ℓ (t.1 0) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (hVW t) ≫ (Φ (lam (t.1 0)) (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) inf_le_left inf_le_right).hom ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι by
      show Spec.map _ ≫ hW.isoSpec.inv ≫ _ = Spec.map _ ≫ hW.isoSpec.inv ≫ _
      rw [← Category.assoc, hε', ← Category.assoc (Spec.map _), hε', Category.assoc, Category.assoc, M]

    set V' : (↑(𝒱.U (t.1 0)) : Scheme.{u}).Opens := gZ (t.1 0) ⁻¹ᵁ OX (t.1 0) (𝒱.inter t) with hV'
    have hV'eq : V' = (𝒱.U (t.1 0)).ι ⁻¹ᵁ (𝒱.inter t) := by rw [hV', hOX]
    have hV'set : ((V' : (↑(𝒱.U (t.1 0)) : Scheme.{u}).Opens) : Set ↑(𝒱.U (t.1 0))) = (𝒱.U (t.1 0)).ι.base ⁻¹' (((𝒱.inter t) : X₀.Opens) : Set X₀) := by
      rw [hV'eq]; rfl
    have hlamV : Set.range (V'.ι ≫ (𝒱.U (t.1 0)).ι).base ⊆ (((𝒱.inter t) : X₀.Opens) : Set X₀) := by
      rintro _ ⟨x, rfl⟩
      have hx : V'.ι.base x ∈ ((V' : (↑(𝒱.U (t.1 0)) : Scheme.{u}).Opens) : Set ↑(𝒱.U (t.1 0))) := by
        rw [← Scheme.Opens.range_ι V']; exact ⟨x, rfl⟩
      rw [hV'set] at hx
      simpa using hx
    have hVt2 : (𝒱.inter t) ≤ 𝒱.U (t.1 0) ⊓ 𝒱.U (t.1 1) := le_inf (𝒱.inter_le t 0) (𝒱.inter_le t 1)

    obtain ⟨κ, hκ⟩ : ∃ κ : (↑V' : Scheme.{u}) ⟶ ↑(𝒱.U (t.1 0) ⊓ 𝒱.U (t.1 1)), κ ≫ (𝒱.U (t.1 0) ⊓ 𝒱.U (t.1 1)).ι = V'.ι ≫ (𝒱.U (t.1 0)).ι := by
      refine ⟨IsOpenImmersion.lift (𝒱.U (t.1 0) ⊓ 𝒱.U (t.1 1)).ι (V'.ι ≫ (𝒱.U (t.1 0)).ι) ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rw [Scheme.Opens.range_ι]; exact hlamV.trans hVt2

    have hWt : Set.range (V'.ι ≫ (𝒱.U (t.1 0)).ι ≫ h₀).base ⊆ (((𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) : A₀.Opens) : Set A₀) := by
      rintro _ ⟨x, rfl⟩
      have h1 : ((V'.ι ≫ (𝒱.U (t.1 0)).ι).base x) ∈ (((𝒱.inter t) : X₀.Opens) : Set X₀) := hlamV ⟨x, rfl⟩
      have h2 := hVW t h1
      simpa [Scheme.Hom.comp_base] using h2
    obtain ⟨μ, hμ⟩ : ∃ μ : (↑V' : Scheme.{u}) ⟶ ↑(𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))), μ ≫ ((𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι = V'.ι ≫ (𝒱.U (t.1 0)).ι ≫ h₀ := by
      refine ⟨IsOpenImmersion.lift ((𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι (V'.ι ≫ (𝒱.U (t.1 0)).ι ≫ h₀) ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rw [Scheme.Opens.range_ι]; exact hWt

    have hγex : ∀ (a : 𝒰.ι) (ha : (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) ≤ 𝒰.U a), ∃ γ : (↑(𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) : Scheme.{u}) ⟶ ↑(O a (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))),
        γ ≫ (O a (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι = A₀.homOfLE ha ≫ g a := by
      intro a ha
      refine ⟨IsOpenImmersion.lift (O a (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι (A₀.homOfLE ha ≫ g a) ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hp : (A₀.homOfLE ha).base p ∈ ((g a ⁻¹ᵁ O a (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) : (↑(𝒰.U a) : Scheme.{u}).Opens) : Set ↑(𝒰.U a)) := by
        rw [hO]
        show ((A₀.homOfLE ha ≫ (𝒰.U a).ι).base p) ∈ (((𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) : A₀.Opens) : Set A₀)
        rw [Scheme.homOfLE_ι, ← Scheme.Opens.range_ι ((𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))))]
        exact ⟨p, rfl⟩
      simpa [Scheme.Hom.comp_base] using hp
    obtain ⟨γ, hγ⟩ := hγex (lam (t.1 0)) inf_le_left
    obtain ⟨γ', hγ'⟩ := hγex (lam (t.1 1)) inf_le_right
    obtain ⟨γX, γX', hγX, hγX', hφγX⟩ := hφXg (t.1 0) (t.1 1) (t.2 (by decide))

    have hκ' : κ ≫ X₀.homOfLE (inf_le_left : 𝒱.U (t.1 0) ⊓ 𝒱.U (t.1 1) ≤ 𝒱.U (t.1 0)) = V'.ι := by
      rw [← cancel_mono (𝒱.U (t.1 0)).ι, Category.assoc, Scheme.homOfLE_ι, hκ]
    have hκa : ∀ {Q : Scheme.{u}} (k : X₀ ⟶ Q), κ ≫ (𝒱.U (t.1 0) ⊓ 𝒱.U (t.1 1)).ι ≫ k = V'.ι ≫ (𝒱.U (t.1 0)).ι ≫ k :=
      fun k => by rw [← Category.assoc, hκ, Category.assoc]
    have hμa : ∀ {Q : Scheme.{u}} (k : A₀ ⟶ Q), μ ≫ (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))).ι ≫ k =
        V'.ι ≫ (𝒱.U (t.1 0)).ι ≫ h₀ ≫ k :=
      fun k => by rw [← Category.assoc, hμ, Category.assoc, Category.assoc]
    have F1X : (gZ (t.1 0) ∣_ OX (t.1 0) (𝒱.inter t)) ≫ (Z (t.1 0)).homOfLE (hOXm (t.1 0) hVt2) = κ ≫ γX := by
      rw [← cancel_mono (OX (t.1 0) (𝒱.U (t.1 0) ⊓ 𝒱.U (t.1 1))).ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι,
        Category.assoc, hγX, ← Category.assoc κ, hκ']

    have KY1 : κ ≫ X₀.homOfLE (inf_le_right : 𝒱.U (t.1 0) ⊓ 𝒱.U (t.1 1) ≤ 𝒱.U (t.1 1)) ≫ X₀.homOfLE (hlam₀ (t.1 1)) ≫ (h₀ ∣_ 𝒰.U (lam (t.1 1))) =
        μ ≫ A₀.homOfLE (inf_le_right : (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) ≤ 𝒰.U (lam (t.1 1))) := by
      rw [← cancel_mono (𝒰.U (lam (t.1 1))).ι]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, hμ, hκa]
    have KX1 : V'.ι ≫ X₀.homOfLE (hlam₀ (t.1 0)) ≫ (h₀ ∣_ 𝒰.U (lam (t.1 0))) = μ ≫ A₀.homOfLE (inf_le_left : (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) ≤ 𝒰.U (lam (t.1 0))) := by
      rw [← cancel_mono (𝒰.U (lam (t.1 0))).ι]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, hμ]
    have KY1g : κ ≫ X₀.homOfLE (inf_le_right : 𝒱.U (t.1 0) ⊓ 𝒱.U (t.1 1) ≤ 𝒱.U (t.1 1)) ≫ X₀.homOfLE (hlam₀ (t.1 1)) ≫
        (h₀ ∣_ 𝒰.U (lam (t.1 1))) ≫ g (lam (t.1 1)) =
        μ ≫ A₀.homOfLE (inf_le_right : (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) ≤ 𝒰.U (lam (t.1 1))) ≫ g (lam (t.1 1)) := by
      rw [← Category.assoc μ, ← KY1]; simp only [Category.assoc]

    have L : (gZ (t.1 0) ∣_ OX (t.1 0) (𝒱.inter t)) ≫ (ΦX (t.1 0) (t.1 1) (t.2 (by decide)) (𝒱.inter t) hVt2).hom ≫ ℓ (t.1 1) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (hVW t) ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι =
        μ ≫ A₀.homOfLE (inf_le_right : (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) ≤ 𝒰.U (lam (t.1 1))) ≫ g (lam (t.1 1)) := by
      rw [hℓ, ← Scheme.homOfLE_ι _ (hOXm (t.1 1) hVt2), Category.assoc, ← Category.assoc (ΦX _ _ _ _ _).hom, hΦX,
        Category.assoc, ← Category.assoc (gZ (t.1 0) ∣_ _), F1X, Category.assoc, ← Category.assoc γX, hφγX,
        ← Category.assoc γX', hγX']
      simp only [Category.assoc]
      rw [hhZg, KY1g]

    have F1A : (gZ (t.1 0) ∣_ OX (t.1 0) (𝒱.inter t)) ≫ ℓ (t.1 0) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (hVW t) = μ ≫ γ := by
      rw [← cancel_mono (O (lam (t.1 0)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι, Category.assoc, hℓ, ← Category.assoc, morphismRestrict_ι, Category.assoc,
        hhZg, Category.assoc, hγ, ← Category.assoc μ, ← KX1]
      simp only [Category.assoc]
      rfl
    have R : (gZ (t.1 0) ∣_ OX (t.1 0) (𝒱.inter t)) ≫ ℓ (t.1 0) (𝒱.inter t) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) (hVW t) ≫ (Φ (lam (t.1 0)) (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) inf_le_left inf_le_right).hom ≫ (O (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1)))).ι =
        μ ≫ A₀.homOfLE (inf_le_right : (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) ≤ 𝒰.U (lam (t.1 1))) ≫ g (lam (t.1 1)) := by
      rw [← Category.assoc (gZ (t.1 0) ∣_ _), F1A, Category.assoc, ← Category.assoc γ,
        hΦg (lam (t.1 0)) (lam (t.1 1)) (𝒰.U (lam (t.1 0)) ⊓ 𝒰.U (lam (t.1 1))) inf_le_left inf_le_right γ γ' hγ hγ', hγ']
    exact L.trans R.symm

end S_AlgebraicGeometry_SmallExtension_naturality_pair_comp_eq_and_quotient_comp_eq_of_local_lifts_hom
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_naturality_pair_comp_eq_and_quotient_comp_eq_of_local_lifts_hom (solution)
