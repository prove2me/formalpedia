-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_pointDerivations_two_cochain_of_isTangentCoordsOfPairAtVia_pin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1e38ae15-5044-5d1f-a279-89aa5c70b674

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia
import Theorems.Thm_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_two_cochain_of_isTangentCoordsOfPairAtVia_pin

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace E163W

theorem exists_pointDerivations_via
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u : Spec (CommRingCat.of C) ⟶ Y) (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Y)
    (haW : IsPullback aW (W.ι ≫ xk) qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (v : Spec (CommRingCat.of C) ⟶ Y)
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v) :
    letI := algebraOfHom xk Ue
    ∃ (D : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))))
      (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))),
      IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue c ∧ ∀ a, D.1 a = c a := by
  letI := algebraOfHom xk Ue
  obtain ⟨c, hc⟩ := AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia I hI hsmall V ι hι hιI C qY u hu
    xk Lk W aW haW Ue hUe e₁ he₁ v hv huv
  obtain ⟨w₀, hw₀, w₁, hpair, hw₁, hcw⟩ := hc
  have h1 : (w₁ ≫ Ue.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) := by
    rw [hw₁]
    exact (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C) (w₀ ≫ W.ι) hw₀).2.1
  have h2 : SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
      ≫ w₁ ≫ Ue.ι = reductionBase T' C ≫ (Lk.one (𝟙 _)).1 := by
    rw [hw₁]
    exact (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C) (w₀ ≫ W.ι) hw₀).2.2
  obtain ⟨D, hD⟩ := (AlgebraicGeometry.SmallExtension.mem_pointDerivations_tangentCoords_and_injective_and_surjective V C xk
    (Lk.one (𝟙 _)).1 (Lk.one (𝟙 _)).2 Ue hUe e₁ he₁).1 w₁ h1 h2
  exact ⟨D, c, ⟨w₀, hw₀, w₁, hpair, hw₁, hcw⟩, fun a => (hD a).trans (congrFun hcw a).symm⟩

end E163W

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀]
    (hI : RingHom.ker π ≤ maximalIdeal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀]
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))

    (σ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      ((ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))) ≃+* Γ(Ak, (𝒰.comap i₀).inter s))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒰.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
      σ s (x ⊗ₜ[T'] (1 : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)))) = algebraMap (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter s) x)

    (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
    (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
    (hρT : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
          (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) ≫ q (r.1 2) =
        Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))) ∧
      ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
          (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) ≫ q (r.1 2) =
        Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))
    (hρI : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))) ≫
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
            (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))) ≫
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
            (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι))

    (haW : ∀ c : 𝒰.ι,
      IsPullback ((i₀ ∣_ 𝒰.U c) ≫ g c) ((i₀ ⁻¹ᵁ 𝒰.U c).ι ≫ fk) (q c) (Spec.map (CommRingCat.ofHom (residue T')))) :
    ∃ (ω : letI := algebraOfHom fk Ue
        ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
            ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
            (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2))),
      ∀ r : 𝒰.Idx 2,
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
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ r (cs a ξ) = ω.1 a ξ r := by
  classical
  letI iUe := algebraOfHom fk Ue

  have per : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      ∃ (D : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
            ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
            (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
              ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))))))
        (cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                  ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
            ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
                (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
            ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
                (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
            fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs ∧
        ∀ a, D.1 a = cs a := by
    intro r
    letI iC := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
    haveI : Smooth (q (r.1 0)) := hq _
    haveI : Module.Flat T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)) :=
      AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_sections_of_flat (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
        (hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0))
    have hρ := hρT r
    exact E163W.exists_pointDerivations_via (RingHom.ker π) hI hsmall V ι hι hιI Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
      (q (r.1 2)) _ hρ.1 fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) (haW (r.1 2)) Ue hUe e₁ he₁ _ hρ.2 (hρI r)
  choose D cs hcs hD using per

  have σlin : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      ∃ L : ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))) →ₗ[ResidueField T']
          (OModulePresheaf.unit fk).obj ((𝒰.comap i₀).inter r), ∀ t, L t = σ r t := by
    intro r
    letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
    letI := algebraOfHom fk ((𝒰.comap i₀).inter r)
    refine ⟨{ toFun := fun t => σ r t, map_add' := fun t t' => map_add (σ r) t t', map_smul' := fun x t => ?_ }, fun t => rfl⟩
    show σ r (x • t) = x • σ r t
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul,
      hσ₂ r x, ← Algebra.smul_def]
  choose L hL using σlin

  let Ω : Γ(Ak, Ue) →ₗ[ResidueField T']
      (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2) :=
    { toFun := fun a => LinearMap.pi fun r => (L r).comp ((D r).1 a)
      map_add' := fun a b => by
        ext ξ r
        simp only [LinearMap.pi_apply, LinearMap.comp_apply, map_add, LinearMap.add_apply, Pi.add_apply]
      map_smul' := fun x a => by
        ext ξ r
        simp only [LinearMap.pi_apply, LinearMap.comp_apply, map_smul, LinearMap.smul_apply, Pi.smul_apply,
          RingHom.id_apply] }
  have hΩ : Ω ∈ Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
      ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
      (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2) := by
    intro a b
    ext ξ r
    show L r ((D r).1 (a * b) ξ) = _
    rw [(D r).2 a b]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
    rfl
  refine ⟨⟨Ω, hΩ⟩, fun r => ⟨cs r, hcs r, fun a ξ => ?_⟩⟩
  show σ r (cs r a ξ) = L r ((D r).1 a ξ)
  rw [hL, hD]

#print axioms solution

end S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_two_cochain_of_isTangentCoordsOfPairAtVia_pin
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_pointDerivations_two_cochain_of_isTangentCoordsOfPairAtVia_pin (solution)
