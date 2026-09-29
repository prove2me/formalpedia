-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.d_two_cochain_eq_zero_of_isTangentCoordsOfPairAtVia_pin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9bd2e164-f869-5fc2-a365-55ade6a4c2d6

import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_add
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_of_isPullback_of_comp_mono
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq
import Theorems.Thm_AlgebraicGeometry_exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_d_two_cochain_eq_zero_of_isTangentCoordsOfPairAtVia_pin

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.haveLet 0
set_option linter.unreachableTactic false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace CocAux

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

theorem specMap_res_comp_isoSpec_inv {X : Scheme.{u}} {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) :
    Spec.map (X.presheaf.map (homOfLE h).op) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ X.homOfLE h := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι]
  exact IsAffineOpen.map_fromSpec hU hV (homOfLE h).op

end CocAux

open CocAux

theorem CocAux.alt_sum_eq_zero {M N : Type u} [AddCommGroup M] [AddCommGroup N] (s : M → N)
    (hs : ∀ x y, s (x + y) = s x + s y) (y0 y1 y2 y3 : M) (h : y0 + y2 = y1 + y3) :
    ((-1 : ℤ) ^ ((0 : Fin (2 + 2)) : ℕ)) • s y0 + ((-1 : ℤ) ^ ((1 : Fin (2 + 2)) : ℕ)) • s y1 +
      ((-1 : ℤ) ^ ((2 : Fin (2 + 2)) : ℕ)) • s y2 + ((-1 : ℤ) ^ ((3 : Fin (2 + 2)) : ℕ)) • s y3 = 0 := by
  have e : s y0 + s y2 = s y1 + s y3 := by rw [← hs, ← hs, h]
  have e0 : ((-1 : ℤ) ^ ((0 : Fin (2 + 2)) : ℕ)) = 1 := by norm_num
  have e1 : ((-1 : ℤ) ^ ((1 : Fin (2 + 2)) : ℕ)) = -1 := by norm_num
  have e2 : ((-1 : ℤ) ^ ((2 : Fin (2 + 2)) : ℕ)) = 1 := by norm_num
  have e3 : ((-1 : ℤ) ^ ((3 : Fin (2 + 2)) : ℕ)) = -1 := by
    rw [show ((3 : Fin (2 + 2)) : ℕ) = 3 from rfl]; norm_num
  rw [e0, e1, e2, e3]
  calc _ = (s y0 + s y2) - (s y1 + s y3) := by abel
    _ = 0 := by rw [e, sub_self]

theorem CocAux.reassoc3 {C : Type*} [Category C] {P Q R S T : C} {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S} {d : S ⟶ T}
    {e : P ⟶ T} (h : a ≫ b ≫ c ≫ d = e) : (a ≫ b ≫ c) ≫ d = e := by
  simpa only [Category.assoc] using h

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
        ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ r (cs a ξ) = ω.1 a ξ r) :
    letI := algebraOfHom fk Ue
    ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
    (OModulePresheaf.unit fk).d (𝒰.comap i₀) 2 (ω.1 a ξ) = 0 := by
  classical
  intro a₀ ξ
  funext t
  rw [OModulePresheaf.d_apply, Pi.zero_apply]

  obtain ⟨cs0, hcs0, hp0⟩ := hω (𝒰.face t 0)
  obtain ⟨cs1, hcs1, hp1⟩ := hω (𝒰.face t 1)
  obtain ⟨cs2, hcs2, hp2⟩ := hω (𝒰.face t 2)
  obtain ⟨cs3, hcs3, hp3⟩ := hω (𝒰.face t 3)

  have hab : t.1 0 < t.1 1 := t.2 (by decide)
  have hac : t.1 0 < t.1 2 := t.2 (by decide)
  have had : t.1 0 < t.1 3 := t.2 (by decide)
  have hbc : t.1 1 < t.1 2 := t.2 (by decide)
  have hbd : t.1 1 < t.1 3 := t.2 (by decide)
  have hcd : t.1 2 < t.1 3 := t.2 (by decide)
  have haff : ∀ {n : ℕ} (s : 𝒰.Idx n), IsAffineOpen (𝒰.inter s) := fun s =>
    Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 s
  have hle : ∀ (i j : Fin 4), 𝒰.inter t ≤ 𝒰.U (t.1 i) ⊓ 𝒰.U (t.1 j) := fun i j =>
    le_inf (𝒰.inter_le t i) (𝒰.inter_le t j)

  let ρab0 : (↑(O (t.1 1) (𝒰.inter (𝒰.face t 0))) : Scheme.{u}) ≅ ↑(O (t.1 2) (𝒰.inter (𝒰.face t 0))) := ρab (𝒰.face t 0)
  let ρbc0 : (↑(O (t.1 2) (𝒰.inter (𝒰.face t 0))) : Scheme.{u}) ≅ ↑(O (t.1 3) (𝒰.inter (𝒰.face t 0))) := ρbc (𝒰.face t 0)
  let ρac0 : (↑(O (t.1 1) (𝒰.inter (𝒰.face t 0))) : Scheme.{u}) ≅ ↑(O (t.1 3) (𝒰.inter (𝒰.face t 0))) := ρac (𝒰.face t 0)
  have hW0ab : 𝒰.inter (𝒰.face t 0) ≤ 𝒰.U (t.1 1) ⊓ 𝒰.U (t.1 2) := le_inf (𝒰.inter_le (𝒰.face t 0) 0) (𝒰.inter_le (𝒰.face t 0) 1)
  have hW0bc : 𝒰.inter (𝒰.face t 0) ≤ 𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3) := le_inf (𝒰.inter_le (𝒰.face t 0) 1) (𝒰.inter_le (𝒰.face t 0) 2)
  have hW0ac : 𝒰.inter (𝒰.face t 0) ≤ 𝒰.U (t.1 1) ⊓ 𝒰.U (t.1 3) := le_inf (𝒰.inter_le (𝒰.face t 0) 0) (𝒰.inter_le (𝒰.face t 0) 2)
  have hρab0 : ρab0.hom ≫ (Y (t.1 2)).homOfLE (hOm (t.1 2) hW0ab) =
      (Y (t.1 1)).homOfLE (hOm (t.1 1) hW0ab) ≫ (φ (t.1 1) (t.1 2) hbc).hom := hρab (𝒰.face t 0)
  have hρbc0 : ρbc0.hom ≫ (Y (t.1 3)).homOfLE (hOm (t.1 3) hW0bc) =
      (Y (t.1 2)).homOfLE (hOm (t.1 2) hW0bc) ≫ (φ (t.1 2) (t.1 3) hcd).hom := hρbc (𝒰.face t 0)
  have hρac0 : ρac0.hom ≫ (Y (t.1 3)).homOfLE (hOm (t.1 3) hW0ac) =
      (Y (t.1 1)).homOfLE (hOm (t.1 1) hW0ac) ≫ (φ (t.1 1) (t.1 3) hbd).hom := hρac (𝒰.face t 0)
  let ρab1 : (↑(O (t.1 0) (𝒰.inter (𝒰.face t 1))) : Scheme.{u}) ≅ ↑(O (t.1 2) (𝒰.inter (𝒰.face t 1))) := ρab (𝒰.face t 1)
  let ρbc1 : (↑(O (t.1 2) (𝒰.inter (𝒰.face t 1))) : Scheme.{u}) ≅ ↑(O (t.1 3) (𝒰.inter (𝒰.face t 1))) := ρbc (𝒰.face t 1)
  let ρac1 : (↑(O (t.1 0) (𝒰.inter (𝒰.face t 1))) : Scheme.{u}) ≅ ↑(O (t.1 3) (𝒰.inter (𝒰.face t 1))) := ρac (𝒰.face t 1)
  have hW1ab : 𝒰.inter (𝒰.face t 1) ≤ 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 2) := le_inf (𝒰.inter_le (𝒰.face t 1) 0) (𝒰.inter_le (𝒰.face t 1) 1)
  have hW1bc : 𝒰.inter (𝒰.face t 1) ≤ 𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3) := le_inf (𝒰.inter_le (𝒰.face t 1) 1) (𝒰.inter_le (𝒰.face t 1) 2)
  have hW1ac : 𝒰.inter (𝒰.face t 1) ≤ 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 3) := le_inf (𝒰.inter_le (𝒰.face t 1) 0) (𝒰.inter_le (𝒰.face t 1) 2)
  have hρab1 : ρab1.hom ≫ (Y (t.1 2)).homOfLE (hOm (t.1 2) hW1ab) =
      (Y (t.1 0)).homOfLE (hOm (t.1 0) hW1ab) ≫ (φ (t.1 0) (t.1 2) hac).hom := hρab (𝒰.face t 1)
  have hρbc1 : ρbc1.hom ≫ (Y (t.1 3)).homOfLE (hOm (t.1 3) hW1bc) =
      (Y (t.1 2)).homOfLE (hOm (t.1 2) hW1bc) ≫ (φ (t.1 2) (t.1 3) hcd).hom := hρbc (𝒰.face t 1)
  have hρac1 : ρac1.hom ≫ (Y (t.1 3)).homOfLE (hOm (t.1 3) hW1ac) =
      (Y (t.1 0)).homOfLE (hOm (t.1 0) hW1ac) ≫ (φ (t.1 0) (t.1 3) had).hom := hρac (𝒰.face t 1)
  let ρab2 : (↑(O (t.1 0) (𝒰.inter (𝒰.face t 2))) : Scheme.{u}) ≅ ↑(O (t.1 1) (𝒰.inter (𝒰.face t 2))) := ρab (𝒰.face t 2)
  let ρbc2 : (↑(O (t.1 1) (𝒰.inter (𝒰.face t 2))) : Scheme.{u}) ≅ ↑(O (t.1 3) (𝒰.inter (𝒰.face t 2))) := ρbc (𝒰.face t 2)
  let ρac2 : (↑(O (t.1 0) (𝒰.inter (𝒰.face t 2))) : Scheme.{u}) ≅ ↑(O (t.1 3) (𝒰.inter (𝒰.face t 2))) := ρac (𝒰.face t 2)
  have hW2ab : 𝒰.inter (𝒰.face t 2) ≤ 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1) := le_inf (𝒰.inter_le (𝒰.face t 2) 0) (𝒰.inter_le (𝒰.face t 2) 1)
  have hW2bc : 𝒰.inter (𝒰.face t 2) ≤ 𝒰.U (t.1 1) ⊓ 𝒰.U (t.1 3) := le_inf (𝒰.inter_le (𝒰.face t 2) 1) (𝒰.inter_le (𝒰.face t 2) 2)
  have hW2ac : 𝒰.inter (𝒰.face t 2) ≤ 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 3) := le_inf (𝒰.inter_le (𝒰.face t 2) 0) (𝒰.inter_le (𝒰.face t 2) 2)
  have hρab2 : ρab2.hom ≫ (Y (t.1 1)).homOfLE (hOm (t.1 1) hW2ab) =
      (Y (t.1 0)).homOfLE (hOm (t.1 0) hW2ab) ≫ (φ (t.1 0) (t.1 1) hab).hom := hρab (𝒰.face t 2)
  have hρbc2 : ρbc2.hom ≫ (Y (t.1 3)).homOfLE (hOm (t.1 3) hW2bc) =
      (Y (t.1 1)).homOfLE (hOm (t.1 1) hW2bc) ≫ (φ (t.1 1) (t.1 3) hbd).hom := hρbc (𝒰.face t 2)
  have hρac2 : ρac2.hom ≫ (Y (t.1 3)).homOfLE (hOm (t.1 3) hW2ac) =
      (Y (t.1 0)).homOfLE (hOm (t.1 0) hW2ac) ≫ (φ (t.1 0) (t.1 3) had).hom := hρac (𝒰.face t 2)
  let ρab3 : (↑(O (t.1 0) (𝒰.inter (𝒰.face t 3))) : Scheme.{u}) ≅ ↑(O (t.1 1) (𝒰.inter (𝒰.face t 3))) := ρab (𝒰.face t 3)
  let ρbc3 : (↑(O (t.1 1) (𝒰.inter (𝒰.face t 3))) : Scheme.{u}) ≅ ↑(O (t.1 2) (𝒰.inter (𝒰.face t 3))) := ρbc (𝒰.face t 3)
  let ρac3 : (↑(O (t.1 0) (𝒰.inter (𝒰.face t 3))) : Scheme.{u}) ≅ ↑(O (t.1 2) (𝒰.inter (𝒰.face t 3))) := ρac (𝒰.face t 3)
  have hW3ab : 𝒰.inter (𝒰.face t 3) ≤ 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1) := le_inf (𝒰.inter_le (𝒰.face t 3) 0) (𝒰.inter_le (𝒰.face t 3) 1)
  have hW3bc : 𝒰.inter (𝒰.face t 3) ≤ 𝒰.U (t.1 1) ⊓ 𝒰.U (t.1 2) := le_inf (𝒰.inter_le (𝒰.face t 3) 1) (𝒰.inter_le (𝒰.face t 3) 2)
  have hW3ac : 𝒰.inter (𝒰.face t 3) ≤ 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 2) := le_inf (𝒰.inter_le (𝒰.face t 3) 0) (𝒰.inter_le (𝒰.face t 3) 2)
  have hρab3 : ρab3.hom ≫ (Y (t.1 1)).homOfLE (hOm (t.1 1) hW3ab) =
      (Y (t.1 0)).homOfLE (hOm (t.1 0) hW3ab) ≫ (φ (t.1 0) (t.1 1) hab).hom := hρab (𝒰.face t 3)
  have hρbc3 : ρbc3.hom ≫ (Y (t.1 2)).homOfLE (hOm (t.1 2) hW3bc) =
      (Y (t.1 1)).homOfLE (hOm (t.1 1) hW3bc) ≫ (φ (t.1 1) (t.1 2) hbc).hom := hρbc (𝒰.face t 3)
  have hρac3 : ρac3.hom ≫ (Y (t.1 2)).homOfLE (hOm (t.1 2) hW3ac) =
      (Y (t.1 0)).homOfLE (hOm (t.1 0) hW3ac) ≫ (φ (t.1 0) (t.1 2) hac).hom := hρac (𝒰.face t 3)

  have resNat : ∀ {W₁ W₂ : A₀.Opens} (h : W₁ ≤ W₂),
      Ak.homOfLE (i₀.preimage_mono h) ≫ (i₀ ∣_ W₂) = (i₀ ∣_ W₁) ≫ A₀.homOfLE h := by
    intro W₁ W₂ h
    rw [← cancel_mono W₂.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]
  have resNat_assoc : ∀ {W₁ W₂ : A₀.Opens} (h : W₁ ≤ W₂) {Z : Scheme.{u}} (f : (↑W₂ : Scheme.{u}) ⟶ Z),
      (i₀ ∣_ W₁) ≫ A₀.homOfLE h ≫ f = Ak.homOfLE (i₀.preimage_mono h) ≫ (i₀ ∣_ W₂) ≫ f := by
    intro W₁ W₂ h Z f
    rw [← Category.assoc, ← resNat, Category.assoc]
  have merge : ∀ {U₁ V₁ W₁ : Ak.Opens} (e₁ : U₁ ≤ V₁) (e₂ : V₁ ≤ W₁) {Z : Scheme.{u}} (h : (↑W₁ : Scheme.{u}) ⟶ Z),
      Ak.homOfLE e₁ ≫ Ak.homOfLE e₂ ≫ h = Ak.homOfLE (e₁.trans e₂) ≫ h := by
    intro U₁ V₁ W₁ e₁ e₂ Z h
    rw [← Category.assoc, Scheme.homOfLE_homOfLE]

  have hτ := fun (i j : Fin 4) (h : t.1 i < t.1 j) =>
    AlgebraicGeometry.Scheme.exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq
      (O (t.1 i) (𝒰.U (t.1 i) ⊓ 𝒰.U (t.1 j))) (O (t.1 j) (𝒰.U (t.1 i) ⊓ 𝒰.U (t.1 j))) (φ (t.1 i) (t.1 j) h)
      (O (t.1 i) (𝒰.inter t)) (O (t.1 j) (𝒰.inter t)) (hOm (t.1 i) (hle i j)) (hOm (t.1 j) (hle i j))
      (hφO (t.1 i) (t.1 j) h (𝒰.inter t))
  obtain ⟨τab, hτab, hτab'⟩ := hτ 0 1 hab
  obtain ⟨τac, hτac, hτac'⟩ := hτ 0 2 hac
  obtain ⟨τad, hτad, hτad'⟩ := hτ 0 3 had
  obtain ⟨τbc, hτbc, hτbc'⟩ := hτ 1 2 hbc
  obtain ⟨τbd, hτbd, hτbd'⟩ := hτ 1 3 hbd
  obtain ⟨τcd, hτcd, hτcd'⟩ := hτ 2 3 hcd

  obtain ⟨aWc, haWcι, hsqc⟩ := AlgebraicGeometry.exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift
    (𝒰.U (t.1 2)) (g (t.1 2)) (O (t.1 2)) (hO (t.1 2)) i₀ (𝒰.inter t) (𝒰.inter_le t 2)
  obtain ⟨aWd, haWdι, hsqd⟩ := AlgebraicGeometry.exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift
    (𝒰.U (t.1 3)) (g (t.1 3)) (O (t.1 3)) (hO (t.1 3)) i₀ (𝒰.inter t) (𝒰.inter_le t 3)

  letI instC : Algebra T' Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) := algebraOfHom (q (t.1 0)) (O (t.1 0) (𝒰.inter t))
  have hOt : IsAffineOpen (O (t.1 0) (𝒰.inter t)) := hOaff (t.1 0) (𝒰.inter t) (haff t) (𝒰.inter_le t 0)
  haveI : Smooth (q (t.1 0)) := hq (t.1 0)
  haveI : Module.Flat T' Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) := flat_sections (q (t.1 0)) hOt
  have hιq : hOt.isoSpec.inv ≫ (O (t.1 0) (𝒰.inter t)).ι ≫ q (t.1 0) =
      Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)))) := by
    rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι]; exact fromSpec_comp_eq (q (t.1 0)) hOt

  obtain ⟨m1, hm1d⟩ : ∃ m : Spec (CommRingCat.of Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t))) ⟶ Y (t.1 3),
      m = hOt.isoSpec.inv ≫ τad.hom ≫ (O (t.1 3) (𝒰.inter t)).ι := ⟨_, rfl⟩
  obtain ⟨m2, hm2d⟩ : ∃ m : Spec (CommRingCat.of Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t))) ⟶ Y (t.1 3),
      m = hOt.isoSpec.inv ≫ τab.hom ≫ τbd.hom ≫ (O (t.1 3) (𝒰.inter t)).ι := ⟨_, rfl⟩
  obtain ⟨m3, hm3d⟩ : ∃ m : Spec (CommRingCat.of Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t))) ⟶ Y (t.1 3),
      m = hOt.isoSpec.inv ≫ τac.hom ≫ τcd.hom ≫ (O (t.1 3) (𝒰.inter t)).ι := ⟨_, rfl⟩
  obtain ⟨m4, hm4d⟩ : ∃ m : Spec (CommRingCat.of Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t))) ⟶ Y (t.1 3),
      m = hOt.isoSpec.inv ≫ τab.hom ≫ τbc.hom ≫ τcd.hom ≫ (O (t.1 3) (𝒰.inter t)).ι := ⟨_, rfl⟩

  have τT : ∀ (x y : 𝒰.ι) (hxy : x < y) (hW : 𝒰.inter t ≤ 𝒰.U x ⊓ 𝒰.U y)
      (τ : (↑(O x (𝒰.inter t)) : Scheme.{u}) ≅ ↑(O y (𝒰.inter t)))
      (hτ : τ.hom ≫ (Y y).homOfLE (hOm y hW) = (Y x).homOfLE (hOm x hW) ≫ (φ x y hxy).hom),
      τ.hom ≫ (O y (𝒰.inter t)).ι ≫ q y = (O x (𝒰.inter t)).ι ≫ q x := by
    intro x y hxy hW τ hτ
    rw [← Scheme.homOfLE_ι (Y y) (hOm y hW), ← Scheme.homOfLE_ι (Y x) (hOm x hW), Category.assoc, Category.assoc,
      hφq x y hxy |>.symm, ← Category.assoc τ.hom, hτ, Category.assoc]

  have ρτ : ∀ (x y : 𝒰.ι) (hxy : x < y) (Wr : A₀.Opens) (hWr : Wr ≤ 𝒰.U x ⊓ 𝒰.U y) (htr : 𝒰.inter t ≤ Wr)
      (hW : 𝒰.inter t ≤ 𝒰.U x ⊓ 𝒰.U y)
      (ρ : (↑(O x Wr) : Scheme.{u}) ≅ ↑(O y Wr)) (τ : (↑(O x (𝒰.inter t)) : Scheme.{u}) ≅ ↑(O y (𝒰.inter t)))
      (hρ : ρ.hom ≫ (Y y).homOfLE (hOm y hWr) = (Y x).homOfLE (hOm x hWr) ≫ (φ x y hxy).hom)
      (hτ : τ.hom ≫ (Y y).homOfLE (hOm y hW) = (Y x).homOfLE (hOm x hW) ≫ (φ x y hxy).hom),
      (Y x).homOfLE (hOm x htr) ≫ ρ.hom = τ.hom ≫ (Y y).homOfLE (hOm y htr) := by
    intro x y hxy Wr hWr htr hW ρ τ hρ hτ
    rw [← cancel_mono ((Y y).homOfLE (hOm y hWr)), Category.assoc, Category.assoc, hρ, Scheme.homOfLE_homOfLE,
      ← Category.assoc ((Y x).homOfLE _), Scheme.homOfLE_homOfLE]
    exact hτ.symm

  letI i1 : Algebra T' Γ(Y (t.1 0), O (t.1 0) (𝒰.inter (𝒰.face t 1))) := algebraOfHom (q (t.1 0)) (O (t.1 0) (𝒰.inter (𝒰.face t 1)))
  letI i2 : Algebra T' Γ(Y (t.1 0), O (t.1 0) (𝒰.inter (𝒰.face t 2))) := algebraOfHom (q (t.1 0)) (O (t.1 0) (𝒰.inter (𝒰.face t 2)))
  letI i3 : Algebra T' Γ(Y (t.1 0), O (t.1 0) (𝒰.inter (𝒰.face t 3))) := algebraOfHom (q (t.1 0)) (O (t.1 0) (𝒰.inter (𝒰.face t 3)))
  let h1 : Γ(Y (t.1 0), O (t.1 0) (𝒰.inter (𝒰.face t 1))) →ₐ[T'] Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) :=
    restrictAlgHom (q (t.1 0)) (hOm (t.1 0) (𝒰.inter_le_inter_face t 1))
  let h2 : Γ(Y (t.1 0), O (t.1 0) (𝒰.inter (𝒰.face t 2))) →ₐ[T'] Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) :=
    restrictAlgHom (q (t.1 0)) (hOm (t.1 0) (𝒰.inter_le_inter_face t 2))
  let h3 : Γ(Y (t.1 0), O (t.1 0) (𝒰.inter (𝒰.face t 3))) →ₐ[T'] Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) :=
    restrictAlgHom (q (t.1 0)) (hOm (t.1 0) (𝒰.inter_le_inter_face t 3))

  have hA1 : IsAffineOpen (O (t.1 0) (𝒰.inter (𝒰.face t 1))) := hOaff _ _ (haff (𝒰.face t 1)) (𝒰.inter_le (𝒰.face t 1) 0)
  have hA2 : IsAffineOpen (O (t.1 0) (𝒰.inter (𝒰.face t 2))) := hOaff _ _ (haff (𝒰.face t 2)) (𝒰.inter_le (𝒰.face t 2) 0)
  have hA3 : IsAffineOpen (O (t.1 0) (𝒰.inter (𝒰.face t 3))) := hOaff _ _ (haff (𝒰.face t 3)) (𝒰.inter_le (𝒰.face t 3) 0)

  have hcs1' : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (t.1 0), O (t.1 0) (𝒰.inter (𝒰.face t 1)))
      (hA1.isoSpec.inv ≫ ρac1.hom ≫ (O (t.1 3) (𝒰.inter (𝒰.face t 1))).ι)
      (hA1.isoSpec.inv ≫ ρab1.hom ≫ ρbc1.hom ≫ (O (t.1 3) (𝒰.inter (𝒰.face t 1))).ι)
      fk Lk (i₀ ⁻¹ᵁ 𝒰.U (t.1 3)) ((i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3)) Ue cs1 := hcs1
  have hcs2' : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (t.1 0), O (t.1 0) (𝒰.inter (𝒰.face t 2)))
      (hA2.isoSpec.inv ≫ ρac2.hom ≫ (O (t.1 3) (𝒰.inter (𝒰.face t 2))).ι)
      (hA2.isoSpec.inv ≫ ρab2.hom ≫ ρbc2.hom ≫ (O (t.1 3) (𝒰.inter (𝒰.face t 2))).ι)
      fk Lk (i₀ ⁻¹ᵁ 𝒰.U (t.1 3)) ((i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3)) Ue cs2 := hcs2
  have hcs3' : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (t.1 0), O (t.1 0) (𝒰.inter (𝒰.face t 3)))
      (hA3.isoSpec.inv ≫ ρac3.hom ≫ (O (t.1 2) (𝒰.inter (𝒰.face t 3))).ι)
      (hA3.isoSpec.inv ≫ ρab3.hom ≫ ρbc3.hom ≫ (O (t.1 2) (𝒰.inter (𝒰.face t 3))).ι)
      fk Lk (i₀ ⁻¹ᵁ 𝒰.U (t.1 2)) ((i₀ ∣_ 𝒰.U (t.1 2)) ≫ g (t.1 2)) Ue cs3 := hcs3

  have H1 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) m1 m3 fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (t.1 3)) ((i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3)) Ue
      (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h1).toLinearMap ∘ₗ cs1 x) := by
    have raw := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat (RingHom.ker π) hI hsmall V ι hι hιI
      _ _ h1 _ _ fk Lk _ _ Ue _ hcs1'
    have hS : Spec.map (CommRingCat.ofHom h1.toRingHom) =
        Spec.map ((Y (t.1 0)).presheaf.map (homOfLE (hOm (t.1 0) (𝒰.inter_le_inter_face t 1))).op) := rfl
    have eu : Spec.map (CommRingCat.ofHom h1.toRingHom) ≫
        (hA1.isoSpec.inv ≫ ρac1.hom ≫ (O (t.1 3) (𝒰.inter (𝒰.face t 1))).ι) = m1 := by
      rw [hm1d, hS, ← Category.assoc, specMap_res_comp_isoSpec_inv hA1 hOt (hOm (t.1 0) (𝒰.inter_le_inter_face t 1)),
        Category.assoc, ← Category.assoc ((Y (t.1 0)).homOfLE _),
        ρτ (t.1 0) (t.1 3) had (𝒰.inter (𝒰.face t 1)) hW1ac
          (𝒰.inter_le_inter_face t 1) (hle 0 3) ρac1 τad hρac1 hτad,
        Category.assoc, Scheme.homOfLE_ι]
    have ev : Spec.map (CommRingCat.ofHom h1.toRingHom) ≫
        (hA1.isoSpec.inv ≫ ρab1.hom ≫ ρbc1.hom ≫ (O (t.1 3) (𝒰.inter (𝒰.face t 1))).ι) = m3 := by
      rw [hm3d, hS, ← Category.assoc, specMap_res_comp_isoSpec_inv hA1 hOt (hOm (t.1 0) (𝒰.inter_le_inter_face t 1)),
        Category.assoc, ← Category.assoc ((Y (t.1 0)).homOfLE _),
        ρτ (t.1 0) (t.1 2) hac (𝒰.inter (𝒰.face t 1)) hW1ab
          (𝒰.inter_le_inter_face t 1) (hle 0 2) ρab1 τac hρab1 hτac,
        Category.assoc, ← Category.assoc ((Y (t.1 2)).homOfLE _),
        ρτ (t.1 2) (t.1 3) hcd (𝒰.inter (𝒰.face t 1)) hW1bc
          (𝒰.inter_le_inter_face t 1) (hle 2 3) ρbc1 τcd hρbc1 hτcd,
        Category.assoc, Scheme.homOfLE_ι]
    rw [eu, ev] at raw
    exact raw
  have H2 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) m1 m2 fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (t.1 3)) ((i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3)) Ue
      (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h2).toLinearMap ∘ₗ cs2 x) := by
    have raw := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat (RingHom.ker π) hI hsmall V ι hι hιI
      _ _ h2 _ _ fk Lk _ _ Ue _ hcs2'
    have hS : Spec.map (CommRingCat.ofHom h2.toRingHom) =
        Spec.map ((Y (t.1 0)).presheaf.map (homOfLE (hOm (t.1 0) (𝒰.inter_le_inter_face t 2))).op) := rfl
    have eu : Spec.map (CommRingCat.ofHom h2.toRingHom) ≫
        (hA2.isoSpec.inv ≫ ρac2.hom ≫ (O (t.1 3) (𝒰.inter (𝒰.face t 2))).ι) = m1 := by
      rw [hm1d, hS, ← Category.assoc, specMap_res_comp_isoSpec_inv hA2 hOt (hOm (t.1 0) (𝒰.inter_le_inter_face t 2)),
        Category.assoc, ← Category.assoc ((Y (t.1 0)).homOfLE _),
        ρτ (t.1 0) (t.1 3) had (𝒰.inter (𝒰.face t 2)) hW2ac
          (𝒰.inter_le_inter_face t 2) (hle 0 3) ρac2 τad hρac2 hτad,
        Category.assoc, Scheme.homOfLE_ι]
    have ev : Spec.map (CommRingCat.ofHom h2.toRingHom) ≫
        (hA2.isoSpec.inv ≫ ρab2.hom ≫ ρbc2.hom ≫ (O (t.1 3) (𝒰.inter (𝒰.face t 2))).ι) = m2 := by
      rw [hm2d, hS, ← Category.assoc, specMap_res_comp_isoSpec_inv hA2 hOt (hOm (t.1 0) (𝒰.inter_le_inter_face t 2)),
        Category.assoc, ← Category.assoc ((Y (t.1 0)).homOfLE _),
        ρτ (t.1 0) (t.1 1) hab (𝒰.inter (𝒰.face t 2)) hW2ab
          (𝒰.inter_le_inter_face t 2) (hle 0 1) ρab2 τab hρab2 hτab,
        Category.assoc, ← Category.assoc ((Y (t.1 1)).homOfLE _),
        ρτ (t.1 1) (t.1 3) hbd (𝒰.inter (𝒰.face t 2)) hW2bc
          (𝒰.inter_le_inter_face t 2) (hle 1 3) ρbc2 τbd hρbc2 hτbd,
        Category.assoc, Scheme.homOfLE_ι]
    rw [eu, ev] at raw
    exact raw
  have H3 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) m3 m4 fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (t.1 3)) ((i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3)) Ue
      (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h3).toLinearMap ∘ₗ cs3 x) := by
    have raw := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat (RingHom.ker π) hI hsmall V ι hι hιI
      _ _ h3 _ _ fk Lk _ _ Ue _ hcs3'
    have hS : Spec.map (CommRingCat.ofHom h3.toRingHom) =
        Spec.map ((Y (t.1 0)).presheaf.map (homOfLE (hOm (t.1 0) (𝒰.inter_le_inter_face t 3))).op) := rfl
    have eu : Spec.map (CommRingCat.ofHom h3.toRingHom) ≫
        (hA3.isoSpec.inv ≫ ρac3.hom ≫ (O (t.1 2) (𝒰.inter (𝒰.face t 3))).ι) =
        (hOt.isoSpec.inv ≫ τac.hom) ≫ (O (t.1 2) (𝒰.inter t)).ι := by
      rw [hS, ← Category.assoc, specMap_res_comp_isoSpec_inv hA3 hOt (hOm (t.1 0) (𝒰.inter_le_inter_face t 3)),
        Category.assoc, ← Category.assoc ((Y (t.1 0)).homOfLE _),
        ρτ (t.1 0) (t.1 2) hac (𝒰.inter (𝒰.face t 3)) hW3ac
          (𝒰.inter_le_inter_face t 3) (hle 0 2) ρac3 τac hρac3 hτac,
        Category.assoc, Scheme.homOfLE_ι, Category.assoc]
    have ev : Spec.map (CommRingCat.ofHom h3.toRingHom) ≫
        (hA3.isoSpec.inv ≫ ρab3.hom ≫ ρbc3.hom ≫ (O (t.1 2) (𝒰.inter (𝒰.face t 3))).ι) =
        (hOt.isoSpec.inv ≫ τab.hom ≫ τbc.hom) ≫ (O (t.1 2) (𝒰.inter t)).ι := by
      rw [hS, ← Category.assoc, specMap_res_comp_isoSpec_inv hA3 hOt (hOm (t.1 0) (𝒰.inter_le_inter_face t 3)),
        Category.assoc, ← Category.assoc ((Y (t.1 0)).homOfLE _),
        ρτ (t.1 0) (t.1 1) hab (𝒰.inter (𝒰.face t 3)) hW3ab
          (𝒰.inter_le_inter_face t 3) (hle 0 1) ρab3 τab hρab3 hτab,
        Category.assoc, ← Category.assoc ((Y (t.1 1)).homOfLE _),
        ρτ (t.1 1) (t.1 2) hbc (𝒰.inter (𝒰.face t 3)) hW3bc
          (𝒰.inter_le_inter_face t 3) (hle 1 2) ρbc3 τbc hρbc3 hτbc,
        Category.assoc, Scheme.homOfLE_ι]
      simp only [Category.assoc]
    rw [eu, ev] at raw

    have fac := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_of_isPullback_of_comp_mono (RingHom.ker π) hI hsmall V ι
      Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) ((O (t.1 2) (𝒰.inter t)).ι)
      (hOt.isoSpec.inv ≫ τac.hom) (hOt.isoSpec.inv ≫ τab.hom ≫ τbc.hom) fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (t.1 2)) (i₀ ⁻¹ᵁ 𝒰.inter t) (i₀.preimage_mono (𝒰.inter_le t 2))
      ((i₀ ∣_ 𝒰.U (t.1 2)) ≫ g (t.1 2)) aWc hsqc Ue _ raw

    have G2 : aWc ≫ τcd.hom = aWd := by
      obtain ⟨γ, γ', hγ, hγ', hγφ⟩ := hφg (t.1 2) (t.1 3) hcd
      have hUcd : 𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3) ≤ 𝒰.U (t.1 2) := inf_le_left
      have hUcd' : 𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3) ≤ 𝒰.U (t.1 3) := inf_le_right
      have hA : aWc ≫ (Y (t.1 2)).homOfLE (hOm (t.1 2) (hle 2 3)) =
          (Ak.homOfLE (i₀.preimage_mono (hle 2 3)) ≫ (i₀ ∣_ (𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3)))) ≫ γ := by
        rw [← cancel_mono (O (t.1 2) (𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3))).ι]
        calc (aWc ≫ (Y (t.1 2)).homOfLE (hOm (t.1 2) (hle 2 3))) ≫ (O (t.1 2) (𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3))).ι
            = aWc ≫ (O (t.1 2) (𝒰.inter t)).ι := by rw [Category.assoc, Scheme.homOfLE_ι]
          _ = Ak.homOfLE (i₀.preimage_mono (𝒰.inter_le t 2)) ≫ (i₀ ∣_ 𝒰.U (t.1 2)) ≫ g (t.1 2) := haWcι
          _ = (Ak.homOfLE (i₀.preimage_mono (hle 2 3)) ≫ Ak.homOfLE (i₀.preimage_mono hUcd)) ≫
                (i₀ ∣_ 𝒰.U (t.1 2)) ≫ g (t.1 2) := by simp only [Scheme.homOfLE_homOfLE]
          _ = Ak.homOfLE (i₀.preimage_mono (hle 2 3)) ≫ ((i₀ ∣_ (𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3))) ≫ A₀.homOfLE hUcd) ≫
                g (t.1 2) := by rw [← resNat hUcd]; simp only [Category.assoc]
          _ = ((Ak.homOfLE (i₀.preimage_mono (hle 2 3)) ≫ (i₀ ∣_ (𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3)))) ≫ γ) ≫
                (O (t.1 2) (𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3))).ι := by simp only [Category.assoc, hγ]
      rw [← cancel_mono (O (t.1 3) (𝒰.inter t)).ι, haWdι]
      calc (aWc ≫ τcd.hom) ≫ (O (t.1 3) (𝒰.inter t)).ι
          = aWc ≫ (τcd.hom ≫ (Y (t.1 3)).homOfLE (hOm (t.1 3) (hle 2 3))) ≫ (O (t.1 3) (𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3))).ι := by
            simp only [Category.assoc, Scheme.homOfLE_ι]
        _ = (aWc ≫ (Y (t.1 2)).homOfLE (hOm (t.1 2) (hle 2 3))) ≫ (φ (t.1 2) (t.1 3) hcd).hom ≫
              (O (t.1 3) (𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3))).ι := by rw [hτcd]; simp only [Category.assoc]
        _ = (Ak.homOfLE (i₀.preimage_mono (hle 2 3)) ≫ (i₀ ∣_ (𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3)))) ≫ (γ ≫ (φ (t.1 2) (t.1 3) hcd).hom) ≫
              (O (t.1 3) (𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3))).ι := by rw [hA]; simp only [Category.assoc]
        _ = (Ak.homOfLE (i₀.preimage_mono (hle 2 3)) ≫ (i₀ ∣_ (𝒰.U (t.1 2) ⊓ 𝒰.U (t.1 3)))) ≫
              A₀.homOfLE hUcd' ≫ g (t.1 3) := by rw [hγφ, hγ']
        _ = Ak.homOfLE (i₀.preimage_mono (hle 2 3)) ≫ (Ak.homOfLE (i₀.preimage_mono hUcd') ≫ (i₀ ∣_ 𝒰.U (t.1 3))) ≫
              g (t.1 3) := by rw [resNat hUcd']; simp only [Category.assoc]
        _ = Ak.homOfLE (i₀.preimage_mono (𝒰.inter_le t 3)) ≫ (i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3) := by
            simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]

    have post := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq (RingHom.ker π) V ι
      Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) (τcd.hom ≫ (O (t.1 3) (𝒰.inter t)).ι)
      (hOt.isoSpec.inv ≫ τac.hom) (hOt.isoSpec.inv ≫ τab.hom ≫ τbc.hom) fk Lk
      (i₀ ⁻¹ᵁ 𝒰.inter t) (i₀ ⁻¹ᵁ 𝒰.U (t.1 3)) (i₀.preimage_mono (𝒰.inter_le t 3)) aWc ((i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3))
      (by rw [← Category.assoc aWc, G2, haWdι]) Ue _ fac
    rw [hm3d, hm4d]
    simpa only [Category.assoc] using post

  letI i0 : Algebra T' Γ(Y (t.1 1), O (t.1 1) (𝒰.inter (𝒰.face t 0))) := algebraOfHom (q (t.1 1)) (O (t.1 1) (𝒰.inter (𝒰.face t 0)))
  have hA0 : IsAffineOpen (O (t.1 1) (𝒰.inter (𝒰.face t 0))) := hOaff _ _ (haff (𝒰.face t 0)) (𝒰.inter_le (𝒰.face t 0) 0)
  have hσ₁0 : (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) (𝒰.face t 0)).isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (σ (𝒰.face t 0)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        Γ(Y (t.1 1), O (t.1 1) (𝒰.inter (𝒰.face t 0))) →ₐ[T']
          (ResidueField T') ⊗[T'] Γ(Y (t.1 1), O (t.1 1) (𝒰.inter (𝒰.face t 0)))).toRingHom) ≫ hA0.fromSpec =
      Ak.homOfLE (𝒰.comap_inter_le i₀ (𝒰.face t 0)) ≫ (i₀ ∣_ 𝒰.inter (𝒰.face t 0)) ≫
        A₀.homOfLE (V := 𝒰.U (t.1 1)) (𝒰.inter_le (𝒰.face t 0) 0) ≫ g (t.1 1) := hσ₁ (𝒰.face t 0)
  have hcs0' : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (t.1 1), O (t.1 1) (𝒰.inter (𝒰.face t 0)))
      (hA0.isoSpec.inv ≫ ρac0.hom ≫ (O (t.1 3) (𝒰.inter (𝒰.face t 0))).ι)
      (hA0.isoSpec.inv ≫ ρab0.hom ≫ ρbc0.hom ≫ (O (t.1 3) (𝒰.inter (𝒰.face t 0))).ι)
      fk Lk (i₀ ⁻¹ᵁ 𝒰.U (t.1 3)) ((i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3)) Ue cs0 := hcs0
  obtain ⟨θ₀, hθ₀d⟩ : ∃ θ : (↑(O (t.1 0) (𝒰.inter t)) : Scheme.{u}) ⟶ ↑(O (t.1 1) (𝒰.inter (𝒰.face t 0))),
      θ = τab.hom ≫ (Y (t.1 1)).homOfLE (hOm (t.1 1) (𝒰.inter_le_inter_face t 0)) := ⟨_, rfl⟩
  obtain ⟨h0r, hh0⟩ : ∃ h0r : CommRingCat.of Γ(Y (t.1 1), O (t.1 1) (𝒰.inter (𝒰.face t 0))) ⟶
      CommRingCat.of Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)), Spec.map h0r = hOt.isoSpec.inv ≫ θ₀ ≫ hA0.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hθ₀q : θ₀ ≫ (O (t.1 1) (𝒰.inter (𝒰.face t 0))).ι ≫ q (t.1 1) = (O (t.1 0) (𝒰.inter t)).ι ≫ q (t.1 0) := by
    rw [hθ₀d, Category.assoc, ← Category.assoc ((Y (t.1 1)).homOfLE _), Scheme.homOfLE_ι, τT _ _ hab (hle 0 1) τab hτab]
  have hh0T : CommRingCat.ofHom (algebraMap T' Γ(Y (t.1 1), O (t.1 1) (𝒰.inter (𝒰.face t 0)))) ≫ h0r =
      CommRingCat.ofHom (algebraMap T' Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hh0, ← fromSpec_comp_eq (q (t.1 1)) hA0, ← hιq, ← IsAffineOpen.isoSpec_inv_ι hA0]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hθ₀q]
  let h0 : Γ(Y (t.1 1), O (t.1 1) (𝒰.inter (𝒰.face t 0))) →ₐ[T'] Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) :=
    { toRingHom := h0r.hom
      commutes' := fun r => congrArg (fun φ : CommRingCat.of T' ⟶ _ => φ.hom r) hh0T }
  have hS0 : Spec.map (CommRingCat.ofHom h0.toRingHom) ≫ hA0.isoSpec.inv = hOt.isoSpec.inv ≫ θ₀ := by
    show Spec.map h0r ≫ _ = _
    rw [hh0]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have H0 : IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) m2 m4 fk Lk
      (i₀ ⁻¹ᵁ 𝒰.U (t.1 3)) ((i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3)) Ue
      (fun x => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h0).toLinearMap ∘ₗ cs0 x) := by
    have raw := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_flat (RingHom.ker π) hI hsmall V ι hι hιI
      _ _ h0 _ _ fk Lk _ _ Ue _ hcs0'
    have eu : Spec.map (CommRingCat.ofHom h0.toRingHom) ≫
        (hA0.isoSpec.inv ≫ ρac0.hom ≫ (O (t.1 3) (𝒰.inter (𝒰.face t 0))).ι) = m2 := by
      rw [hm2d, ← Category.assoc, hS0]
      rw [hθ₀d, Category.assoc, Category.assoc, ← Category.assoc ((Y (t.1 1)).homOfLE _),
        ρτ (t.1 1) (t.1 3) hbd (𝒰.inter (𝒰.face t 0)) hW0ac (𝒰.inter_le_inter_face t 0) (hle 1 3) ρac0 τbd hρac0 hτbd,
        Category.assoc, Scheme.homOfLE_ι]
    have ev : Spec.map (CommRingCat.ofHom h0.toRingHom) ≫
        (hA0.isoSpec.inv ≫ ρab0.hom ≫ ρbc0.hom ≫ (O (t.1 3) (𝒰.inter (𝒰.face t 0))).ι) = m4 := by
      rw [hm4d, ← Category.assoc, hS0]
      rw [hθ₀d, Category.assoc, Category.assoc, ← Category.assoc ((Y (t.1 1)).homOfLE _),
        ρτ (t.1 1) (t.1 2) hbc (𝒰.inter (𝒰.face t 0)) hW0ab (𝒰.inter_le_inter_face t 0) (hle 1 2) ρab0 τbc hρab0 hτbc,
        Category.assoc, ← Category.assoc ((Y (t.1 2)).homOfLE _),
        ρτ (t.1 2) (t.1 3) hcd (𝒰.inter (𝒰.face t 0)) hW0bc (𝒰.inter_le_inter_face t 0) (hle 2 3) ρbc0 τcd hρbc0 hτcd,
        Category.assoc, Scheme.homOfLE_ι]
    rw [eu, ev] at raw
    exact raw

  have hm1 : m1 ≫ q (t.1 3) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)))) := by
    rw [hm1d]; simp only [Category.assoc]; rw [τT _ _ had (hle 0 3) τad hτad]; exact hιq
  have hm2 : m2 ≫ q (t.1 3) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)))) := by
    rw [hm2d]; simp only [Category.assoc]; rw [τT _ _ hbd (hle 1 3) τbd hτbd, τT _ _ hab (hle 0 1) τab hτab]; exact hιq
  have hm3 : m3 ≫ q (t.1 3) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)))) := by
    rw [hm3d]; simp only [Category.assoc]; rw [τT _ _ hcd (hle 2 3) τcd hτcd, τT _ _ hac (hle 0 2) τac hτac]; exact hιq
  have hm4 : m4 ≫ q (t.1 3) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)))) := by
    rw [hm4d]; simp only [Category.assoc]
    rw [τT _ _ hcd (hle 2 3) τcd hτcd, τT _ _ hbc (hle 1 2) τbc hτbc, τT _ _ hab (hle 0 1) τab hτab]; exact hιq

  have haWd : IsPullback ((i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3)) ((i₀ ⁻¹ᵁ 𝒰.U (t.1 3)).ι ≫ fk) (q (t.1 3))
      (Spec.map (CommRingCat.ofHom (residue T'))) := by
    have h1 : IsPullback (i₀ ∣_ 𝒰.U (t.1 3)) ((i₀ ⁻¹ᵁ 𝒰.U (t.1 3)).ι ≫ fk) ((𝒰.U (t.1 3)).ι ≫ f₀)
        (Spec.map (CommRingCat.ofHom ρ)) :=
      (isPullback_morphismRestrict i₀ (𝒰.U (t.1 3))).paste_vert hi₀
    have h2 := h1.paste_horiz (hg (t.1 3))
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ] at h2

  have h12 := modI_of_via _ V ι _ H2
  have h24 := modI_of_via _ V ι _ H0
  have h13 := modI_of_via _ V ι _ H1
  have h34 := modI_of_via _ V ι _ H3

  obtain ⟨c14, hc14⟩ := AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia (RingHom.ker π) hI hsmall V ι hι hιI
    Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) (q (t.1 3)) m1 hm1 fk Lk (i₀ ⁻¹ᵁ 𝒰.U (t.1 3)) ((i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3)) haWd
    Ue hUe e₁ he₁ m4 hm4 (h12.trans h24)
  have e124 := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_add (RingHom.ker π) hI hsmall V ι hι hιI
    Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) (q (t.1 3)) m1 m2 m4 hm1 hm2 hm4 h12 h24 fk Lk
    (i₀ ⁻¹ᵁ 𝒰.U (t.1 3)) ((i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3)) haWd Ue hUe e₁ he₁ _ _ _ H2 H0 hc14
  have e134 := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_add (RingHom.ker π) hI hsmall V ι hι hιI
    Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)) (q (t.1 3)) m1 m3 m4 hm1 hm3 hm4 h13 h34 fk Lk
    (i₀ ⁻¹ᵁ 𝒰.U (t.1 3)) ((i₀ ∣_ 𝒰.U (t.1 3)) ≫ g (t.1 3)) haWd Ue hUe e₁ he₁ _ _ _ H1 H3 hc14

  have hkey : (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h0) (cs0 a₀ ξ)
      + (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h2) (cs2 a₀ ξ)
      = (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h1) (cs1 a₀ ξ)
      + (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h3) (cs3 a₀ ξ) := by
    have e1 := LinearMap.congr_fun (congrFun e124 a₀) ξ
    have e2 := LinearMap.congr_fun (congrFun e134 a₀) ξ
    simp only [Pi.add_apply, LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply] at e1 e2
    calc _ = _ := add_comm _ _
      _ = _ := e1.symm
      _ = _ := e2

  have S0 : ∀ z, σ t (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h0 z) =
      (Ak.presheaf.map (homOfLE ((𝒰.comap i₀).inter_le_inter_face t 0)).op).hom (σ (𝒰.face t 0) z) := by
    refine AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
      (q (t.1 1)) (q (t.1 0)) fk (O (t.1 1) (𝒰.inter (𝒰.face t 0))) hA0 (O (t.1 0) (𝒰.inter t)) hOt
      ((𝒰.comap i₀).inter (𝒰.face t 0)) ((𝒰.comap i₀).inter t)
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) (𝒰.face t 0))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) t)
      ((𝒰.comap i₀).inter_le_inter_face t 0) _ h0 (σ (𝒰.face t 0)) (σ t) hσ₁0
      (hσ₂ (𝒰.face t 0)) (hσ₂ t) ?_

    obtain ⟨γ, γ', hγ, hγ', hγφ⟩ := hφg (t.1 0) (t.1 1) hab
    have hUab' : 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1) ≤ 𝒰.U (t.1 1) := inf_le_right
    have hX := CocAux.reassoc3 (hσ₁ t)
    have hBgen : ∀ {X : (↑((𝒰.comap i₀).inter t) : Scheme.{u}) ⟶ Spec (Γ(Y (t.1 0), O (t.1 0) (𝒰.inter t)))},
        X ≫ hOt.fromSpec = Ak.homOfLE (𝒰.comap_inter_le i₀ t) ≫ (i₀ ∣_ 𝒰.inter t) ≫ A₀.homOfLE (𝒰.inter_le t 0) ≫ g (t.1 0) →
        X ≫ hOt.isoSpec.inv ≫ (Y (t.1 0)).homOfLE (hOm (t.1 0) (hle 0 1)) =
          Ak.homOfLE ((𝒰.comap_inter_le i₀ t).trans (i₀.preimage_mono (hle 0 1))) ≫
            (i₀ ∣_ (𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))) ≫ γ := by
      intro X hX'
      rw [← cancel_mono (O (t.1 0) (𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))).ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι]
      rw [hX', hγ, resNat_assoc, resNat_assoc]
      simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]
    have key := congrArg (fun f => f ≫ (φ (t.1 0) (t.1 1) hab).hom ≫ (O (t.1 1) (𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))).ι) (hBgen hX)
    simp only [Category.assoc] at key
    rw [← IsAffineOpen.isoSpec_inv_ι hA0, ← Category.assoc (Spec.map _) hA0.isoSpec.inv, hS0, hθ₀d]
    simp only [Category.assoc]
    rw [Scheme.homOfLE_ι, ← Scheme.homOfLE_ι (Y (t.1 1)) (hOm (t.1 1) (hle 0 1)), ← Category.assoc τab.hom, hτab]
    simp only [Category.assoc]
    rw [key, ← Category.assoc γ, hγφ, hγ', resNat_assoc, resNat_assoc]
    simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]
  have S1 : ∀ z, σ t (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h1 z) =
      (Ak.presheaf.map (homOfLE ((𝒰.comap i₀).inter_le_inter_face t 1)).op).hom (σ (𝒰.face t 1) z) := by
    refine AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
      (q (t.1 0)) (q (t.1 0)) fk (O (t.1 0) (𝒰.inter (𝒰.face t 1))) hA1 (O (t.1 0) (𝒰.inter t)) hOt
      ((𝒰.comap i₀).inter (𝒰.face t 1)) ((𝒰.comap i₀).inter t)
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) (𝒰.face t 1))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) t)
      ((𝒰.comap i₀).inter_le_inter_face t 1) _ h1 (σ (𝒰.face t 1)) (σ t) (hσ₁ (𝒰.face t 1))
      (hσ₂ (𝒰.face t 1)) (hσ₂ t) ?_
    have hS : Spec.map (CommRingCat.ofHom h1.toRingHom) =
        Spec.map ((Y (t.1 0)).presheaf.map (homOfLE (hOm (t.1 0) (𝒰.inter_le_inter_face t 1))).op) := rfl
    rw [hS, IsAffineOpen.map_fromSpec hA1 hOt]
    refine (hσ₁ t).trans ?_
    show Ak.homOfLE _ ≫ (i₀ ∣_ 𝒰.inter t) ≫ A₀.homOfLE _ ≫ g (t.1 0) =
      Ak.homOfLE _ ≫ Ak.homOfLE _ ≫ (i₀ ∣_ 𝒰.inter (𝒰.face t 1)) ≫ A₀.homOfLE _ ≫ g (t.1 0)
    rw [resNat_assoc, resNat_assoc]
    simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]
  have S2 : ∀ z, σ t (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h2 z) =
      (Ak.presheaf.map (homOfLE ((𝒰.comap i₀).inter_le_inter_face t 2)).op).hom (σ (𝒰.face t 2) z) := by
    refine AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
      (q (t.1 0)) (q (t.1 0)) fk (O (t.1 0) (𝒰.inter (𝒰.face t 2))) hA2 (O (t.1 0) (𝒰.inter t)) hOt
      ((𝒰.comap i₀).inter (𝒰.face t 2)) ((𝒰.comap i₀).inter t)
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) (𝒰.face t 2))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) t)
      ((𝒰.comap i₀).inter_le_inter_face t 2) _ h2 (σ (𝒰.face t 2)) (σ t) (hσ₁ (𝒰.face t 2))
      (hσ₂ (𝒰.face t 2)) (hσ₂ t) ?_
    have hS : Spec.map (CommRingCat.ofHom h2.toRingHom) =
        Spec.map ((Y (t.1 0)).presheaf.map (homOfLE (hOm (t.1 0) (𝒰.inter_le_inter_face t 2))).op) := rfl
    rw [hS, IsAffineOpen.map_fromSpec hA2 hOt]
    refine (hσ₁ t).trans ?_
    show Ak.homOfLE _ ≫ (i₀ ∣_ 𝒰.inter t) ≫ A₀.homOfLE _ ≫ g (t.1 0) =
      Ak.homOfLE _ ≫ Ak.homOfLE _ ≫ (i₀ ∣_ 𝒰.inter (𝒰.face t 2)) ≫ A₀.homOfLE _ ≫ g (t.1 0)
    rw [resNat_assoc, resNat_assoc]
    simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]
  have S3 : ∀ z, σ t (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h3 z) =
      (Ak.presheaf.map (homOfLE ((𝒰.comap i₀).inter_le_inter_face t 3)).op).hom (σ (𝒰.face t 3) z) := by
    refine AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
      (q (t.1 0)) (q (t.1 0)) fk (O (t.1 0) (𝒰.inter (𝒰.face t 3))) hA3 (O (t.1 0) (𝒰.inter t)) hOt
      ((𝒰.comap i₀).inter (𝒰.face t 3)) ((𝒰.comap i₀).inter t)
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) (𝒰.face t 3))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) t)
      ((𝒰.comap i₀).inter_le_inter_face t 3) _ h3 (σ (𝒰.face t 3)) (σ t) (hσ₁ (𝒰.face t 3))
      (hσ₂ (𝒰.face t 3)) (hσ₂ t) ?_
    have hS : Spec.map (CommRingCat.ofHom h3.toRingHom) =
        Spec.map ((Y (t.1 0)).presheaf.map (homOfLE (hOm (t.1 0) (𝒰.inter_le_inter_face t 3))).op) := rfl
    rw [hS, IsAffineOpen.map_fromSpec hA3 hOt]
    refine (hσ₁ t).trans ?_
    show Ak.homOfLE _ ≫ (i₀ ∣_ 𝒰.inter t) ≫ A₀.homOfLE _ ≫ g (t.1 0) =
      Ak.homOfLE _ ≫ Ak.homOfLE _ ≫ (i₀ ∣_ 𝒰.inter (𝒰.face t 3)) ≫ A₀.homOfLE _ ≫ g (t.1 0)
    rw [resNat_assoc, resNat_assoc]
    simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]

  rw [Fin.sum_univ_four]
  simp only [OModulePresheaf.unit_res_apply]
  erw [← hp0 a₀ ξ, ← hp1 a₀ ξ, ← hp2 a₀ ξ, ← hp3 a₀ ξ]
  rw [← S0, ← S1, ← S2, ← S3]
  exact CocAux.alt_sum_eq_zero (σ t) (fun x y => (σ t).map_add x y) _ _ _ _ hkey

end S_AlgebraicGeometry_SmallExtension_d_two_cochain_eq_zero_of_isTangentCoordsOfPairAtVia_pin
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_d_two_cochain_eq_zero_of_isTangentCoordsOfPairAtVia_pin (solution)
