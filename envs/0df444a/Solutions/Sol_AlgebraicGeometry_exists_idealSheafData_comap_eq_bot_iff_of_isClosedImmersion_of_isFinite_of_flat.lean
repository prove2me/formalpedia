-- Prove2me | solution 1 for AlgebraicGeometry.exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/726b986c-c37a-55db-83a2-ef23c4e0fb5b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app Scheme.IdealSheafData.le_ofIdeals_iff Scheme.Hom.map_appLE Spec.map_comp_assoc Scheme.IdealSheafData.map_bot Scheme.Hom exists_basicOpen_le_affine_inter Scheme.Hom.appLE_comp_appLE iSup_affineOpens_eq_top IsFinite Scheme.preimage_basicOpen IsAffineOpen.SpecMap_appLE_fromSpec IsAffineOpen.fromSpec_preimage_self Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.IdealSheafData.le_map_iff_comap_le Scheme.Hom.comp_appLE Flat IsFinite.finite_app IsClosedImmersion Scheme.Hom.comp_app Scheme.Hom.ker IsAffineOpen IsAffineOpen.fromSpec_app_of_le Scheme.Hom.ker_apply LocallyOfFinitePresentation IsAffineHom Scheme.Hom.appLE Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app"
namespace KMKeyLemmaSol
p2m_open "AlgebraicGeometry"

section Algebra

variable {A B : Type*} [CommRing A] [CommRing B]

def IsFunctional (φ : A →+* B) (ψ : B →+ A) : Prop :=
  ∀ (a : A) (b : B), ψ (φ a * b) = a * ψ b

def contentIdeal (φ : A →+* B) (I : Ideal B) : Ideal A :=
  Ideal.span {a | ∃ b ∈ I, ∃ ψ : B →+ A, IsFunctional φ ψ ∧ ψ b = a}

theorem mem_contentIdeal_of {φ : A →+* B} {I : Ideal B} {b : B} (hb : b ∈ I) {ψ : B →+ A}
    (hψ : IsFunctional φ ψ) : ψ b ∈ contentIdeal φ I :=
  Ideal.subset_span ⟨b, hb, ψ, hψ, rfl⟩

theorem isFunctional_of_linearMap [Algebra A B] (ψ : B →ₗ[A] A) :
    IsFunctional (algebraMap A B) ψ.toAddMonoidHom := by
  intro a b
  change ψ (algebraMap A B a * b) = a * ψ b
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

def IsFunctional.toLinearMap [Algebra A B] {ψ : B →+ A} (hψ : IsFunctional (algebraMap A B) ψ) :
    B →ₗ[A] A where
  toFun := ψ
  map_add' := ψ.map_add
  map_smul' a b := by rw [Algebra.smul_def, hψ, RingHom.id_apply, smul_eq_mul]

@[scoped simp] theorem IsFunctional.toLinearMap_apply [Algebra A B] {ψ : B →+ A}
    (hψ : IsFunctional (algebraMap A B) ψ) (b : B) : hψ.toLinearMap b = ψ b := rfl

p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.AlgebraicGeometry.KMKeyLemmaSol.IsFunctional"
theorem mem_contentIdeal_of_linearMap [Algebra A B] {I : Ideal B} {b : B} (hb : b ∈ I)
    (ψ : B →ₗ[A] A) : ψ b ∈ contentIdeal (algebraMap A B) I :=
  mem_contentIdeal_of hb (isFunctional_of_linearMap ψ)

theorem IsFunctional.comp_mulLeft {φ : A →+* B} {ψ : B →+ A} (hψ : IsFunctional φ ψ) (c : B) :
    IsFunctional φ (ψ.comp (AddMonoidHom.mulLeft c)) := by
  intro a b
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft]
  rw [mul_left_comm, hψ]

theorem map_eq_zero_of_forall_contentIdeal [Algebra A B] [Module.Projective A B]
    {C : Type*} [CommRing C] (χ : B →+* C) (I : Ideal B)
    (hχ : ∀ a ∈ contentIdeal (algebraMap A B) I, χ (algebraMap A B a) = 0) {b : B} (hb : b ∈ I) :
    χ b = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective A B›
  have hb' : Finsupp.linearCombination A id (s b) = b := by
    simpa using LinearMap.congr_fun hs b
  rw [← hb', Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [id, Algebra.smul_def, map_mul]
  have hmem : s b p ∈ contentIdeal (algebraMap A B) I :=
    mem_contentIdeal_of_linearMap hb ((Finsupp.lapply p).comp s)
  rw [hχ _ hmem, zero_mul]

theorem algebraMap_eq_zero_of_tmul_eq_zero [Algebra A B] {A' : Type*} [CommRing A'] [Algebra A A']
    {b : B} (h : (1 : A') ⊗ₜ[A] b = 0) (ψ : B →ₗ[A] A) : algebraMap A A' (ψ b) = 0 := by
  let μ : A' ⊗[A] B →ₗ[A] A' :=
    LinearMap.mul' A A' ∘ₗ LinearMap.lTensor A' ((Algebra.linearMap A A') ∘ₗ ψ)
  have hμ : μ ((1 : A') ⊗ₜ[A] b) = algebraMap A A' (ψ b) := by
    simp [μ, LinearMap.mul'_apply]
  rw [← hμ, h, map_zero]

end Algebra
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.AlgebraicGeometry.KMKeyLemmaSol.IsFunctional"

section Localization

variable {A B Aᵣ Bᵣ : Type*} [CommRing A] [CommRing B] [CommRing Aᵣ] [CommRing Bᵣ]
  [Algebra A Aᵣ] [Algebra B Bᵣ]

theorem contentIdeal_map_localization (r : A) [IsLocalization.Away r Aᵣ] (φ : A →+* B)
    [IsLocalization.Away (φ r) Bᵣ] (φᵣ : Aᵣ →+* Bᵣ)
    (hsq : φᵣ.comp (algebraMap A Aᵣ) = (algebraMap B Bᵣ).comp φ)
    (hfin : φ.Finite) (hfp : φ.FinitePresentation) (I : Ideal B) :
    (contentIdeal φ I).map (algebraMap A Aᵣ) = contentIdeal φᵣ (I.map (algebraMap B Bᵣ)) := by
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra Aᵣ Bᵣ := φᵣ.toAlgebra
  letI : Algebra A Bᵣ := ((algebraMap B Bᵣ).comp φ).toAlgebra
  haveI : IsScalarTower A B Bᵣ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A Aᵣ Bᵣ := IsScalarTower.of_algebraMap_eq (fun a => by
    change ((algebraMap B Bᵣ).comp φ) a = φᵣ (algebraMap A Aᵣ a)
    rw [← hsq]; rfl)
  haveI : Module.Finite A B := hfin
  haveI : Algebra.FinitePresentation A B := hfp
  haveI : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_finite_of_finitePresentation A B

  have hsub : Algebra.algebraMapSubmonoid B (Submonoid.powers r) = Submonoid.powers (φ r) := by
    change Submonoid.map (algebraMap A B) (Submonoid.powers r) = _
    rw [Submonoid.map_powers]; rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers r)) Bᵣ := by
    rw [hsub]; infer_instance
  let fB : B →ₗ[A] Bᵣ := (IsScalarTower.toAlgHom A B Bᵣ).toLinearMap
  have hfB : ∀ b, fB b = algebraMap B Bᵣ b := fun _ => rfl
  haveI : IsLocalizedModule (Submonoid.powers r) fB := inferInstance
  let fA : A →ₗ[A] Aᵣ := Algebra.linearMap A Aᵣ
  haveI : IsLocalizedModule (Submonoid.powers r) fA := inferInstance
  have hφᵣ : ∀ a', algebraMap Aᵣ Bᵣ a' = φᵣ a' := fun _ => rfl
  apply le_antisymm
  ·
    rw [Ideal.map_le_iff_le_comap]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨b, hb, ψ, hψ, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    have hψ' : IsFunctional (algebraMap A B) ψ := hψ
    let ψl : B →ₗ[A] A := hψ'.toLinearMap
    let ψᵣ : Bᵣ →ₗ[Aᵣ] Aᵣ :=
      (IsLocalizedModule.map (Submonoid.powers r) fB fA ψl).extendScalarsOfIsLocalization
        (Submonoid.powers r) Aᵣ
    have hval : ψᵣ (algebraMap B Bᵣ b) = algebraMap A Aᵣ (ψ b) := by
      change (IsLocalizedModule.map (Submonoid.powers r) fB fA ψl) (fB b) = fA (ψl b)
      exact IsLocalizedModule.map_apply (Submonoid.powers r) fB fA ψl b
    rw [← hval]
    refine mem_contentIdeal_of (Ideal.mem_map_of_mem _ hb) (ψ := ψᵣ.toAddMonoidHom) ?_
    intro a' y
    change ψᵣ (φᵣ a' * y) = a' * ψᵣ y
    rw [← hφᵣ, ← Algebra.smul_def, map_smul, smul_eq_mul]
  ·
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨y, hy, ψ', hψ', rfl⟩
    rw [SetLike.mem_coe]

    revert ψ'
    refine Submodule.span_induction (p := fun y _ => ∀ ψ' : Bᵣ →+ Aᵣ, IsFunctional φᵣ ψ' →
      ψ' y ∈ (contentIdeal φ I).map (algebraMap A Aᵣ)) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨x, hx, rfl⟩ ψ' hψ'
      have hψ'' : IsFunctional (algebraMap Aᵣ Bᵣ) ψ' := hψ'
      let ψl : Bᵣ →ₗ[Aᵣ] Aᵣ := hψ''.toLinearMap
      let χ : B →ₗ[A] Aᵣ := (ψl.restrictScalars A) ∘ₗ fB
      obtain ⟨χ₀, s, hχ⟩ :=
        Module.FinitePresentation.exists_lift_of_isLocalizedModule (Submonoid.powers r) fA χ
      have hx' : algebraMap A Aᵣ (χ₀ x) = algebraMap A Aᵣ (s : A) * ψ' (algebraMap B Bᵣ x) := by
        have := LinearMap.congr_fun hχ x
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply] at this
        change algebraMap A Aᵣ (χ₀ x) = (s : A) • ψl (fB x) at this
        rw [this, Algebra.smul_def]
        rfl
      have hunit : IsUnit (algebraMap A Aᵣ (s : A)) :=
        IsLocalization.map_units Aᵣ s
      have hmem : algebraMap A Aᵣ (χ₀ x) ∈ (contentIdeal φ I).map (algebraMap A Aᵣ) :=
        Ideal.mem_map_of_mem _
          (mem_contentIdeal_of hx (ψ := χ₀.toAddMonoidHom) (isFunctional_of_linearMap χ₀))
      have : ψ' (algebraMap B Bᵣ x) =
          ↑hunit.unit⁻¹ * algebraMap A Aᵣ (χ₀ x) := by
        rw [hx', ← mul_assoc, IsUnit.val_inv_mul, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ hmem
    · intro ψ' _; simp
    · intro y z _ _ hy hz ψ' hψ'
      rw [map_add]; exact Ideal.add_mem _ (hy ψ' hψ') (hz ψ' hψ')
    · intro c y _ hy ψ' hψ'
      have := hy (ψ'.comp (AddMonoidHom.mulLeft c)) (hψ'.comp_mulLeft c)
      simpa [smul_eq_mul] using this

end Localization
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.AlgebraicGeometry.KMKeyLemmaSol.IsFunctional"

section SchemeLevel

variable {Z D T : Scheme.{u}} (i : Z ⟶ D) [IsClosedImmersion i] (g : D ⟶ T)

abbrev gInv [IsAffineHom g] (U : T.affineOpens) : D.affineOpens := ⟨g ⁻¹ᵁ U, U.2.preimage g⟩

@[scoped simp] theorem coe_gInv [IsAffineHom g] (U : T.affineOpens) : (gInv g U : D.Opens) = g ⁻¹ᵁ U := rfl

def contentAt (U : T.affineOpens) : Ideal Γ(T, U) :=
  contentIdeal (g.app U).hom (RingHom.ker (i.app (g ⁻¹ᵁ U)).hom)

omit [IsClosedImmersion i] in

theorem contentIdeal_appLE_congr (U : T.Opens) {V₁ V₂ : D.Opens} (e : V₁ = V₂) (h₁ : V₁ ≤ g ⁻¹ᵁ U) :
    contentIdeal (g.appLE U V₁ h₁).hom (RingHom.ker (i.app V₁).hom) =
      contentIdeal (g.appLE U V₂ (e ▸ h₁)).hom (RingHom.ker (i.app V₂).hom) := by
  subst e; rfl

theorem contentAt_map_basicOpen [IsFinite g] [LocallyOfFinitePresentation g]
    (U : T.affineOpens) (r : Γ(T, U)) :
    (contentAt i g U).map (T.presheaf.map (homOfLE <| T.basicOpen_le r).op).hom =
      contentAt i g (T.affineBasicOpen r) := by

  haveI := U.2.isLocalization_basicOpen r
  haveI : IsLocalization.Away ((g.app U).hom r) Γ(D, D.basicOpen ((g.app U).hom r)) :=
    (U.2.preimage g).isLocalization_basicOpen ((g.app U).hom r)
  have e : D.basicOpen ((g.app U).hom r) = g ⁻¹ᵁ T.basicOpen r := (Scheme.preimage_basicOpen g r).symm

  let φᵣ := (g.appLE (T.basicOpen r) (D.basicOpen ((g.app U).hom r)) e.le).hom
  have hsq : φᵣ.comp (algebraMap Γ(T, U) Γ(T, T.basicOpen r)) =
      (algebraMap Γ(D, g ⁻¹ᵁ U) Γ(D, D.basicOpen ((g.app U).hom r))).comp (g.app U).hom := by
    change (T.presheaf.map (homOfLE <| T.basicOpen_le r).op ≫
        g.appLE (T.basicOpen r) (D.basicOpen ((g.app U).hom r)) e.le).hom =
      (g.app U ≫ D.presheaf.map (homOfLE <| D.basicOpen_le ((g.app U).hom r)).op).hom
    rw [Scheme.Hom.map_appLE]
    rfl
  have hfin : (g.app U).hom.Finite := IsFinite.finite_app g U U.2
  have hfp : (g.app U).hom.FinitePresentation := by
    have := g.finitePresentation_appLE U.2 (U.2.preimage g) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  have ALG := contentIdeal_map_localization r (g.app U).hom φᵣ hsq hfin hfp
    (RingHom.ker (i.app (g ⁻¹ᵁ U)).hom)

  have hI : (RingHom.ker (i.app (g ⁻¹ᵁ U)).hom).map
      (algebraMap Γ(D, g ⁻¹ᵁ U) Γ(D, D.basicOpen ((g.app U).hom r))) =
      RingHom.ker (i.app (D.basicOpen ((g.app U).hom r))).hom := by
    have := i.ker.map_ideal_basicOpen (gInv g U) ((g.app U).hom r)
    rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at this
    exact this
  rw [hI] at ALG
  refine ALG.trans ?_

  change contentIdeal (g.appLE (T.basicOpen r) (D.basicOpen ((g.app U).hom r)) e.le).hom _ = _
  rw [contentIdeal_appLE_congr i g (T.basicOpen r) e e.le, Scheme.Hom.appLE_eq_app]
  rfl

def contentSheaf [IsFinite g] [LocallyOfFinitePresentation g] : T.IdealSheafData :=
  ⟨contentAt i g, contentAt_map_basicOpen i g, _, rfl⟩

@[scoped simp] theorem contentSheaf_ideal [IsFinite g] [LocallyOfFinitePresentation g] (U : T.affineOpens) :
    (contentSheaf i g).ideal U = contentAt i g U := rfl

theorem comap_eq_bot_iff_forall_le_ker {X Y : Scheme.{u}} (J : Y.IdealSheafData) (f : X ⟶ Y) :
    J.comap f = ⊥ ↔ ∀ U : Y.affineOpens, J.ideal U ≤ RingHom.ker (f.app U).hom := by
  rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_bot,
    Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
  rfl

theorem ker_comap_eq_bot_iff_forall_le_ker {X : Scheme.{u}} (f : X ⟶ D) :
    i.ker.comap f = ⊥ ↔
      ∀ V : D.affineOpens, RingHom.ker (i.app V).hom ≤ RingHom.ker (f.app V).hom := by
  rw [comap_eq_bot_iff_forall_le_ker]
  refine forall_congr' fun V => ?_
  rw [Scheme.Hom.ker_apply]

section Forward

variable [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] {T' : Scheme.{u}} (h : T' ⟶ T)

omit [IsClosedImmersion i] in

theorem fst_app_eq_zero_of_mem_ker (hJ : ∀ U : T.affineOpens, contentAt i g U ≤ RingHom.ker (h.app U).hom)
    (U : T.affineOpens) {b : Γ(D, g ⁻¹ᵁ U)} (hb : b ∈ RingHom.ker (i.app (g ⁻¹ᵁ U)).hom) :
    (pullback.fst g h).app (g ⁻¹ᵁ U) b = 0 := by
  letI : Algebra Γ(T, U) Γ(D, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
  haveI : Module.Finite Γ(T, U) Γ(D, g ⁻¹ᵁ U) := IsFinite.finite_app g U U.2
  haveI : Module.Flat Γ(T, U) Γ(D, g ⁻¹ᵁ U) := by
    have := g.flat_appLE U.2 (U.2.preimage g) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  haveI : Algebra.FinitePresentation Γ(T, U) Γ(D, g ⁻¹ᵁ U) := by
    have := g.finitePresentation_appLE U.2 (U.2.preimage g) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  haveI : Module.FinitePresentation Γ(T, U) Γ(D, g ⁻¹ᵁ U) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  haveI : Module.Projective Γ(T, U) Γ(D, g ⁻¹ᵁ U) :=
    Module.Flat.projective_of_finitePresentation (R := Γ(T, U)) (M := Γ(D, g ⁻¹ᵁ U))
  refine map_eq_zero_of_forall_contentIdeal (A := Γ(T, U)) ((pullback.fst g h).app (g ⁻¹ᵁ U)).hom _ ?_ hb
  intro a ha
  change ((g.app U ≫ (pullback.fst g h).app (g ⁻¹ᵁ U))) a = 0
  rw [← Scheme.Hom.comp_app, Scheme.Hom.congr_app (pullback.condition (f := g) (g := h)) U,
    Scheme.Hom.comp_app]
  change (pullback g h).presheaf.map _ ((pullback.snd g h).app _ (h.app U a)) = 0
  rw [show h.app U a = 0 from hJ U ha, map_zero, map_zero]

theorem fst_app_eq_zero_of_le (hJ : ∀ U : T.affineOpens, contentAt i g U ≤ RingHom.ker (h.app U).hom)
    (U : T.affineOpens) (W : D.affineOpens) (hW : (W : D.Opens) ≤ g ⁻¹ᵁ U)
    {c : Γ(D, W)} (hc : c ∈ RingHom.ker (i.app W).hom) :
    (pullback.fst g h).app W c = 0 := by
  have hIW : RingHom.ker (i.app W).hom =
      (RingHom.ker (i.app (g ⁻¹ᵁ U)).hom).map (D.presheaf.map (homOfLE hW).op).hom := by
    have := i.ker.map_ideal (U := W) (V := gInv g U) hW
    rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at this
    exact this.symm
  rw [hIW] at hc
  have hle : (RingHom.ker (i.app (g ⁻¹ᵁ U)).hom).map (D.presheaf.map (homOfLE hW).op).hom ≤
      RingHom.ker ((pullback.fst g h).app W).hom := by
    refine Ideal.map_le_iff_le_comap.mpr fun t ht => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (D.presheaf.map (homOfLE hW).op ≫ (pullback.fst g h).app W) t = 0
    rw [(pullback.fst g h).naturality]
    change (pullback g h).presheaf.map _ ((pullback.fst g h).app (g ⁻¹ᵁ U) t) = 0
    rw [fst_app_eq_zero_of_mem_ker i g h hJ U ht, map_zero]
  exact hle hc

theorem forall_le_ker_fst (hJ : ∀ U : T.affineOpens, contentAt i g U ≤ RingHom.ker (h.app U).hom)
    (V : D.affineOpens) : RingHom.ker (i.app V).hom ≤ RingHom.ker ((pullback.fst g h).app V).hom := by
  intro b hb
  rw [RingHom.mem_ker]
  refine TopCat.Presheaf.IsSheaf.section_ext (pullback g h).IsSheaf
    (U := .op ((pullback.fst g h) ⁻¹ᵁ (V : D.Opens))) (t := 0) ?_
  intro x hx

  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top T).ge (Set.mem_univ (g.base ((pullback.fst g h).base x))))
  obtain ⟨f, f', e, hyf⟩ := exists_basicOpen_le_affine_inter V.2 (U.2.preimage g)
    ((pullback.fst g h).base x) ⟨hx, hU⟩
  refine ⟨(pullback.fst g h) ⁻¹ᵁ D.basicOpen f, fun y hy => D.basicOpen_le f hy, hyf, ?_⟩
  rw [map_zero]
  change (pullback.fst g h).appLE V ((pullback.fst g h) ⁻¹ᵁ D.basicOpen f)
    (fun y hy => D.basicOpen_le f hy) b = 0
  rw [← Scheme.Hom.map_appLE (pullback.fst g h) le_rfl (homOfLE (D.basicOpen_le f)).op,
    Scheme.Hom.appLE_eq_app, CommRingCat.comp_apply]
  refine fst_app_eq_zero_of_le i g h hJ U ⟨D.basicOpen f, V.2.basicOpen f⟩
    (by change D.basicOpen f ≤ _; rw [e]; exact D.basicOpen_le f') ?_

  have := i.ker.ideal_le_comap_ideal (U := D.affineBasicOpen f) (V := V) (D.basicOpen_le f)
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at this
  exact this hb

end Forward
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.AlgebraicGeometry.KMKeyLemmaSol.IsFunctional"

section Backward

variable [IsFinite g] {T' : Scheme.{u}} (h : T' ⟶ T)

theorem appLE_SpecMap_comp_fromSpec {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    {R : CommRingCat.{u}} (f : Γ(X, V) ⟶ R) (e : ⊤ ≤ (Spec.map f ≫ hV.fromSpec) ⁻¹ᵁ V) :
    (Spec.map f ≫ hV.fromSpec).appLE V ⊤ e = f ≫ (Scheme.ΓSpecIso R).inv := by
  have e₁ : (⊤ : (Spec Γ(X, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := by
    rw [IsAffineOpen.fromSpec_preimage_self]
  have hf : hV.fromSpec.appLE V ⊤ e₁ = (Scheme.ΓSpecIso Γ(X, V)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_of_le _ V le_rfl]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show (homOfLE (le_refl V)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [show ((homOfLE le_top).op ≫ (homOfLE e₁).op :
        Opposite.op (⊤ : (Spec Γ(X, V)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hs : (Spec.map f).appLE ⊤ ⊤ le_rfl = (Spec.map f).appTop := Scheme.Hom.appLE_eq_app _
  rw [← Scheme.Hom.appLE_comp_appLE _ _ V ⊤ ⊤ e₁ le_rfl, hf, hs, ← Scheme.ΓSpecIso_inv_naturality]

theorem apply_eq_zero_of_lift {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    {R : CommRingCat.{u}} (f : Γ(X, V) ⟶ R) {P : Scheme.{u}} (π : P ⟶ X) (θ : Spec R ⟶ P)
    (hθ : θ ≫ π = Spec.map f ≫ hV.fromSpec) {b : Γ(X, V)} (hb : π.app V b = 0) : f b = 0 := by
  have htop : (⊤ : (Spec R).Opens) ≤ (Spec.map f ≫ hV.fromSpec) ⁻¹ᵁ V := by
    change ⊤ ≤ Spec.map f ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ V)
    rw [IsAffineOpen.fromSpec_preimage_self]
    exact le_rfl
  have h1 : (Spec.map f ≫ hV.fromSpec).appLE V ⊤ htop b = 0 := by
    have key : ∀ (q : Spec R ⟶ X) (_ : q = Spec.map f ≫ hV.fromSpec) (hle : ⊤ ≤ q ⁻¹ᵁ V),
        q.appLE V ⊤ hle b = 0 → (Spec.map f ≫ hV.fromSpec).appLE V ⊤ htop b = 0 := by
      rintro q rfl hle hq0; exact hq0
    refine key (θ ≫ π) hθ (hθ ▸ htop) ?_
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, hb, map_zero]
  rw [appLE_SpecMap_comp_fromSpec, CommRingCat.comp_apply] at h1
  have := congrArg (Scheme.ΓSpecIso R).hom h1
  rwa [Iso.inv_hom_id_apply, map_zero] at this

theorem tmul_eq_zero (U : T.affineOpens) (W : T'.Opens) (hW : IsAffineOpen W) (hWU : W ≤ h ⁻¹ᵁ U)
    [Algebra Γ(T, U) Γ(D, g ⁻¹ᵁ U)] [Algebra Γ(T, U) Γ(T', W)]
    (hφ : algebraMap Γ(T, U) Γ(D, g ⁻¹ᵁ U) = (g.app U).hom)
    (hσ : algebraMap Γ(T, U) Γ(T', W) = (h.appLE U W hWU).hom)
    {b : Γ(D, g ⁻¹ᵁ U)} (hb : (pullback.fst g h).app (g ⁻¹ᵁ U) b = 0) :
    (1 : Γ(T', W)) ⊗ₜ[Γ(T, U)] b = 0 := by
  let C : CommRingCat.{u} := .of (Γ(T', W) ⊗[T.presheaf.obj (Opposite.op (U : T.Opens))] Γ(D, g ⁻¹ᵁ (U : T.Opens)))
  let ιR : Γ(D, g ⁻¹ᵁ (U : T.Opens)) ⟶ C := CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight :
      Γ(D, g ⁻¹ᵁ (U : T.Opens)) →ₐ[T.presheaf.obj (Opposite.op (U : T.Opens))]
        Γ(T', W) ⊗[T.presheaf.obj (Opposite.op (U : T.Opens))] Γ(D, g ⁻¹ᵁ (U : T.Opens))).toRingHom
  let ιL : Γ(T', W) ⟶ C := CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom :
      Γ(T', W) →+* Γ(T', W) ⊗[T.presheaf.obj (Opposite.op (U : T.Opens))] Γ(D, g ⁻¹ᵁ (U : T.Opens)))

  have hring : g.appLE U (g ⁻¹ᵁ U) le_rfl ≫ ιR = h.appLE U W hWU ≫ ιL := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rw [Scheme.Hom.appLE_eq_app]
    simp only [ιR, ιL, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [← hφ, ← hσ]
    exact ((Algebra.TensorProduct.includeRight :
      Γ(D, g ⁻¹ᵁ (U : T.Opens)) →ₐ[T.presheaf.obj (Opposite.op (U : T.Opens))]
        Γ(T', W) ⊗[T.presheaf.obj (Opposite.op (U : T.Opens))] Γ(D, g ⁻¹ᵁ (U : T.Opens))).commutes a).trans
      (Algebra.TensorProduct.algebraMap_apply (R := T.presheaf.obj (Opposite.op (U : T.Opens)))
        (S := T.presheaf.obj (Opposite.op (U : T.Opens))) (A := Γ(T', W))
        (B := Γ(D, g ⁻¹ᵁ (U : T.Opens))) a)

  have comm : (Spec.map ιR ≫ (U.2.preimage g).fromSpec) ≫ g = (Spec.map ιL ≫ hW.fromSpec) ≫ h := by
    rw [Category.assoc, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec g U.2 (U.2.preimage g) le_rfl,
      ← IsAffineOpen.SpecMap_appLE_fromSpec h U.2 hW hWU, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      hring]
  have h3 : ιR b = 0 :=
    apply_eq_zero_of_lift (U.2.preimage g) ιR (pullback.fst g h) (pullback.lift _ _ comm)
      (pullback.lift_fst _ _ _) hb
  simpa [ιR, Algebra.TensorProduct.includeRight_apply] using h3

omit [IsClosedImmersion i] in

theorem contentAt_le_ker
    (hZ : ∀ V : D.affineOpens, RingHom.ker (i.app V).hom ≤ RingHom.ker ((pullback.fst g h).app V).hom)
    (U : T.affineOpens) : contentAt i g U ≤ RingHom.ker (h.app U).hom := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨b, hb, ψ, hψ, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  refine TopCat.Presheaf.IsSheaf.section_ext T'.IsSheaf (U := .op (h ⁻¹ᵁ (U : T.Opens))) (t := 0) ?_
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    T'.isBasis_affineOpens.exists_subset_of_mem_open hx (h ⁻¹ᵁ (U : T.Opens)).isOpen
  refine ⟨W, hWU, hxW, ?_⟩
  rw [map_zero]
  change h.appLE U W hWU (ψ b) = 0
  letI : Algebra Γ(T, U) Γ(D, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
  letI : Algebra Γ(T, U) Γ(T', W) := (h.appLE U W hWU).hom.toAlgebra
  have hψ' : IsFunctional (algebraMap Γ(T, U) Γ(D, g ⁻¹ᵁ U)) ψ := hψ
  have ht := tmul_eq_zero g h U W hW hWU rfl rfl (hZ (gInv g U) hb)
  exact algebraMap_eq_zero_of_tmul_eq_zero ht hψ'.toLinearMap

end Backward
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.AlgebraicGeometry.KMKeyLemmaSol.IsFunctional"

end SchemeLevel
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.AlgebraicGeometry.KMKeyLemmaSol.IsFunctional"

end AlgebraicGeometry.KMKeyLemmaSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.AlgebraicGeometry.KMKeyLemmaSol.IsFunctional P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.AlgebraicGeometry.KMKeyLemmaSol"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.AlgebraicGeometry.KMKeyLemmaSol.IsFunctional P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.AlgebraicGeometry"

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat.AlgebraicGeometry CategoryTheory CategoryTheory.Limits in

theorem solution
    {Z D T : Scheme.{u}} (i : Z ⟶ D) [IsClosedImmersion i] (g : D ⟶ T) [IsFinite g] [Flat g]
    [LocallyOfFinitePresentation g] :
    ∃ J : T.IdealSheafData, ∀ {T' : Scheme.{u}} (h : T' ⟶ T),
      J.comap h = ⊥ ↔ i.ker.comap (pullback.fst g h) = ⊥ := by
  refine ⟨KMKeyLemmaSol.contentSheaf i g, fun {T'} h => ?_⟩
  rw [KMKeyLemmaSol.comap_eq_bot_iff_forall_le_ker, KMKeyLemmaSol.ker_comap_eq_bot_iff_forall_le_ker]
  exact ⟨fun hJ V => KMKeyLemmaSol.forall_le_ker_fst i g h hJ V,
    fun hZ U => KMKeyLemmaSol.contentAt_le_ker i g h hZ U⟩

end S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_exists_idealSheafData_comap_eq_bot_iff_of_isClosedImmersion_of_isFinite_of_flat (solution)
