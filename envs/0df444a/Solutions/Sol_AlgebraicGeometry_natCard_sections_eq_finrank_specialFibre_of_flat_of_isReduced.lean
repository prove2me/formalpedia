-- Prove2me | solution 1 for AlgebraicGeometry.natCard_sections_eq_finrank_specialFibre_of_flat_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4ab3b99b-8229-5049-b8ae-f13b393d36dc

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing
import Theorems.Thm_AlgebraicGeometry_exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing
import Theorems.Thm_AlgebraicGeometry_finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite
import Theorems.Thm_AlgebraicGeometry_finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite
import Theorems.Thm_AlgebraicGeometry_exists_algEquiv_globalSections_pullback_spec_tensorProduct
import Theorems.Thm_Algebra_natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_natCard_sections_eq_finrank_specialFibre_of_flat_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed K]
    {X Y XK : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g] [Flat g]
    (q : Y ⟶ Spec (.of (IsLocalRing.ResidueField R))) (π : Y ⟶ X)
    (hY : IsPullback π q g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (qK : XK ⟶ Spec (.of K)) (πK : XK ⟶ X)
    (hXK : IsPullback πK qK g (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsReduced XK] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
    Module.Finite (IsLocalRing.ResidueField R) Γ(Y, ⊤) ∧
    Nat.card {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _} = Module.finrank (IsLocalRing.ResidueField R) Γ(Y, ⊤) := by
  classical

  obtain ⟨Xf, X', i, j, hi, hj, hfin, hcover, -, hempty⟩ :=
    exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing g
  haveI := hi
  haveI := hfin

  obtain ⟨hYfin, heq⟩ :=
    finrank_sections_eq_finrank_tensorProduct_of_isPullback_residue_of_isFinite g i j hcover hempty q π hY
  refine ⟨hYfin, ?_⟩
  rw [heq]

  letI algB : Algebra R Γ(Xf, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ g).appTop).hom.toAlgebra
  obtain ⟨hXfaff, -⟩ := (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := i ≫ g)).mp inferInstance
  haveI : IsAffine Xf := hXfaff

  obtain ⟨-, hBfin, -⟩ := finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite g i K
  haveI : Module.Finite R Γ(Xf, ⊤) := hBfin

  haveI : Module.Flat R Γ(Xf, ⊤) := by
    have hf : Flat (i ≫ g) := inferInstance
    have := (HasRingHomProperty.iff_of_isAffine (P := @Flat) (f := i ≫ g)).mp hf

    have h2 : ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ g).appTop).hom.Flat := by
      rw [CommRingCat.hom_comp]
      exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective) this
    exact h2

  haveI : IsReduced (K ⊗[R] Γ(Xf, ⊤)) := by

    let XfK := pullback (i ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap R K)))

    let u : XfK ⟶ XK := hXK.lift (pullback.fst _ _ ≫ i) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
    have hu1 : u ≫ πK = pullback.fst _ _ ≫ i := hXK.lift_fst _ _ _
    have hu2 : u ≫ qK = pullback.snd _ _ := hXK.lift_snd _ _ _
    have hsq : IsPullback u (pullback.fst (i ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) πK i :=
      IsPullback.of_right (by rw [hu2]; exact (IsPullback.of_hasPullback (i ≫ g)
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).flip) hu1 hXK.flip
    haveI : IsOpenImmersion u := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
    haveI : IsReduced XfK := isReduced_of_isOpenImmersion u

    letI : Algebra K Γ(pullback (i ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap R K))), ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (pullback.snd (i ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).appTop).hom.toAlgebra
    obtain ⟨e, -⟩ := exists_algEquiv_globalSections_pullback_spec_tensorProduct (i ≫ g) K
    haveI : IsReduced Γ(pullback (i ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap R K))), ⊤) := inferInstance
    exact isReduced_of_injective e.toRingHom e.injective

  rw [← Algebra.natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced K Γ(Xf, ⊤)]

  let P := {x : Spec (.of K) ⟶ Xf // x ≫ i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K))}
  have hfac : ∀ s : {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _},
      ∃ xf : Spec (.of K) ⟶ Xf, xf ≫ i = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s.1 := fun s =>
    (exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing R K g i j hcover hempty
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s.1)
      (by rw [Category.assoc, s.2, Category.comp_id])).mp ⟨s.1, s.2, rfl⟩
  choose xf hxf using hfac
  let Φ₁ : {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _} → P :=
    fun s => ⟨xf s, by rw [← Category.assoc, hxf s, Category.assoc, s.2, Category.comp_id]⟩
  have hker : RingHom.ker (algebraMap R K) ≤ nilradical R := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
    exact bot_le
  haveI hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr hker⟩
  have hΦ₁ : Function.Bijective Φ₁ := by
    constructor
    · intro s s' h
      have h' : xf s = xf s' := congrArg Subtype.val h
      apply Subtype.ext
      refine ext_of_isDominant_of_isSeparated g (s.2.trans s'.2.symm)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ?_
      rw [← hxf s, ← hxf s', h']
    · intro x
      obtain ⟨s, hs, hsx⟩ :=
        (exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing R K g i j hcover hempty
          (x.1 ≫ i) (by rw [Category.assoc]; exact x.2)).mpr ⟨x.1, rfl⟩
      refine ⟨⟨s, hs⟩, ?_⟩
      apply Subtype.ext
      show xf ⟨s, hs⟩ = x.1
      rw [← cancel_mono i, hxf ⟨s, hs⟩]
      exact hsx
  rw [Nat.card_congr (Equiv.ofBijective Φ₁ hΦ₁)]

  have key : ∀ (x : P) (r : R),
      (Scheme.ΓSpecIso (.of K)).hom.hom (x.1.appTop.hom ((i ≫ g).appTop.hom
        ((Scheme.ΓSpecIso (.of R)).inv.hom r))) = algebraMap R K r := by
    intro x r
    have hx := x.2
    have e1 : x.1.appTop.hom ((i ≫ g).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r)) =
        (x.1 ≫ i ≫ g).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) := by
      rfl
    rw [e1, hx]
    have e2 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R K)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    rw [e2]
    simp
  let Φ : P → (Γ(Xf, ⊤) →ₐ[R] K) := fun x =>
    { toRingHom := (Scheme.ΓSpecIso (.of K)).hom.hom.comp x.1.appTop.hom
      commutes' := fun r => key x r }

  have hover : ∀ φ : Γ(Xf, ⊤) →ₐ[R] K,
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Xf.isoSpec.inv) ≫ i ≫ g =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    intro φ
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality (i ≫ g), Scheme.isoSpec_Spec_inv,
      ← Spec.map_comp_assoc, ← Spec.map_comp]
    congr 1
    have h1 : (Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ g).appTop = CommRingCat.ofHom (algebraMap R Γ(Xf, ⊤)) := rfl
    rw [← Category.assoc, h1, ← CommRingCat.ofHom_comp]
    congr 1
    exact φ.comp_algebraMap
  let Ψ : (Γ(Xf, ⊤) →ₐ[R] K) → P := fun φ =>
    ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Xf.isoSpec.inv, hover φ⟩
  have hΨΦ : ∀ x : P, Ψ (Φ x) = x := by
    intro x
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of K)).hom.hom.comp x.1.appTop.hom)) ≫ Xf.isoSpec.inv = x.1
    have : CommRingCat.ofHom ((Scheme.ΓSpecIso (.of K)).hom.hom.comp x.1.appTop.hom) =
        x.1.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom := rfl
    rw [this, Spec.map_comp, Category.assoc, Scheme.isoSpec_inv_naturality x.1, ← Scheme.isoSpec_Spec_hom,
      Iso.hom_inv_id_assoc]
  have hΨinj : Function.Injective Ψ := by
    intro φ φ' h
    have h1 : Spec.map (CommRingCat.ofHom φ.toRingHom) = Spec.map (CommRingCat.ofHom φ'.toRingHom) := by
      have := congrArg Subtype.val h
      simpa [Ψ, cancel_mono] using this
    have h2 := Spec.map_injective h1
    apply AlgHom.ext
    intro b
    exact congrArg (fun f : Γ(Xf, ⊤) ⟶ CommRingCat.of K => f.hom b) h2
  have hΦΨ : ∀ φ, Φ (Ψ φ) = φ := fun φ => hΨinj (by rw [hΨΦ])
  exact Nat.card_congr { toFun := Φ, invFun := Ψ, left_inv := hΨΦ, right_inv := hΦΨ }

end S_AlgebraicGeometry_natCard_sections_eq_finrank_specialFibre_of_flat_of_isReduced
end P2MW
export P2MW.S_AlgebraicGeometry_natCard_sections_eq_finrank_specialFibre_of_flat_of_isReduced (solution)
