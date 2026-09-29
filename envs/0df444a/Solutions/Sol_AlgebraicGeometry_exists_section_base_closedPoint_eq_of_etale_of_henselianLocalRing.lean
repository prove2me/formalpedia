-- Prove2me | solution 1 for AlgebraicGeometry.exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/1e0f4657-1d09-51bd-ade4-1f5c1f70bab2

import Mathlib
import Theorems.Thm_HenselianLocalRing_exists_algHom_lift_of_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option maxHeartbeats 3200000 in
theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [AlgebraicGeometry.Etale f]
    (x : X) (hx : f.base x = IsLocalRing.closedPoint R) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint R) = x := by
  classical

  let k := IsLocalRing.ResidueField R
  let κX := X.residueField x
  have hy : (f.base x).asIdeal = IsLocalRing.maximalIdeal R := by rw [hx]; rfl
  haveI : (f.base x).asIdeal.IsMaximal := hy ▸ IsLocalRing.maximalIdeal.isMaximal R

  let ρY : R →+* (Spec (CommRingCat.of R)).residueField (f.base x) :=
    ((Scheme.Spec.residueFieldIso (.of R) (f.base x)).inv).hom.comp (algebraMap R (f.base x).asIdeal.ResidueField)
  have hρY_surj : Function.Surjective ρY :=
    ((Scheme.Spec.residueFieldIso (.of R) (f.base x)).commRingCatIsoToRingEquiv.symm.surjective).comp
      (Ideal.algebraMap_residueField_surjective (f.base x).asIdeal)
  let r : (Spec (CommRingCat.of R)).residueField (f.base x) →+* κX := (f.residueFieldMap x).hom
  let ρ : R →+* κX := r.comp ρY

  have hker : RingHom.ker ρY = IsLocalRing.maximalIdeal R := by
    rw [← hy]
    ext a
    simp only [RingHom.mem_ker, ρY, RingHom.coe_comp, Function.comp_apply]
    rw [← Ideal.algebraMap_residueField_eq_zero (I := (f.base x).asIdeal)]
    constructor
    · intro h
      exact (Scheme.Spec.residueFieldIso (.of R) (f.base x)).commRingCatIsoToRingEquiv.symm.injective
        (h.trans (map_zero _).symm)
    · intro h; rw [h, map_zero]

  let e₁ : k ≃+* (Spec (CommRingCat.of R)).residueField (f.base x) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hρY_surj)
  have he₁ : ∀ a : R, e₁ (IsLocalRing.residue R a) = ρY a := fun a => rfl

  letI algY : Algebra ((Spec (CommRingCat.of R)).residueField (f.base x)) κX := r.toAlgebra
  haveI hsepY : Algebra.IsSeparable ((Spec (CommRingCat.of R)).residueField (f.base x)) κX := inferInstance
  let ρk : k →+* κX := r.comp e₁.toRingHom
  letI algk : Algebra k κX := ρk.toAlgebra
  haveI hsepk : Algebra.IsSeparable k κX := by
    refine Algebra.IsSeparable.of_equiv_equiv (A₁ := (Spec (CommRingCat.of R)).residueField (f.base x)) (B₁ := κX)
      e₁.symm (RingEquiv.refl κX) ?_
    ext a
    show ρk (e₁.symm a) = r a
    simp [ρk]

  have hρk_bij : Function.Bijective ρk :=
    ⟨ρk.injective, IsSepClosed.algebraMap_surjective k κX⟩
  let E : k ≃+* κX := RingEquiv.ofBijective ρk hρk_bij
  have hE : ∀ a : R, E (IsLocalRing.residue R a) = ρ a := fun a => by
    show r (e₁ (IsLocalRing.residue R a)) = r (ρY a); rw [he₁]

  let pt : Spec (CommRingCat.of k) ⟶ X :=
    Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ X.fromSpecResidueField x
  have hpt_x : ∀ z, pt.base z = x := fun z => by
    show (X.fromSpecResidueField x) _ = x
    exact Scheme.fromSpecResidueField_apply x _
  have hpt_f : pt ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
    have hring : CommRingCat.ofHom (algebraMap R (f.base x).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of R) (f.base x)).inv ≫ f.residueFieldMap x ≫ CommRingCat.ofHom E.symm.toRingHom =
        CommRingCat.ofHom (IsLocalRing.residue R) := by
      ext a
      show E.symm (ρ a) = IsLocalRing.residue R a
      rw [← hE, RingEquiv.symm_apply_apply]
    show (Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ X.fromSpecResidueField x) ≫ f = _
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := f) x,
      ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of R) (f.base x), ← hring]
    simp only [Spec.map_comp, Category.assoc]
    rfl

  obtain ⟨U, hUaff, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  let B : CommRingCat := Γ(X, U)
  let g : Spec B ⟶ X := hUaff.fromSpec
  have hrange : Set.range pt.base ⊆ Set.range g.base := by
    rintro _ ⟨z, rfl⟩
    rw [hpt_x z, IsAffineOpen.range_fromSpec]
    exact hxU
  let pt' : Spec (CommRingCat.of k) ⟶ Spec B := IsOpenImmersion.lift g pt hrange
  have hpt' : pt' ≫ g = pt := IsOpenImmersion.lift_fac g pt hrange

  let φB : CommRingCat.of R ⟶ B := Spec.preimage (g ≫ f)
  have hφB : Spec.map φB = g ≫ f := Spec.map_preimage _
  let φpt : B ⟶ CommRingCat.of k := Spec.preimage pt'
  have hφpt : Spec.map φpt = pt' := Spec.map_preimage _
  have hcomp : φB ≫ φpt = CommRingCat.ofHom (IsLocalRing.residue R) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφB, hφpt, ← Category.assoc, hpt', hpt_f]

  letI algB : Algebra R B := φB.hom.toAlgebra
  haveI : Algebra.Etale R B := by
    have h1 : AlgebraicGeometry.Etale (g ≫ f) := inferInstance
    rw [← hφB] at h1
    exact (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mp h1

  let φ : B →ₐ[R] k :=
    { φpt.hom with
      commutes' := fun a => by
        show φpt.hom (φB.hom a) = IsLocalRing.residue R a
        exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) a }

  obtain ⟨ψ, hψ⟩ := HenselianLocalRing.exists_algHom_lift_of_etale (R := R) B φ
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ g, ?_, ?_⟩
  ·
    have hid : φB ≫ CommRingCat.ofHom ψ.toRingHom = 𝟙 _ := by
      ext a
      exact ψ.commutes a
    rw [Category.assoc, ← hφB, ← Spec.map_comp, hid, Spec.map_id]
  ·
    have hpoint : (Spec.map (CommRingCat.ofHom ψ.toRingHom)).base (IsLocalRing.closedPoint R) =
        pt'.base (IsLocalRing.closedPoint k) := by
      rw [← hφpt]
      show Spec.map (CommRingCat.ofHom ψ.toRingHom) (IsLocalRing.closedPoint R) =
        Spec.map φpt (IsLocalRing.closedPoint k)
      rw [Spec.map_apply, Spec.map_apply]
      refine PrimeSpectrum.ext (Ideal.ext fun b => ?_)
      show ψ b ∈ IsLocalRing.maximalIdeal R ↔ φpt.hom b ∈ IsLocalRing.maximalIdeal k
      rw [← IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_iff_ne_zero, not_not]
      show algebraMap R k (ψ b) = 0 ↔ φ b = 0
      rw [hψ b]
    show g.base ((Spec.map (CommRingCat.ofHom ψ.toRingHom)).base (IsLocalRing.closedPoint R)) = x
    rw [hpoint, ← Scheme.Hom.comp_apply, hpt']
    exact hpt_x _

end S_AlgebraicGeometry_exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing (solution)
