-- Prove2me | solution 1 for AlgebraicGeometry.exists_etale_nhd_section_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2e5b0f02-cf87-51cf-8c49-05f4ff5c8aad

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_etale_nhd_section_of_smooth

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

open scoped TensorProduct

namespace EtaleNhd

open IsLocalRing

theorem exists_etale_of_smooth_of_algHom_residueField
    {R : Type u} [CommRing R] [IsLocalRing R] {B : Type u} [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (ψ : B →ₐ[R] ResidueField R) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E) (_ : Algebra.Etale R E) (𝔫 : Ideal E) (_ : 𝔫.IsMaximal)
      (h𝔫 : maximalIdeal R ≤ 𝔫.comap (algebraMap R E)) (_ : ∀ e : E, ∃ r : R, e - algebraMap R E r ∈ 𝔫)
      (β : B →ₐ[R] E),
      (Ideal.Quotient.mk 𝔫).comp β.toRingHom = (Ideal.quotientMap 𝔫 (algebraMap R E) h𝔫).comp ψ.toRingHom := by
  classical

  have hψsurj : Function.Surjective ψ := fun a => by
    obtain ⟨r, rfl⟩ := residue_surjective a
    exact ⟨algebraMap R B r, ψ.commutes r⟩
  let P : Ideal B := RingHom.ker ψ.toRingHom
  haveI hPmax : P.IsMaximal := RingHom.ker_isMaximal_of_surjective ψ.toRingHom hψsurj

  obtain ⟨s, hs, hstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R B
  have : ∃ g ∈ s, g ∉ P := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have : Ideal.span s ≤ P := Ideal.span_le.mpr h
    rw [hs, top_le_iff] at this
    exact hPmax.ne_top this
  obtain ⟨g, hgs, hgP⟩ := this
  let Bg := Localization.Away g
  haveI : Algebra.IsStandardSmooth R Bg := hstd g hgs

  have hstd' : (algebraMap R Bg).IsStandardSmooth := by
    have halg : (algebraMap R Bg).toAlgebra = (inferInstance : Algebra R Bg) := Algebra.algebra_ext _ _ fun _ => rfl
    unfold RingHom.IsStandardSmooth
    rw [halg]
    infer_instance
  obtain ⟨n, G, hGC, hGet⟩ := hstd'.exists_etale_mvPolynomial

  have hunit : IsUnit (ψ.toRingHom g) := by
    rw [isUnit_iff_ne_zero]
    exact fun h => hgP (by simpa [P, RingHom.mem_ker] using h)
  let ψg : Bg →+* ResidueField R := Localization.awayLift ψ.toRingHom g hunit
  have hψg : ∀ b : B, ψg (algebraMap B Bg b) = ψ b := fun b =>
    IsLocalization.Away.lift_eq g hunit b
  have hψgR : ∀ r : R, ψg (algebraMap R Bg r) = residue R r := fun r => by
    rw [IsScalarTower.algebraMap_apply R B Bg, hψg, ψ.commutes]; rfl

  choose r hr using fun i : Fin n => residue_surjective (ψg (G (MvPolynomial.X i)))
  let ev : MvPolynomial (Fin n) R →+* R := MvPolynomial.eval r

  letI algG : Algebra (MvPolynomial (Fin n) R) Bg := G.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) Bg := hGet
  letI algEv : Algebra (MvPolynomial (Fin n) R) R := ev.toAlgebra

  let E := R ⊗[MvPolynomial (Fin n) R] Bg
  haveI : Algebra.Etale R E := Algebra.Etale.baseChange _ _ _

  letI algk : Algebra (MvPolynomial (Fin n) R) (ResidueField R) := ((residue R).comp ev).toAlgebra
  have key : ψg.comp G = (residue R).comp ev := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · change ψg (G (MvPolynomial.C c)) = residue R (MvPolynomial.eval r (MvPolynomial.C c))
      rw [MvPolynomial.eval_C, ← hψgR, ← hGC]
      rfl
    · change ψg (G (MvPolynomial.X i)) = residue R (MvPolynomial.eval r (MvPolynomial.X i))
      rw [MvPolynomial.eval_X, hr]
  have hfR : ∀ p : MvPolynomial (Fin n) R, residue R (algebraMap (MvPolynomial (Fin n) R) R p) =
      algebraMap (MvPolynomial (Fin n) R) (ResidueField R) p := fun _ => rfl
  let fR : R →ₐ[MvPolynomial (Fin n) R] ResidueField R := ⟨residue R, hfR⟩
  have hgB : ∀ p : MvPolynomial (Fin n) R, ψg (algebraMap (MvPolynomial (Fin n) R) Bg p) =
      algebraMap (MvPolynomial (Fin n) R) (ResidueField R) p := fun p =>
    congrArg (fun φ : MvPolynomial (Fin n) R →+* ResidueField R => φ p) key
  let gB : Bg →ₐ[MvPolynomial (Fin n) R] ResidueField R := ⟨ψg, hgB⟩
  haveI : IsScalarTower (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) (ResidueField R) :=
    IsScalarTower.left _
  let χ : E →ₐ[MvPolynomial (Fin n) R] ResidueField R :=
    Algebra.TensorProduct.lift fR gB (fun _ _ => Commute.all _ _)
  have hχ : ∀ (a : R) (b : Bg), χ (a ⊗ₜ b) = residue R a * ψg b := fun a b =>
    Algebra.TensorProduct.lift_tmul _ _ _ a b
  have hχR : ∀ a : R, χ (algebraMap R E a) = residue R a := fun a => by
    have : algebraMap R E a = a ⊗ₜ[MvPolynomial (Fin n) R] (1 : Bg) := rfl
    rw [this, hχ, map_one, mul_one]
  have hχsurj : Function.Surjective χ := fun t => by
    obtain ⟨a, rfl⟩ := residue_surjective t
    exact ⟨algebraMap R E a, hχR a⟩
  let 𝔫 : Ideal E := RingHom.ker χ.toRingHom
  haveI h𝔫max : 𝔫.IsMaximal := RingHom.ker_isMaximal_of_surjective χ.toRingHom hχsurj
  have h𝔫 : maximalIdeal R ≤ 𝔫.comap (algebraMap R E) := fun a ha => by
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change χ (algebraMap R E a) = 0
    rw [hχR, residue_eq_zero_iff]
    exact ha
  have hres : ∀ e : E, ∃ a : R, e - algebraMap R E a ∈ 𝔫 := fun e => by
    obtain ⟨a, ha⟩ := residue_surjective (χ e)
    refine ⟨a, ?_⟩
    rw [RingHom.mem_ker]
    change χ (e - algebraMap R E a) = 0
    rw [map_sub, hχR, ha, sub_self]

  let β₀ : B →+* E := (Algebra.TensorProduct.includeRight (R := MvPolynomial (Fin n) R) (A := R) (B := Bg)).toRingHom.comp
    (algebraMap B Bg)
  have hβ₀ : ∀ b : B, β₀ b = (1 : R) ⊗ₜ[MvPolynomial (Fin n) R] algebraMap B Bg b := fun _ => rfl
  have hβ₀R : ∀ a : R, β₀ (algebraMap R B a) = algebraMap R E a := fun a => by
    rw [hβ₀, ← IsScalarTower.algebraMap_apply R B Bg]

    have h1 : algebraMap R Bg a = (MvPolynomial.C a : MvPolynomial (Fin n) R) • (1 : Bg) := by
      rw [Algebra.smul_def, mul_one, ← hGC]; rfl
    have h2 : algebraMap R E a = ((MvPolynomial.C a : MvPolynomial (Fin n) R) • (1 : R)) ⊗ₜ[MvPolynomial (Fin n) R] (1 : Bg) := by
      have : (MvPolynomial.C a : MvPolynomial (Fin n) R) • (1 : R) = a := by
        rw [Algebra.smul_def, mul_one]; exact MvPolynomial.eval_C a
      rw [this]; rfl
    rw [h1, h2, TensorProduct.smul_tmul]
  let β : B →ₐ[R] E := ⟨β₀, hβ₀R⟩
  have hχβ : ∀ b : B, χ (β b) = ψ b := fun b => by
    change χ (β₀ b) = ψ b
    rw [hβ₀, hχ, map_one, one_mul, hψg]
  refine ⟨E, inferInstance, inferInstance, inferInstance, 𝔫, h𝔫max, h𝔫, hres, β, ?_⟩
  refine RingHom.ext fun b => ?_
  obtain ⟨a, ha⟩ := residue_surjective (ψ b)
  change Ideal.Quotient.mk 𝔫 (β b) = Ideal.quotientMap 𝔫 (algebraMap R E) h𝔫 (ψ b)
  rw [← ha]
  change _ = Ideal.quotientMap 𝔫 (algebraMap R E) h𝔫 (Ideal.Quotient.mk (maximalIdeal R) a)
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, RingHom.mem_ker]
  change χ (β b - algebraMap R E a) = 0
  rw [map_sub, hχβ, hχR, ← ha, sub_self]

end EtaleNhd

namespace EtaleNhd

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem main
    {R : Type u} [CommRing R] [IsLocalRing R]
    {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ U)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E) (_ : Algebra.Etale R E) (𝔫 : Ideal E) (_ : 𝔫.IsMaximal)
      (h𝔫 : IsLocalRing.maximalIdeal R ≤ 𝔫.comap (algebraMap R E))
      (_ : ∀ e : E, ∃ r : R, e - algebraMap R E r ∈ 𝔫)
      (τ : Spec (CommRingCat.of E) ⟶ U),
      τ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R E)) ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔫)) ≫ τ =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap 𝔫 (algebraMap R E) h𝔫)) ≫ x := by
  classical
  set k := ResidueField R with hk

  let pt : U := x.base (closedPoint k)
  obtain ⟨V, hV, hptV, -⟩ := exists_isAffineOpen_mem_and_subset (x := pt) (U := (⊤ : U.Opens)) trivial
  let B : Type u := Γ(U, V)
  let φ : Γ(Spec (CommRingCat.of R), ⊤) ⟶ Γ(U, V) := f.appLE ⊤ V le_top
  let ι : R →+* Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  letI algB : Algebra R B := (φ.hom.comp ι).toAlgebra

  haveI : Algebra.Smooth R B := by
    have h1 : φ.hom.Smooth := Smooth.smooth_appLE f (isAffineOpen_top _) hV le_top
    have h2 : ι.Smooth := RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.bijective
    have h3 : (φ.hom.comp ι).Smooth := RingHom.Smooth.stableUnderComposition _ _ h2 h1
    exact h3

  have hrange : Set.range x.base ⊆ Set.range V.ι.base := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = closedPoint k := Subsingleton.elim _ _
    rw [Scheme.Opens.range_ι]
    exact hptV
  let x' : Spec (CommRingCat.of k) ⟶ V := IsOpenImmersion.lift V.ι x hrange
  have hx' : x' ≫ V.ι = x := IsOpenImmersion.lift_fac _ _ _
  let ψ' : Γ(U, V) ⟶ CommRingCat.of k := Spec.preimage (x' ≫ hV.isoSpec.hom)
  have hψ'x : Spec.map ψ' ≫ hV.fromSpec = x := by
    rw [Spec.map_preimage, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc, hx']

  have hVf : hV.fromSpec ≫ f = Spec.map φ ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
    rw [← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact (IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV le_top).symm
  have hψ'R : ψ'.hom.comp (φ.hom.comp ι) = residue R := by
    have h1 : Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ ≫ ψ') =
        Spec.map (CommRingCat.ofHom (residue R)) := by
      rw [Spec.map_comp, Spec.map_comp, Category.assoc, ← hVf, ← Category.assoc, hψ'x, hx]
    have h2 := Spec.map_injective h1
    have h3 := congrArg CommRingCat.Hom.hom h2
    exact h3
  let ψ : B →ₐ[R] k := ⟨ψ'.hom, fun r => congrArg (fun φ0 : R →+* k => φ0 r) hψ'R⟩

  obtain ⟨E, _, _, _, 𝔫, _, h𝔫, hres, β, hβ⟩ := exists_etale_of_smooth_of_algHom_residueField ψ
  refine ⟨E, inferInstance, inferInstance, inferInstance, 𝔫, inferInstance, h𝔫, hres,
    Spec.map (CommRingCat.ofHom β.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  ·
    rw [Category.assoc, hVf, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    change β (φ.hom (ι r)) = algebraMap R E r
    exact β.commutes r
  ·
    rw [← hψ'x, ← Category.assoc, ← Spec.map_comp]
    have hring : CommRingCat.ofHom β.toRingHom ≫ CommRingCat.ofHom (Ideal.Quotient.mk 𝔫) =
        ψ' ≫ CommRingCat.ofHom (Ideal.quotientMap 𝔫 (algebraMap R E) h𝔫) := by
      ext b
      exact congrArg (fun φ0 : B →+* E ⧸ 𝔫 => φ0 b) hβ
    rw [hring, Spec.map_comp, Category.assoc]
    rfl

end EtaleNhd

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ U)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E) (_ : Algebra.Etale R E) (𝔫 : Ideal E) (_ : 𝔫.IsMaximal)
      (h𝔫 : IsLocalRing.maximalIdeal R ≤ 𝔫.comap (algebraMap R E))
      (_ : ∀ e : E, ∃ r : R, e - algebraMap R E r ∈ 𝔫)
      (τ : Spec (CommRingCat.of E) ⟶ U),
      τ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R E)) ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔫)) ≫ τ =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap 𝔫 (algebraMap R E) h𝔫)) ≫ x :=
  EtaleNhd.main f x hx

end S_AlgebraicGeometry_exists_etale_nhd_section_of_smooth
end P2MW
export P2MW.S_AlgebraicGeometry_exists_etale_nhd_section_of_smooth (solution)
