-- Prove2me | Definitions.Def_AlgebraicGeometry_HenselianEtaleSections
-- name    : AlgebraicGeometry_HenselianEtaleSections
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T00:39:34.301799+00:00
-- url     : https://prove2.me/theorems/8bf7b1af-ded7-4c57-8774-e0bec7119d54
-- title:
--   Sections of étale schemes over henselian local rings
-- statement:
--   An étale neighborhood with a point over the residue field has a section lifting that point.

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Unramified.LocalStructure

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial


namespace PhilipponHenselianEtaleSection

variable (R : Type*) [CommRing R] [HenselianLocalRing R]

private abbrev ρ := Algebra.ofId R (ResidueField R)

private theorem exists_section_standardPair (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] ResidueField R) :
    ∃ ψ : P.Ring →ₐ[R] R, (ρ R).comp ψ = φ := by
  have hx := (StandardEtalePair.hasMap_X (P := P)).map φ
  have hLift : ∀ p : R[X], p.Monic → ∀ a : ResidueField R,
      aeval a p = 0 → aeval a p.derivative ≠ 0 →
      ∃ b : R, p.IsRoot b ∧ residue R b = a :=
    ((HenselianLocalRing.TFAE R).out 0 1).mp (show HenselianLocalRing R from inferInstance)
  obtain ⟨b, hb, hres⟩ := hLift P.f P.monic_f (φ P.X)
    hx.1 (hx.isUnit_derivative_f.ne_zero)
  have hb' : P.HasMap b := by
    refine ⟨?_, ?_⟩
    · simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
        Polynomial.IsRoot.def] using hb
    · have h := hx.2.ne_zero
      rw [← hres, Polynomial.aeval_def, IsLocalRing.ResidueField.algebraMap_eq,
        Polynomial.eval₂_at_apply] at h
      simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using
        (residue_ne_zero_iff_isUnit _).mp h
  refine ⟨P.lift b hb', P.hom_ext ?_⟩
  change residue R (P.lift b hb' P.X) = φ P.X
  rw [P.lift_X, hres]

private theorem exists_section_standard {S : Type*} [CommRing S] [Algebra R S]
    [Algebra.IsStandardEtale R S] (φ : S →ₐ[R] ResidueField R) :
    ∃ ψ : S →ₐ[R] R, (ρ R).comp ψ = φ := by
  let P : StandardEtalePresentation R S := Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨ψ, hψ⟩ := exists_section_standardPair R P.P (φ.comp P.equivRing.symm.toAlgHom)
  refine ⟨ψ.comp P.equivRing.toAlgHom, ?_⟩
  ext x
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
    DFunLike.congr_fun hψ (P.equivRing x)

/-- An algebra map from an étale algebra to the residue field of a Henselian
local ring lifts to an algebra map to the ring. -/
theorem exists_section {S : Type*} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (φ : S →ₐ[R] ResidueField R) : ∃ ψ : S →ₐ[R] R, (ρ R).comp ψ = φ := by
  let Q := RingHom.ker φ.toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime φ.toRingHom
  let : Algebra.IsEtaleAt R Q := Algebra.FormallyEtale.comp R S _
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  have hu : IsUnit (φ g) := isUnit_iff_ne_zero.mpr hg
  let φ' : Localization.Away g →ₐ[R] ResidueField R := IsLocalization.Away.liftAlgHom g hu
  obtain ⟨ψ, hψ⟩ := exists_section_standard R φ'
  refine ⟨ψ.comp (IsScalarTower.toAlgHom R S (Localization.Away g)), ?_⟩
  ext x
  exact (DFunLike.congr_fun hψ (algebraMap S (Localization.Away g) x)).trans
    (IsLocalization.Away.lift_eq g hu x)

universe u

/-- A lift of the residue point to an étale scheme over a Henselian local
ring extends to a section over the ring. -/
theorem exists_scheme_section {R : Type u} [CommRing R] [HenselianLocalRing R]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) [Etale g]
    (x : Spec (CommRingCat.of (ResidueField R)) ⟶ Y)
    (hx : x ≫ g = Spec.map (CommRingCat.ofHom (residue R))) :
    ∃ t : Spec (CommRingCat.of R) ⟶ Y,
      t ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue R)) ≫ t = x := by
  obtain ⟨A, i, hi, hxI, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x default) (U := ⊤) trivial
  have hr : Set.range x ⊆ Set.range i := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  let e := IsOpenImmersion.lift i x hr
  have he : e ≫ i = x := IsOpenImmersion.lift_fac ..
  obtain ⟨p, hp⟩ := Spec.map_surjective (i ≫ g)
  obtain ⟨q, hq⟩ := Spec.map_surjective e
  have hpq : p ≫ q = CommRingCat.ofHom (residue R) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hq, hp, ← Category.assoc, he, hx]
  have hpe : Etale (Spec.map p) := hp.symm ▸ (inferInstance : Etale (i ≫ g))
  let : Algebra R A := p.hom.toAlgebra
  let : Algebra.Etale R A := (HasRingHomProperty.Spec_iff (P := @Etale)).mp hpe
  let q' : A →ₐ[R] ResidueField R :=
    { toRingHom := q.hom
      commutes' := fun a => ConcreteCategory.congr_hom hpq a }
  obtain ⟨k, hk⟩ := exists_section R q'
  let k' : A ⟶ CommRingCat.of R := CommRingCat.ofHom k.toRingHom
  have hpk : p ≫ k' = 𝟙 _ := ConcreteCategory.hom_ext_iff.mpr k.commutes
  have hkq : k' ≫ CommRingCat.ofHom (residue R) = q := by
    apply ConcreteCategory.hom_ext
    intro a
    exact DFunLike.congr_fun hk a
  refine ⟨Spec.map k' ≫ i, ?_, ?_⟩
  · rw [Category.assoc, ← hp, ← Spec.map_comp, hpk, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hkq, hq, he]

end PhilipponHenselianEtaleSection

end

end


