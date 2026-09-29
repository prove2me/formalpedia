-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f4c1bf34-caa8-5fdf-a2f8-3223a51ef672

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in
theorem solution
    {R : Type} [CommRing R] [IsNoetherianRing R] {M : Scheme.{0}} (ϖ : M ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType ϖ] (x : ↥M) (hx : IsClosed ({x} : Set ↥M)) :
    ∃ (n : ℕ) (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) (hJ : J.IsMaximal)
      (hJI : (J.map (Ideal.Quotient.mk I)).IsPrime)
      (ι : Spec (CommRingCat.of (MvPolynomial (Fin n) R ⧸ I)) ⟶ M) (_ : IsOpenImmersion ι),
      ι ≫ ϖ = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I))) ∧
      ι.base ⟨J.map (Ideal.Quotient.mk I), hJI⟩ = x ∧
      (Algebra.FormallySmooth R (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) →
          (ϖ.stalkMap x).hom.FormallySmooth) := by
  classical

  obtain ⟨i, y₀, hy₀⟩ := M.affineCover.exists_eq x
  let U := M.affineCover.X i
  let A : CommRingCat := Γ(U, ⊤)
  let g : Spec A ⟶ M := U.isoSpec.inv ≫ M.affineCover.f i
  let y : ↥(Spec A) := U.isoSpec.hom.base y₀
  have hgy : g.base y = x := by
    show (U.isoSpec.inv ≫ M.affineCover.f i).base (U.isoSpec.hom.base y₀) = x
    rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply U.isoSpec.hom U.isoSpec.inv y₀, Iso.hom_inv_id]
    simpa using hy₀

  let φ : CommRingCat.of R ⟶ A := Spec.preimage (g ≫ ϖ)
  have hφ : Spec.map φ = g ≫ ϖ := Spec.map_preimage _
  letI algRA : Algebra R A := φ.hom.toAlgebra
  have hft : Algebra.FiniteType R A := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft

  let I : Ideal (MvPolynomial (Fin n) R) := RingHom.ker f.toRingHom
  let e : (MvPolynomial (Fin n) R ⧸ I) ≃ₐ[R] A := Ideal.quotientKerAlgEquivOfSurjective hf
  have he : ∀ a, e (Ideal.Quotient.mk I a) = f a := fun a => by
    show (Ideal.quotientKerAlgEquivOfSurjective hf) (Ideal.Quotient.mk _ a) = f a
    rw [Ideal.quotientKerAlgEquivOfSurjective_apply]; rfl
  let 𝔮 : Ideal A := y.asIdeal
  have hginj : Function.Injective g.base := g.isOpenEmbedding.injective
  have hyclosed : IsClosed ({y} : Set ↥(Spec A)) := by
    have : ({y} : Set ↥(Spec A)) = g.base ⁻¹' {x} := by
      ext z; simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact hgy
      · intro hz; exact hginj (hz.trans hgy.symm)
    rw [this]; exact hx.preimage g.base.hom.continuous
  haveI h𝔮 : 𝔮.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hyclosed
  let J : Ideal (MvPolynomial (Fin n) R) := 𝔮.comap f.toRingHom
  have hIJ : I ≤ J := by
    intro a ha
    show f a ∈ 𝔮
    rw [show f a = 0 from ha]; exact 𝔮.zero_mem
  haveI hJ : J.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hf
  have hJI : (J.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIJ)
  have hJe : J.map (Ideal.Quotient.mk I) = 𝔮.comap (e : (MvPolynomial (Fin n) R ⧸ I) →+* A) := by
    have : J = (𝔮.comap (e : (MvPolynomial (Fin n) R ⧸ I) →+* A)).comap (Ideal.Quotient.mk I) := by
      rw [Ideal.comap_comap]
      ext a
      simp only [J, Ideal.mem_comap, RingHom.comp_apply]
      rw [show ((e : (MvPolynomial (Fin n) R ⧸ I) →+* A)) (Ideal.Quotient.mk I a) = f a from he a]
      rfl
    rw [this, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

  let eR : ↑A ≃+* (MvPolynomial (Fin n) R ⧸ I) := e.symm.toRingEquiv
  let ι : Spec (CommRingCat.of (MvPolynomial (Fin n) R ⧸ I)) ⟶ M := Spec.map eR.toCommRingCatIso.hom ≫ g
  have hιϖ : ι ≫ ϖ = Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I))) := by
    show (Spec.map eR.toCommRingCatIso.hom ≫ g) ≫ ϖ = _
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext r
    show eR (φ.hom r) = algebraMap R _ r
    exact e.symm.commutes r
  have hpt : PrimeSpectrum.comap eR.toRingHom ⟨J.map (Ideal.Quotient.mk I), hJI⟩ = y := by
    apply PrimeSpectrum.ext
    show (J.map (Ideal.Quotient.mk I)).comap eR.toRingHom = 𝔮
    rw [hJe, Ideal.comap_comap]
    have : ((e : (MvPolynomial (Fin n) R ⧸ I) →+* A)).comp eR.toRingHom = RingHom.id _ :=
      RingHom.ext fun a => e.apply_symm_apply a
    rw [this, Ideal.comap_id]
  have hιx : ι.base ⟨J.map (Ideal.Quotient.mk I), hJI⟩ = x := by
    show (Spec.map eR.toCommRingCatIso.hom ≫ g).base _ = x
    rw [Scheme.Hom.comp_apply, Spec.map_base]
    show g.base (PrimeSpectrum.comap eR.toRingHom ⟨J.map (Ideal.Quotient.mk I), hJI⟩) = x
    rw [hpt, hgy]
  refine ⟨n, I, J, hIJ, hJ, hJI, ι, inferInstance, hιϖ, hιx, fun hFS => ?_⟩

  let Pfs : MorphismProperty CommRingCat.{0} := RingHom.toMorphismProperty @RingHom.FormallySmooth
  haveI : Pfs.RespectsIso := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.FormallySmooth.respectsIso
  have goal_iff : (ϖ.stalkMap x).hom.FormallySmooth ↔ Pfs (ϖ.stalkMap x) := Iff.rfl
  rw [goal_iff]
  subst hιx
  have h3 : Pfs ((Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I)))).stalkMap
      ⟨J.map (Ideal.Quotient.mk I), hJI⟩) := by
    rw [MorphismProperty.arrow_mk_iso_iff Pfs (Scheme.arrowStalkMapSpecIso _ _)]
    set 𝔭 : Ideal R := (PrimeSpectrum.comap (algebraMap R (MvPolynomial (Fin n) R ⧸ I)) ⟨J.map (Ideal.Quotient.mk I), hJI⟩).asIdeal
    letI algL : Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) :=
      (Localization.localRingHom 𝔭 (J.map (Ideal.Quotient.mk I)) (algebraMap R (MvPolynomial (Fin n) R ⧸ I)) rfl).toAlgebra
    haveI : IsScalarTower R (Localization.AtPrime 𝔭) (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) :=
      IsScalarTower.of_algebraMap_eq (R := R) (S := Localization.AtPrime 𝔭) (A := Localization.AtPrime (J.map (Ideal.Quotient.mk I))) fun r => by
        rw [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map, ← IsScalarTower.algebraMap_apply]
    haveI := hFS
    have := Algebra.FormallySmooth.localization_base (R := R) (Rₘ := Localization.AtPrime 𝔭)
      (Sₘ := Localization.AtPrime (J.map (Ideal.Quotient.mk I))) 𝔭.primeCompl
    exact RingHom.formallySmooth_algebraMap.mpr this
  have h2 : Pfs ((ι ≫ ϖ).stalkMap ⟨J.map (Ideal.Quotient.mk I), hJI⟩) := by
    rw [Scheme.Hom.stalkMap_congr_hom _ _ hιϖ]
    exact (MorphismProperty.cancel_left_of_respectsIso Pfs _ _).mpr h3
  rw [Scheme.Hom.stalkMap_comp] at h2
  exact (MorphismProperty.cancel_right_of_respectsIso Pfs _ _).mp h2

end S_AlgebraicGeometry_Scheme_exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_chart_formallySmooth_stalkMap_of_formallySmooth_localization (solution)
