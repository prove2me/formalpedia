-- Prove2me | solution 1 for AlgebraicGeometry.exists_closedFibre_testCurves_of_integralPoints_through
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6dd5fd4d-3f19-53d2-92bb-746eb1b6bf2f

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_FLTPrelim_Ramification

import Theorems.Thm_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_closedFibre_testCurves_of_integralPoints_through

set_option autoImplicit false
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_closedFibre_testCurves_of_integralPoints_through.AlgebraicGeometry NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Spec.map_preimage Scheme.Hom Scheme.Pullback.range_fst LocallyOfFiniteType Spec Spec.map Scheme LocallyOfFiniteType.jacobsonSpace IsPreimmersion.of_isLocalization IsPreimmersion Scheme.Hom.comp_apply Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton"
namespace ASMB
p2m_open "AlgebraicGeometry"

theorem hom_specInt_ext {T : Type} [CommRing T] (u v : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of ℤ)) : u = v := by
  rw [← Spec.map_preimage u, ← Spec.map_preimage v]
  congr 1
  ext1
  exact RingHom.ext_int _ _

theorem hom_specRat_ext {T : Type} [CommRing T] (u v : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of ℚ)) : u = v := by
  rw [← Spec.map_preimage u, ← Spec.map_preimage v]
  congr 1
  ext1
  exact RingHom.ext_rat _ _

theorem hom_specLoc_ext (R : Type) [CommRing R] (M : Submonoid ℤ) [Algebra ℤ R] [IsLocalization M R]
    {T : Type} [CommRing T] (u v : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R)) : u = v := by
  rw [← Spec.map_preimage u, ← Spec.map_preimage v]
  congr 1
  ext1
  exact IsLocalization.ringHom_ext M (RingHom.ext_int _ _)

theorem specMap_base_closedPoint_eq_bot {K T : Type} [Field K] [CommRing T] [IsDomain T] (f : T →+* K)
    (hf : Function.Injective f) :
    (Spec.map (CommRingCat.ofHom f)).base (IsLocalRing.closedPoint K) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T) := by
  apply PrimeSpectrum.ext
  change Ideal.comap f (IsLocalRing.maximalIdeal K) = ⊥
  rw [(Ideal.eq_bot_or_top (IsLocalRing.maximalIdeal K)).resolve_right (IsLocalRing.maximalIdeal.isMaximal K).ne_top,
    Ideal.comap_bot_of_injective f hf]

end AlgebraicGeometry.ASMB

open AlgebraicGeometry.ASMB in
set_option linter.unusedVariables false in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [(Ideal.span {(p : ℤ)}).IsPrime] [IsLocalization.AtPrime R (Ideal.span {(p : ℤ)})]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [LocallyOfFiniteType g]

    (η : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))))
    (hη : (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base η = IsLocalRing.closedPoint R)

    (φη : SchemeHomOver (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))))
    (φK : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶ pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    (hφK : φK ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) = pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    (θ : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
    (hθ₁ : θ ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
    (hθ₂ : θ ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    (hφ : φK ≫ θ = θ ≫ φη.1)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hsupply : ∀ ζ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ G,
      ζ ≫ g = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap ℤ ↥A))) →
      ∃ (s e : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g)
        (z zt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
        s.1.base (IsLocalRing.closedPoint ↥A) =
          ζ.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) ∧
        z ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 ∧
        zt ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = Spec.map (CommRingCat.ofHom A.subtype) ≫ e.1 ∧
        zt = z ≫ φη.1) :
    ∃ D : Set ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))),
      (∀ z ∈ D, (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base z = IsLocalRing.closedPoint R) ∧
      η ∈ closure D ∧
      (∀ z ∈ D, ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B)
        (c : Spec (CommRingCat.of B) ⟶ pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))),
        (c ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))).base (IsLocalRing.closedPoint B) = z ∧
        c.base ⟨⊥, Ideal.isPrime_bot⟩ ∈ Set.range
          (pullback.lift (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
            (φK ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
            (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).base) := by
  classical

  haveI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) := IsPreimmersion.of_isLocalization (Ideal.span {(p : ℤ)}).primeCompl (S := R)
  have hinj : Function.Injective (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base := (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).isEmbedding.injective

  have hpA : (algebraMap ℤ ↥A (p : ℤ)) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; (simp at hA ⊢; exact hA)
  have hunits : ∀ y : (Ideal.span {(p : ℤ)}).primeCompl, IsUnit (algebraMap ℤ ↥A y) := by
    intro y
    have hy : ¬ (p : ℤ) ∣ (y : ℤ) := fun h => y.2 (Ideal.mem_span_singleton.mpr h)
    have hcop : IsCoprime (p : ℤ) (y : ℤ) :=
      (Nat.prime_iff_prime_int.mp Fact.out).irreducible.coprime_iff_not_dvd.mpr hy
    obtain ⟨a, b, hab⟩ := hcop
    by_contra hnu
    have hmem : algebraMap ℤ ↥A (y : ℤ) ∈ IsLocalRing.maximalIdeal ↥A :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    apply (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top
    rw [Ideal.eq_top_iff_one, ← map_one (algebraMap ℤ ↥A), ← hab, map_add, map_mul, map_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpA) (Ideal.mul_mem_left _ _ hmem)
  let ρ : R →+* ↥A := IsLocalization.lift (M := (Ideal.span {(p : ℤ)}).primeCompl) hunits
  have hρ : ρ.comp (algebraMap ℤ R) = algebraMap ℤ ↥A := IsLocalization.lift_comp hunits
  let τ : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom ρ)
  have hτ : τ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) = Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]

  have hρloc : ∀ x ∈ IsLocalRing.maximalIdeal R, ρ x ∈ IsLocalRing.maximalIdeal ↥A := by
    intro x hx
    have hmR : IsLocalRing.maximalIdeal R = Ideal.map (algebraMap ℤ R) (Ideal.span {(p : ℤ)}) :=
      (IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(p : ℤ)}) R).symm
    rw [hmR, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hx
    obtain ⟨r, rfl⟩ := hx
    rw [map_mul]
    refine Ideal.mul_mem_right _ _ ?_
    have : ρ (algebraMap ℤ R (p : ℤ)) = algebraMap ℤ ↥A (p : ℤ) := by rw [← RingHom.comp_apply, hρ]
    rw [this]; exact hpA
  haveI hρlocal : IsLocalHom ρ := by
    refine ⟨fun x hx => ?_⟩
    by_contra hxu
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp
      (hρloc x ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hxu))))) hx

  let k₀ := IsLocalRing.ResidueField R
  let r : Spec (CommRingCat.of k₀) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hrpt : ∀ x : Spec (CommRingCat.of k₀), r.base x = IsLocalRing.closedPoint R := by
    intro x
    obtain rfl : x = IsLocalRing.closedPoint k₀ := Subsingleton.elim _ _
    apply PrimeSpectrum.ext
    change Ideal.comap (IsLocalRing.residue R) (IsLocalRing.maximalIdeal k₀) = IsLocalRing.maximalIdeal R
    rw [(Ideal.eq_bot_or_top (IsLocalRing.maximalIdeal k₀)).resolve_right (IsLocalRing.maximalIdeal.isMaximal k₀).ne_top,
      ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
  haveI : JacobsonSpace ↥(pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) r) := LocallyOfFiniteType.jacobsonSpace (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) r)

  letI : Algebra k₀ (IsLocalRing.ResidueField ↥A) := (IsLocalRing.ResidueField.map ρ).toAlgebra
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A

  refine ⟨(pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) r).base '' closedPoints ↥(pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) r), ?_, ?_, ?_⟩
  · rintro z ⟨y, -, rfl⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hrpt]
  ·
    have hηF : η ∈ Set.range (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) r).base := by
      rw [Scheme.Pullback.range_fst]
      show (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base η ∈ Set.range r.base
      rw [hη]
      exact ⟨IsLocalRing.closedPoint k₀, hrpt _⟩
    obtain ⟨y, rfl⟩ := hηF
    have hy : y ∈ closure (closedPoints ↥(pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) r)) := by rw [closure_closedPoints]; trivial
    exact image_closure_subset_closure_image (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) r).base.hom.continuous ⟨y, hy, rfl⟩
  · rintro z ⟨y, hy, rfl⟩

    obtain ⟨z₀, hz₀, hz₀y⟩ := AlgebraicGeometry.Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton
      (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) r) (IsLocalRing.ResidueField ↥A) y hy
    let ζ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ G := z₀ ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) r ≫ (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
    have hζ : ζ ≫ g = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap ℤ ↥A))) := hom_specInt_ext _ _
    obtain ⟨s, e, zq, zt, hs, hz, hzt, hzφ⟩ := hsupply ζ hζ

    have hsτ : s.1 ≫ g = τ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) := by rw [s.2, hτ]
    have heτ : e.1 ≫ g = τ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) := by rw [e.2, hτ]
    let s' : Spec (CommRingCat.of ↥A) ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) := pullback.lift s.1 τ hsτ
    let e' : Spec (CommRingCat.of ↥A) ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) := pullback.lift e.1 τ heτ
    have hs'e' : s' ≫ (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) = e' ≫ (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) := by
      simp only [s', e', pullback.lift_snd]
    refine ⟨↥A, inferInstance, inferInstance, inferInstance, pullback.lift s' e' hs'e', ?_, ?_⟩
    ·
      rw [pullback.lift_fst]
      apply hinj
      change (pullback.lift s.1 τ hsτ ≫ (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))) (IsLocalRing.closedPoint ↥A) =
        (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) ((pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) r) y)
      rw [pullback.lift_fst, hs, ← hz₀y]
      simp only [ζ, Scheme.Hom.comp_apply]
    ·
      let jA : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ↥A) := Spec.map (CommRingCat.ofHom A.subtype)
      let ω : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) :=
        pullback.lift (jA ≫ s') (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
          (hom_specLoc_ext R (Ideal.span {(p : ℤ)}).primeCompl _ _)
      have hθ₁' : ∀ {T : Scheme.{0}} (u : T ⟶ pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))),
          u ≫ θ ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = u ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ≫ (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) := fun u => by
        rw [hθ₁]
      have hωθ : ω ≫ θ = zq := by
        apply pullback.hom_ext
        · rw [Category.assoc, hθ₁', ← Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, hz]
        · exact hom_specRat_ext _ _
      have hωφ : (ω ≫ φK) ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) = jA ≫ e' := by
        apply pullback.hom_ext
        · have h1 : (ω ≫ φK) ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ≫ (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) = (ω ≫ φK ≫ θ) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) := by
            rw [Category.assoc, Category.assoc, Category.assoc, hθ₁']
          rw [Category.assoc (ω ≫ φK), h1, hφ, ← Category.assoc ω θ, hωθ, ← hzφ, hzt, Category.assoc, pullback.lift_fst]
        · exact hom_specLoc_ext R (Ideal.span {(p : ℤ)}).primeCompl _ _
      have hc : jA ≫ pullback.lift s' e' hs'e' =
          ω ≫ pullback.lift (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))) (φK ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
            (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition]) := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
        · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, hωφ]
      refine ⟨ω.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)), ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hc, Scheme.Hom.comp_apply]
      congr 1
      exact specMap_base_closedPoint_eq_bot A.subtype Subtype.val_injective

end S_AlgebraicGeometry_exists_closedFibre_testCurves_of_integralPoints_through
end P2MW
export P2MW.S_AlgebraicGeometry_exists_closedFibre_testCurves_of_integralPoints_through (solution)
