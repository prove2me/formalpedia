-- Prove2me | solution 1 for AlgebraicGeometry.SmoothOfRelativeDimension.finrank_eq_pow_of_isPullback_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2ff9d54f-0ade-5084-8025-6c9055117710

import Mathlib
import Theorems.Thm_RingHom_Etale_isPushout_frobenius
import Theorems.Thm_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow
import Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_exists_etale_aeval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_finrank_eq_pow_of_isPullback_frobenius

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobRankMain

theorem frobenius_mvPolynomial (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
    [PerfectRing k p] (n : ℕ) :
    (frobenius (MvPolynomial (Fin n) k) p).Finite ∧ (frobenius (MvPolynomial (Fin n) k) p).Flat ∧
      ∀ q, (frobenius (MvPolynomial (Fin n) k) p).finrank q = p ^ n := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨hfin, hflat, hrank⟩ :=
    MvPolynomial.finite_and_flat_and_finrank_expand_eq_pow k (Fin n) p hp
  set E : MvPolynomial (Fin n) k →+* MvPolynomial (Fin n) k :=
    (MvPolynomial.expand p (σ := Fin n) (R := k)).toRingHom with hE
  let ι : MvPolynomial (Fin n) k ≃+* MvPolynomial (Fin n) k :=
    MvPolynomial.mapEquiv (Fin n) (frobeniusEquiv k p)
  have hι : ∀ f, ι f = MvPolynomial.map (frobenius k p) f := fun f => rfl
  have hcomp : frobenius (MvPolynomial (Fin n) k) p = E.comp ι.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hι,
        MvPolynomial.map_C, hE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.expand_C, frobenius_def, frobenius_def, MvPolynomial.C_pow]
    · intro i
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hι,
        MvPolynomial.map_X, hE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.expand_X, frobenius_def]
  rw [hcomp]
  refine ⟨hfin.comp (RingHom.Finite.of_surjective _ ι.surjective),
    (RingHom.Flat.of_bijective ι.bijective).comp hflat, fun q => ?_⟩
  rw [RingHom.finrank_comp_right_of_bijective ι.toRingHom E ι.bijective hfin hflat q
    (PrimeSpectrum.comap ι.symm.toRingHom q) ?_, hrank]
  · simp
  · rw [← PrimeSpectrum.comap_comp_apply]
    simp

theorem kunz {k B : Type u} [CommRing k] [CommRing B] (p : ℕ) [Fact p.Prime] [CharP k p]
    [PerfectRing k p] [CharP B p] [Algebra k B] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k B] :
    (frobenius B p).Finite ∧ (frobenius B p).Flat ∧ ∀ q, (frobenius B p).finrank q = p ^ n := by
  obtain ⟨x, hx⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_aeval (R := k) (S := B) n
  set φ : MvPolynomial (Fin n) k →+* B :=
    (MvPolynomial.aeval x : MvPolynomial (Fin n) k →ₐ[k] B).toRingHom with hφ
  have sq := RingHom.Etale.isPushout_frobenius p hx
  obtain ⟨hAfin, hAflat, hArank⟩ := frobenius_mvPolynomial k p n
  refine ⟨?_, ?_, fun q => ?_⟩
  · have hst : (RingHom.toMorphismProperty @RingHom.Finite).IsStableUnderCobaseChange :=
      (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).mpr
        RingHom.finite_isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq.flip
      (show (RingHom.toMorphismProperty @RingHom.Finite) _ from hAfin)
  · have hst : (RingHom.toMorphismProperty @RingHom.Flat).IsStableUnderCobaseChange :=
      (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).mpr
        RingHom.Flat.isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq.flip
      (show (RingHom.toMorphismProperty @RingHom.Flat) _ from hAflat)
  · have := CommRingCat.finrank_eq_of_isPushout sq hAflat hAfin q
    simpa [hArank] using this

lemma comap_frobenius {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (q : PrimeSpectrum R) : PrimeSpectrum.comap (frobenius R p) q = q := by
  ext a
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, frobenius_def]
  exact q.2.pow_mem_iff_mem p (Fact.out : p.Prime).pos

theorem main (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (pr : X' ⟶ X)
    (hpr : IsPullback pr f' f (Spec.map (CommRingCat.ofHom (frobenius k p))))
    (F : X ⟶ X') (hF : F ≫ f' = f)
    (hFrob : ∀ (B : Type u) [CommRing B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
      x ≫ F ≫ pr = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x) :
    ∀ y : ↥X', F.finrank y = p ^ n := by
  classical
  have hp : p.Prime := Fact.out

  have chart : ∀ x : X, ∃ (V : X.Opens) (_ : IsAffineOpen V), x ∈ V ∧
      ∃ (_ : CharP Γ(X, V) p) (_ : Algebra k Γ(X, V)),
        Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V) := by
    intro x
    obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x

    have hUtop : U = ⊤ := by
      haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
        inferInstanceAs (Subsingleton (PrimeSpectrum k))
      refine eq_top_iff.mpr fun y _ => ?_
      have hfx : f x ∈ U := e hxV
      rwa [Subsingleton.elim y (f x)]
    subst hUtop

    obtain ⟨z, hz⟩ : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hxV
    have z' : PrimeSpectrum Γ(X, V) := z
    haveI : Nontrivial Γ(X, V) := z'.nontrivial

    let ek : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    let ψ : k →+* Γ(X, V) := (f.appLE ⊤ V e).hom.comp ek.toRingHom
    have hψ : ψ.IsStandardSmoothOfRelativeDimension n :=
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).2 _ ek hstd
    haveI : CharP Γ(X, V) p := charP_of_injective_ringHom ψ.injective p
    exact ⟨V, hV, hxV, ‹_›, ψ.toAlgebra, hψ⟩
  choose V hV hxV hchar halg hstd using chart

  set Φ : X ⟶ X := F ≫ pr with hΦdef
  have hsq : ∀ x : X, (hV x).fromSpec ≫ Φ =
      Spec.map (CommRingCat.ofHom (frobenius Γ(X, V x) p)) ≫ (hV x).fromSpec := by
    intro x
    haveI := hchar x
    have := hFrob (Γ(X, V x)) (hV x).fromSpec
    simpa only [hΦdef] using this

  have hmem : ∀ x : X, x ∈ Set.range (hV x).fromSpec := fun x => by
    rw [(hV x).range_fromSpec]; exact hxV x
  have hfix : ∀ x : X, Φ x = x := by
    intro x
    obtain ⟨z, hz⟩ := hmem x
    haveI := hchar x
    conv_lhs => rw [← hz]
    rw [← Scheme.Hom.comp_apply, hsq x, Scheme.Hom.comp_apply, Spec.map_apply,
      CommRingCat.hom_ofHom, comap_frobenius, hz]

  have hpb : ∀ x : X, IsPullback (Spec.map (CommRingCat.ofHom (frobenius Γ(X, V x) p)))
      (hV x).fromSpec (hV x).fromSpec Φ := by
    intro x
    refine IsOpenImmersion.isPullback _ _ _ _ (hsq x) ?_
    ext v
    change Φ v ∈ ((hV x).fromSpec.opensRange : Set X) ↔ v ∈ ((hV x).fromSpec.opensRange : Set X)
    rw [hfix v]

  have hK : ∀ x : X, (frobenius Γ(X, V x) p).Finite ∧ (frobenius Γ(X, V x) p).Flat ∧
      ∀ q, (frobenius Γ(X, V x) p).finrank q = p ^ n := by
    intro x
    haveI := hchar x
    letI := halg x
    haveI := hstd x
    exact kunz (k := k) p n

  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers (J := ↥X) (fun x => Spec Γ(X, V x))
    (fun x => (hV x).fromSpec) (fun x => by
      obtain ⟨z, hz⟩ := hmem x
      exact ⟨x, z, hz⟩)
  have hpbHom : ∀ x : X, 𝒰.pullbackHom Φ x =
      (hpb x).flip.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom (frobenius Γ(X, V x) p)) := by
    intro x
    change pullback.snd Φ ((hV x).fromSpec) = _
    rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
  haveI : Flat Φ := by
    refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun x => ?_
    have : Flat ((hpb x).flip.isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom (frobenius Γ(X, V x) p))) := by
      rw [MorphismProperty.cancel_left_of_respectsIso @Flat]
      exact Flat.SpecMap_iff.mpr (hK x).2.1
    rw [hpbHom]
    exact this
  haveI : IsFinite Φ := by
    refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun x => ?_
    have : IsFinite ((hpb x).flip.isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom (frobenius Γ(X, V x) p))) := by
      rw [MorphismProperty.cancel_left_of_respectsIso @IsFinite]
      exact (IsFinite.SpecMap_iff _).mpr (hK x).1
    rw [hpbHom]
    exact this

  have hΦrank : ∀ x : X, Φ.finrank x = p ^ n := by
    intro x
    obtain ⟨z, hz⟩ := hmem x
    rw [← hz, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (hpb x).flip z,
      Scheme.Hom.finrank_SpecMap_eq_finrank (f := CommRingCat.ofHom (frobenius Γ(X, V x) p))
        (hK x).1 (hK x).2.1]
    exact (hK x).2.2 z

  haveI : IsIso (CommRingCat.ofHom (frobenius k p)) :=
    (frobeniusEquiv k p).toCommRingCatIso.isIso_hom
  haveI : IsIso (Spec.map (CommRingCat.ofHom (frobenius k p))) := inferInstance
  haveI : IsIso pr := hpr.isIso_fst_of_isIso
  intro y
  have hsqF : IsPullback (𝟙 X) F Φ pr := IsPullback.of_horiz_isIso ⟨by simp [hΦdef]⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hsqF y]
  exact hΦrank (pr y)

end FrobRankMain

theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (pr : X' ⟶ X)
    (hpr : IsPullback pr f' f (Spec.map (CommRingCat.ofHom (frobenius k p))))
    (F : X ⟶ X') (hF : F ≫ f' = f)
    (hFrob : ∀ (B : Type u) [CommRing B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
      x ≫ F ≫ pr = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x) :
    ∀ y : ↥X', F.finrank y = p ^ n :=
  FrobRankMain.main k p f f' n pr hpr F hF hFrob

end S_AlgebraicGeometry_SmoothOfRelativeDimension_finrank_eq_pow_of_isPullback_frobenius
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_finrank_eq_pow_of_isPullback_frobenius (solution)
