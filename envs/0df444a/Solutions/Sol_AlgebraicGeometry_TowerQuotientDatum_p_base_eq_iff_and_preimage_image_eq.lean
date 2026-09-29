-- Prove2me | solution 1 for AlgebraicGeometry.TowerQuotientDatum.p_base_eq_iff_and_preimage_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/19acaf52-bacc-5eac-8cd9-63affaa8defd

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_p_base_eq_iff_and_preimage_image_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem G4.exists_point_through {X Y : Scheme.{0}} (p : X ⟶ Y) [IsIntegralHom p]
    (k : Type) [Field k] [IsAlgClosed k] (y : Spec (CommRingCat.of k) ⟶ Y)
    (x : X) (hx : p.base x ∈ Set.range y.base) :
    ∃ xt : Spec (CommRingCat.of k) ⟶ X, xt ≫ p = y ∧ ∀ s : Spec (CommRingCat.of k), xt.base s = x := by
  classical
  let F := pullback p y
  let snd : F ⟶ Spec (CommRingCat.of k) := pullback.snd p y
  haveI : IsIntegralHom snd := inferInstance
  haveI : IsAffine F := isAffine_of_isAffineHom snd

  have hm : x ∈ Set.range (pullback.fst p y).base := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨m, hm⟩ := hm

  let eK := Scheme.ΓSpecIso (CommRingCat.of k)
  let φ : k →+* Γ(F, ⊤) := snd.appTop.hom.comp eK.inv.hom
  letI alg : Algebra k Γ(F, ⊤) := φ.toAlgebra
  have hφint : φ.IsIntegral := by
    have h1 : snd.appTop.hom.IsIntegral := IsIntegralHom.isIntegral_app snd ⊤ (isAffineOpen_top _)
    have h2 : (eK.inv.hom).IsIntegral :=
      RingHom.isIntegral_of_surjective _ eK.symm.commRingCatIsoToRingEquiv.surjective
    exact RingHom.IsIntegral.trans _ _ h2 h1
  haveI : Algebra.IsIntegral k Γ(F, ⊤) := ⟨fun b => hφint b⟩

  let 𝔭 : Ideal Γ(F, ⊤) := (F.isoSpec.hom.base m).asIdeal
  haveI h𝔭 : 𝔭.IsPrime := (F.isoSpec.hom.base m).isPrime
  haveI : IsDomain (Γ(F, ⊤) ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  haveI : Algebra.IsIntegral k (Γ(F, ⊤) ⧸ 𝔭) :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ k 𝔭) (Ideal.Quotient.mkₐ_surjective k 𝔭)
  haveI : Algebra.IsAlgebraic k (Γ(F, ⊤) ⧸ 𝔭) := Algebra.IsIntegral.isAlgebraic
  let ψ : (Γ(F, ⊤) ⧸ 𝔭) →ₐ[k] k := IsAlgClosed.lift
  let θ : Γ(F, ⊤) →ₐ[k] k := ψ.comp (Ideal.Quotient.mkₐ k 𝔭)

  have h𝔭max : 𝔭.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := k) 𝔭 ?_
    rcases Ideal.eq_bot_or_top (𝔭.comap (algebraMap k Γ(F, ⊤))) with h | h
    · rw [h]; exact Ideal.bot_isMaximal
    · exact absurd h (Ideal.comap_ne_top _ h𝔭.ne_top)
  have hker : RingHom.ker θ.toRingHom = 𝔭 := by
    symm
    refine h𝔭max.eq_of_le (RingHom.ker_ne_top _) (fun b hb => ?_)
    rw [RingHom.mem_ker]
    change ψ (Ideal.Quotient.mk 𝔭 b) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hb, map_zero]

  let σ : Spec (CommRingCat.of k) ⟶ F := Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ F.isoSpec.inv
  have hσ : σ ≫ snd = 𝟙 _ := by
    have hnat : F.isoSpec.inv ≫ snd = Spec.map snd.appTop ≫ (Spec (CommRingCat.of k)).isoSpec.inv :=
      (Scheme.isoSpec_inv_naturality snd).symm
    simp only [σ, Category.assoc, hnat, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    have : eK.inv ≫ snd.appTop ≫ CommRingCat.ofHom θ.toRingHom = 𝟙 _ := by
      ext c
      exact θ.commutes c
    rw [this, Spec.map_id]
  have hσm : ∀ s : Spec (CommRingCat.of k), σ.base s = m := by
    intro s
    have h1 : (Spec.map (CommRingCat.ofHom θ.toRingHom)).base s = F.isoSpec.hom.base m := by
      apply PrimeSpectrum.ext
      change Ideal.comap θ.toRingHom s.asIdeal = 𝔭
      have hs : s.asIdeal = ⊥ := Ideal.eq_bot_of_prime s.asIdeal
      rw [hs, ← RingHom.ker_eq_comap_bot, hker]
    change F.isoSpec.inv.base ((Spec.map (CommRingCat.ofHom θ.toRingHom)).base s) = m
    rw [h1, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  refine ⟨σ ≫ pullback.fst p y, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (σ ≫ snd) ≫ y = y
    rw [hσ, Category.id_comp]
  · intro s
    rw [Scheme.Hom.comp_apply, hσm s, hm]

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪}
    {X : ℕ → Scheme.{0}} {xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))}
    {xt : ∀ n : ℕ, X n ⟶ X (n + 1)}
    {G : Type} [Group G] {a : ∀ n : ℕ, G →* Aut (X n)}
    (D : TowerQuotientDatum 𝒪 π X xb xt G a) (n : ℕ) :
    (∀ x x' : X n, (D.p n).base x = (D.p n).base x' ↔ ∃ g : G, (a n g).hom.base x = x') ∧
    ∀ W : Set (X n), (D.p n).base ⁻¹' ((D.p n).base '' W) = ⋃ g : G, (a n g).hom.base '' W := by
  classical
  haveI : IsFinite (D.p n) := D.p_isFinite n
  have key : ∀ x x' : X n, (D.p n).base x = (D.p n).base x' ↔ ∃ g : G, (a n g).hom.base x = x' := by
    intro x x'
    constructor
    · intro hxx
      let y := (D.p n).base x
      let κ := (D.Y n).residueField y
      let k := AlgebraicClosure ↑κ
      let yt : Spec (CommRingCat.of k) ⟶ D.Y n :=
        Spec.map (CommRingCat.ofHom (algebraMap ↑κ k)) ≫ (D.Y n).fromSpecResidueField y
      have hyt : ∀ s : Spec (CommRingCat.of k), yt.base s = y := by
        intro s
        rw [Scheme.Hom.comp_apply]
        exact Scheme.fromSpecResidueField_apply _ _
      let s₀ : Spec (CommRingCat.of k) := ⟨⊥, Ideal.isPrime_bot⟩
      have hx : (D.p n).base x ∈ Set.range yt.base := ⟨s₀, hyt s₀⟩
      have hx' : (D.p n).base x' ∈ Set.range yt.base := ⟨s₀, (hyt s₀).trans hxx⟩
      obtain ⟨xt, hxt, hxtb⟩ := G4.exists_point_through (D.p n) k yt x hx
      obtain ⟨xt', hxt', hxtb'⟩ := G4.exists_point_through (D.p n) k yt x' hx'
      obtain ⟨g, hg⟩ := ((D.fib n k yt).2 xt xt' hxt).1 hxt'
      refine ⟨g, ?_⟩
      rw [← hxtb s₀, ← Scheme.Hom.comp_apply, ← hg, hxtb' s₀]
    · rintro ⟨g, rfl⟩
      rw [← Scheme.Hom.comp_apply, D.p_inv]
  refine ⟨key, ?_⟩
  intro W
  ext x'
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hxW, hpx⟩
    obtain ⟨g, hg⟩ := (key x x').1 hpx
    exact ⟨g, x, hxW, hg⟩
  · rintro ⟨g, x, hxW, hg⟩
    exact ⟨x, hxW, (key x x').2 ⟨g, hg⟩⟩

end S_AlgebraicGeometry_TowerQuotientDatum_p_base_eq_iff_and_preimage_image_eq
end P2MW
export P2MW.S_AlgebraicGeometry_TowerQuotientDatum_p_base_eq_iff_and_preimage_image_eq (solution)
