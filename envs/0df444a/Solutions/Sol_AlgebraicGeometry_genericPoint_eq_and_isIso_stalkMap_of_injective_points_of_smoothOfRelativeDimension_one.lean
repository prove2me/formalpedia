-- Prove2me | solution 1 for AlgebraicGeometry.genericPoint_eq_and_isIso_stalkMap_of_injective_points_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/91d5828f-2455-53fa-b4eb-0d3d963f074f

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_genericPoint_eq_and_isIso_stalkMap_of_injective_points_of_smoothOfRelativeDimension_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open scoped IntermediateField

namespace C2aBirationalBody

theorem exists_algHom_ne_of_not_surjective {F L : Type} [Field F] [Field L] [Algebra F L]
    [CharZero F] (hns : ¬ Function.Surjective (algebraMap F L)) :
    ∃ σ₁ σ₂ : L →ₐ[F] AlgebraicClosure L, σ₁ ≠ σ₂ := by
  by_cases halg : Algebra.IsAlgebraic F L
  · obtain ⟨a, ha⟩ : ∃ a : L, a ∉ (algebraMap F L).range := by
      by_contra hall
      push Not at hall
      exact hns fun a => RingHom.mem_range.mp (hall a)
    have hint : IsIntegral F a := (halg.isAlgebraic a).isIntegral
    have hdeg : 2 ≤ Module.finrank F F⟮a⟯ := by
      rw [IntermediateField.adjoin.finrank hint]
      have h1 : (minpoly F a).natDegree ≠ 1 := fun h => ha (minpoly.natDegree_eq_one_iff.mp h)
      have hpos : 0 < (minpoly F a).natDegree := minpoly.natDegree_pos hint
      omega
    haveI : Algebra.IsSeparable F L := inferInstance
    have hsep : IsSeparable F a := Algebra.IsSeparable.isSeparable F a
    have hcard : Field.finSepDegree F F⟮a⟯ = Module.finrank F F⟮a⟯ :=
      (IntermediateField.finSepDegree_adjoin_simple_eq_finrank_iff F L a hint.isAlgebraic).mpr hsep
    have hnt : Nontrivial (Field.Emb F F⟮a⟯) := by
      have h2 : 2 ≤ Nat.card (Field.Emb F F⟮a⟯) := by
        change 2 ≤ Field.finSepDegree F F⟮a⟯
        rw [hcard]; exact hdeg
      haveI : Finite (Field.Emb F F⟮a⟯) := Nat.finite_of_card_ne_zero (by omega)
      exact (Finite.one_lt_card_iff_nontrivial).mp (by omega)
    obtain ⟨τ₁, τ₂, hτ⟩ := hnt
    haveI : Algebra.IsAlgebraic F⟮a⟯ L := Algebra.IsAlgebraic.tower_top (K := F) F⟮a⟯
    let eqv := Field.embProdEmbOfIsAlgebraic F F⟮a⟯ L
    let d : Field.Emb F⟮a⟯ L := default
    refine ⟨eqv (τ₁, d), eqv (τ₂, d), fun heq => hτ ?_⟩
    have := eqv.injective heq
    exact (Prod.mk.inj this).1
  · haveI : Algebra.Transcendental F L := Algebra.transcendental_iff_not_isAlgebraic.mpr halg
    haveI := Field.infinite_emb_of_transcendental F L
    obtain ⟨σ₁, σ₂, hne⟩ := exists_pair_ne (Field.Emb F L)
    exact ⟨σ₁, σ₂, hne⟩

theorem localHom_eq_of_comp_eq_id {A : CommRingCat.{0}} [IsLocalRing A] {K : Type} [Field K]
    (ι : CommRingCat.of K ⟶ A) (g₁ g₂ : A ⟶ CommRingCat.of K)
    [IsLocalHom g₁.hom] [IsLocalHom g₂.hom]
    (h₁ : ι ≫ g₁ = 𝟙 _) (h₂ : ι ≫ g₂ = 𝟙 _) : g₁ = g₂ := by
  have hk : ∀ (g : A ⟶ CommRingCat.of K) [IsLocalHom g.hom] (b : A),
      g.hom b = 0 ↔ b ∈ IsLocalRing.maximalIdeal A := by
    intro g _ b
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hb hu
      have hu' := hu.map g.hom
      rw [hb] at hu'
      exact not_isUnit_zero hu'
    · intro hb
      by_contra hne
      exact hb ((isUnit_map_iff g.hom b).mp (Ne.isUnit hne))
  ext a
  have e1 : g₁.hom (ι.hom (g₁.hom a)) = g₁.hom a := by
    have := congrArg (fun φ : CommRingCat.of K ⟶ CommRingCat.of K => φ.hom (g₁.hom a)) h₁
    simpa using this
  have e3 : g₂.hom (ι.hom (g₁.hom a)) = g₁.hom a := by
    have := congrArg (fun φ : CommRingCat.of K ⟶ CommRingCat.of K => φ.hom (g₁.hom a)) h₂
    simpa using this
  have hm : a - ι.hom (g₁.hom a) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hk g₁, map_sub, e1, sub_self]
  have e2 : g₂.hom (a - ι.hom (g₁.hom a)) = 0 := (hk g₂ _).mpr hm
  rw [map_sub, e3, sub_eq_zero] at e2
  exact e2.symm

theorem specHom_eq_of_base_eq {K : Type} [Field K] {X : Scheme.{0}}
    (gX : X ⟶ Spec (CommRingCat.of K)) (P P' : Spec (CommRingCat.of K) ⟶ X)
    (hP : P ≫ gX = 𝟙 _) (hP' : P' ≫ gX = 𝟙 _)
    (hpt : P.base (IsLocalRing.closedPoint K) = P'.base (IsLocalRing.closedPoint K)) :
    P = P' := by
  let e := AlgebraicGeometry.SpecToEquivOfLocalRing X (CommRingCat.of K)
  have aux : ∀ (x : X)
      (g g' : {f : X.presheaf.stalk x ⟶ CommRingCat.of K // IsLocalHom f.hom}),
      Spec.map g.1 ≫ X.fromSpecStalk x ≫ gX = 𝟙 _ →
      Spec.map g'.1 ≫ X.fromSpecStalk x ≫ gX = 𝟙 _ → g = g' := by
    intro x g g' hg hg'
    obtain ⟨ι, hι⟩ := Spec.map_surjective (X.fromSpecStalk x ≫ gX)
    rw [← hι, ← Spec.map_comp, ← Spec.map_id, Spec.map_inj] at hg hg'
    haveI := g.2
    haveI := g'.2
    exact Subtype.ext (localHom_eq_of_comp_eq_id ι g.1 g'.1 hg hg')
  have k : ∀ q q' : Σ x, {f : X.presheaf.stalk x ⟶ CommRingCat.of K // IsLocalHom f.hom},
      q.1 = q'.1 → e.symm q ≫ gX = 𝟙 _ → e.symm q' ≫ gX = 𝟙 _ → q = q' := by
    rintro ⟨x, g⟩ ⟨x', g'⟩ hxx hq hq'
    dsimp only at hxx
    subst hxx
    simp only [e, AlgebraicGeometry.SpecToEquivOfLocalRing_symm_apply, Category.assoc] at hq hq'
    rw [aux x g g' hq hq']
  apply e.injective
  exact k _ _ hpt (by rw [e.symm_apply_apply]; exact hP) (by rw [e.symm_apply_apply]; exact hP')

theorem eq_of_isClosed_of_base_eq {K : Type} [Field K] [IsAlgClosed K] {Y X : Scheme.{0}}
    (gY : Y ⟶ Spec (CommRingCat.of K)) (gX : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType gY] (h : Y ⟶ X) (hh : h ≫ gX = gY)
    (hinj : ∀ (P P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) gY),
      P.1 ≫ h = P'.1 ≫ h → P = P')
    {y₁ y₂ : Y} (hy₁ : IsClosed ({y₁} : Set Y)) (hy₂ : IsClosed ({y₂} : Set Y))
    (he : h.base y₁ = h.base y₂) : y₁ = y₂ := by
  obtain ⟨z₁, hz₁⟩ := exists_over_hom_base_closedPoint_eq_of_isClosed_singleton K gY y₁ hy₁
  obtain ⟨z₂, hz₂⟩ := exists_over_hom_base_closedPoint_eq_of_isClosed_singleton K gY y₂ hy₂
  have w₁ : z₁.left ≫ gY = 𝟙 _ := by simpa using Over.w z₁
  have w₂ : z₂.left ≫ gY = 𝟙 _ := by simpa using Over.w z₂
  let P₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) gY := ⟨z₁.left, w₁⟩
  let P₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) gY := ⟨z₂.left, w₂⟩
  have hc : P₁.1 ≫ h = P₂.1 ≫ h := by
    apply specHom_eq_of_base_eq gX
    · rw [Category.assoc, hh]; exact w₁
    · rw [Category.assoc, hh]; exact w₂
    · change h.base (z₁.left.base _) = h.base (z₂.left.base _)
      rw [hz₁, hz₂, he]
  have hP := hinj P₁ P₂ hc
  have hz : z₁.left = z₂.left := congrArg Subtype.val hP
  rw [← hz₁, ← hz₂, hz]

end C2aBirationalBody

open C2aBirationalBody in
theorem solution
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {Y X : Scheme.{0}} (gY : Y ⟶ Spec (CommRingCat.of K)) (gX : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral Y] [IsIntegral X] [IsSeparated gY] [IsSeparated gX]
    (hY : SmoothOfRelativeDimension 1 gY) (hX : SmoothOfRelativeDimension 1 gX)
    (h : Y ⟶ X) (hh : h ≫ gX = gY)
    (hinj : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K))
      (P P' : SchemeHomOver s gY), P.1 ≫ h = P'.1 ≫ h → P = P') :
    h.base (genericPoint Y) = genericPoint X ∧ IsIso (h.stalkMap (genericPoint Y)) := by
  haveI := hY
  haveI := hX
  haveI : Smooth gY := SmoothOfRelativeDimension.smooth (n := 1) (f := gY)
  haveI : LocallyOfFiniteType gY := inferInstance

  have hgen : h.base (genericPoint Y) = genericPoint X := by
    by_contra hne
    have hxc : IsClosed ({h.base (genericPoint Y)} : Set X) :=
      AlgebraicCurve.isClosed_singleton_of_ne_genericPoint gX _ hne
    have hconst : ∀ y : Y, h.base y = h.base (genericPoint Y) := by
      intro y
      have hs : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes (Set.mem_univ y)
      have hs' : h.base (genericPoint Y) ⤳ h.base y := hs.map h.continuous
      have hmem : h.base y ∈ closure ({h.base (genericPoint Y)} : Set X) :=
        specializes_iff_mem_closure.mp hs'
      rw [hxc.closure_eq] at hmem
      exact hmem
    obtain ⟨y₁, hy₁, y₂, hy₂, hne12⟩ :=
      (AlgebraicCurve.infinite_setOf_isClosed_singleton gY).nontrivial
    exact hne12 (eq_of_isClosed_of_base_eq gY gX h hh (hinj K (𝟙 _)) hy₁ hy₂
      (by rw [hconst y₁, hconst y₂]))
  refine ⟨hgen, ?_⟩

  let R : CommRingCat.{0} := X.presheaf.stalk (h.base (genericPoint Y))
  let L : CommRingCat.{0} := Y.presheaf.stalk (genericPoint Y)
  letI : Field L := inferInstanceAs (Field Y.functionField)
  have hgenF : ∀ x : X, x = genericPoint X →
      IsField (X.presheaf.stalk x) ∧ CharZero (X.presheaf.stalk x) := by
    rintro x rfl
    letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
    refine ⟨Field.toIsField _, ?_⟩
    exact (RingHom.charZero_iff (AlgebraicCurve.baseToFunctionField gX).injective).mp
      inferInstance
  have hRF : IsField R := (hgenF _ hgen).1
  haveI hR0 : CharZero R := (hgenF _ hgen).2
  letI : Field R := hRF.toField
  let φ : R ⟶ L := h.stalkMap (genericPoint Y)
  letI : Algebra R L := φ.hom.toAlgebra

  have key : ∀ (σ₁ σ₂ : L →ₐ[R] AlgebraicClosure L), σ₁ = σ₂ := by
    intro σ₁ σ₂
    let Ω : Type := AlgebraicClosure L
    let p₁ : Spec (CommRingCat.of Ω) ⟶ Y :=
      Spec.map (CommRingCat.ofHom σ₁.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y)
    let p₂ : Spec (CommRingCat.of Ω) ⟶ Y :=
      Spec.map (CommRingCat.ofHom σ₂.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y)
    have e : ∀ σ : L →ₐ[R] Ω,
        φ ≫ CommRingCat.ofHom σ.toRingHom = CommRingCat.ofHom (algebraMap R Ω) := by
      intro σ
      ext r
      exact σ.commutes r
    have hcomp : p₁ ≫ h = p₂ ≫ h := by
      simp only [p₁, p₂, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk h]
      have hφσ := congrArg
        (fun ψ : R ⟶ CommRingCat.of Ω => Spec.map ψ ≫ X.fromSpecStalk (h.base (genericPoint Y)))
        ((e σ₁).trans (e σ₂).symm)
      simp only [Spec.map_comp, Category.assoc] at hφσ
      exact hφσ
    have hover : p₂ ≫ gY = p₁ ≫ gY := by
      rw [← hh, ← Category.assoc, ← hcomp, Category.assoc]
    let P₁ : SchemeHomOver (p₁ ≫ gY) gY := ⟨p₁, rfl⟩
    let P₂ : SchemeHomOver (p₁ ≫ gY) gY := ⟨p₂, hover⟩
    have hP := hinj Ω (p₁ ≫ gY) P₁ P₂ hcomp
    have hp : p₁ = p₂ := congrArg Subtype.val hP
    let eq := AlgebraicGeometry.SpecToEquivOfLocalRing Y (CommRingCat.of Ω)
    have i₁ : IsLocalHom (CommRingCat.ofHom σ₁.toRingHom).hom := by
      rw [CommRingCat.hom_ofHom]; infer_instance
    have i₂ : IsLocalHom (CommRingCat.ofHom σ₂.toRingHom).hom := by
      rw [CommRingCat.hom_ofHom]; infer_instance
    have hq : eq.symm ⟨genericPoint Y, CommRingCat.ofHom σ₁.toRingHom, i₁⟩ =
        eq.symm ⟨genericPoint Y, CommRingCat.ofHom σ₂.toRingHom, i₂⟩ := hp
    have hq' := eq.symm.injective hq
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Subtype.mk.injEq] at hq'
    apply AlgHom.coe_ringHom_injective
    exact congrArg CommRingCat.Hom.hom hq'
  have hinjφ : Function.Injective φ.hom := φ.hom.injective
  have hsurj : Function.Surjective φ.hom := by
    by_contra hns
    obtain ⟨σ₁, σ₂, hne⟩ := exists_algHom_ne_of_not_surjective (F := R) (L := L) hns
    exact hne (key σ₁ σ₂)
  exact (ConcreteCategory.isIso_iff_bijective φ).mpr ⟨hinjφ, hsurj⟩

end S_AlgebraicGeometry_genericPoint_eq_and_isIso_stalkMap_of_injective_points_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_genericPoint_eq_and_isIso_stalkMap_of_injective_points_of_smoothOfRelativeDimension_one (solution)
