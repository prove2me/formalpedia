-- Prove2me | solution 1 for AlgebraicGeometry.TowerQuotientDatum.exists_baseChange_of_flat_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7fb491a8-e6d6-5fbb-829c-b4ee28d97ef1

import Mathlib
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Theorems.Thm_AlgebraicGeometry_flat_specMap_quotientMap_pow_of_flat
import Theorems.Thm_AlgebraicGeometry_epi_morphismRestrict_of_isPullback_of_flat
import Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_univ_loc_of_isPullback_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_baseChange_of_flat_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace DQBC13

theorem quotientMap_comp_factor {𝒪 S : Type} [CommRing 𝒪] [CommRing S] [Algebra 𝒪 S] (π : 𝒪) (n : ℕ)
    (h₁ : Ideal.span {π ^ (n + 1)} ≤ (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}).comap (algebraMap 𝒪 S))
    (h₂ : Ideal.span {π ^ (n + 1 + 1)} ≤ (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1 + 1)}).comap (algebraMap 𝒪 S))
    (h₃ : Ideal.span {π ^ (n + 1 + 1)} ≤ Ideal.span {π ^ (n + 1)})
    (h₄ : Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1 + 1)} ≤ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) :
    (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S) h₁).comp (Ideal.Quotient.factor h₃) =
      (Ideal.Quotient.factor h₄).comp (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1 + 1)}) (algebraMap 𝒪 S) h₂) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

end DQBC13

open DQBC13 in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (haff : ∀ (n : ℕ) (S : Set (X n)), S.Finite → ∃ U : (X n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X n)))
    (G : Type) [Group G] [Finite G] (a : ∀ n : ℕ, G →* Aut (X n))
    (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)

    (S : Type) [CommRing S] [Algebra 𝒪 S] [Module.Flat 𝒪 S]
    (X' : ℕ → Scheme.{0}) (xb' : ∀ n : ℕ, X' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
    (xt' : ∀ n : ℕ, X' n ⟶ X' (n + 1)) (a' : ∀ n : ℕ, G →* Aut (X' n))
    (q : ∀ n : ℕ, X' n ⟶ X n)
    (hq : ∀ n : ℕ, IsPullback (q n) (xb' n) (xb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hcart' : ∀ n : ℕ, IsPullback (xt' n) (xb' n) (xb' (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1))))))))
    (hq_xt : ∀ n : ℕ, xt' n ≫ q (n + 1) = q n ≫ xt n)
    (hq_a : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ q n = q n ≫ (a n g).hom)
    (ha'_over : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ xb' n = xb' n) :
    ∃ (D' : TowerQuotientDatum S (algebraMap 𝒪 S π) X' xb' xt' G a') (r : ∀ n : ℕ, D'.Y n ⟶ D.Y n),
      (∀ n : ℕ, IsPullback (r n) (D'.yb n) (D.yb n)
        (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))) ∧
      (∀ n : ℕ, D'.p n ≫ r n = q n ≫ D.p n) ∧
      (∀ n : ℕ, D'.yt n ≫ r (n + 1) = r n ≫ D.yt n) := by
  classical

  have hle : ∀ n : ℕ, Ideal.span {π ^ (n + 1)} ≤ (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}).comap (algebraMap 𝒪 S) := fun n => by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl
  have hle𝒪 : ∀ n : ℕ, Ideal.span {π ^ (n + 1 + 1)} ≤ Ideal.span {π ^ (n + 1)} := fun n =>
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))
  have hleS : ∀ n : ℕ, Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1 + 1)} ≤ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)} := fun n =>
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1)))
  let σ : ∀ n : ℕ, Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})) ⟶
      Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) := fun n =>
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S) (hle n)))
  let τ : ∀ n : ℕ, Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)})) :=
    fun n => Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hle𝒪 n)))
  let τ' : ∀ n : ℕ, Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})) ⟶
      Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1 + 1)})) :=
    fun n => Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hleS n)))
  have hστ : ∀ n : ℕ, σ n ≫ τ n = τ' n ≫ σ (n + 1) := fun n => by
    simp only [σ, τ, τ', ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [quotientMap_comp_factor π n (hle n) (hle (n + 1)) (hle𝒪 n) (hleS n)]

  let Y' : ℕ → Scheme.{0} := fun n => pullback (D.yb n) (σ n)
  obtain ⟨r, hr⟩ : ∃ r : ∀ n : ℕ, Y' n ⟶ D.Y n, ∀ n, r n = pullback.fst (D.yb n) (σ n) := ⟨_, fun _ => rfl⟩
  obtain ⟨yb', hyb'⟩ : ∃ yb' : ∀ n : ℕ, Y' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})),
      ∀ n, yb' n = pullback.snd (D.yb n) (σ n) := ⟨_, fun _ => rfl⟩
  have hY' : ∀ n : ℕ, r n ≫ D.yb n = yb' n ≫ σ n := fun n => by rw [hr, hyb']; exact pullback.condition
  let p' : ∀ n : ℕ, X' n ⟶ Y' n := fun n =>
    pullback.lift (q n ≫ D.p n) (xb' n) (by rw [Category.assoc, D.p_over]; exact (hq n).w)
  have hp'r : ∀ n : ℕ, p' n ≫ r n = q n ≫ D.p n := fun n => by rw [hr]; exact pullback.lift_fst _ _ _
  have hp'b : ∀ n : ℕ, p' n ≫ yb' n = xb' n := fun n => by rw [hyb']; exact pullback.lift_snd _ _ _
  let yt' : ∀ n : ℕ, Y' n ⟶ Y' (n + 1) := fun n =>
    pullback.lift (r n ≫ D.yt n) (yb' n ≫ τ' n) (by
      rw [Category.assoc, (D.yt_isPullback n).w, ← Category.assoc, hY' n, Category.assoc, Category.assoc]
      exact congrArg (yb' n ≫ ·) (hστ n))
  have hyt'r : ∀ n : ℕ, yt' n ≫ r (n + 1) = r n ≫ D.yt n := fun n => by rw [hr]; exact pullback.lift_fst _ _ _
  have hyt'b : ∀ n : ℕ, yt' n ≫ yb' (n + 1) = yb' n ≫ τ' n := fun n => by rw [hyb']; exact pullback.lift_snd _ _ _

  have hp'r' : ∀ (n : ℕ) {Z : Scheme.{0}} (f : D.Y n ⟶ Z), p' n ≫ r n ≫ f = q n ≫ D.p n ≫ f := fun n Z f => by
    rw [← Category.assoc, hp'r, Category.assoc]
  have hp'b' : ∀ (n : ℕ) {Z : Scheme.{0}} (f : _ ⟶ Z), p' n ≫ yb' n ≫ f = xb' n ≫ f := fun n Z f => by
    rw [← Category.assoc, hp'b]
  have hyt'r' : ∀ (n : ℕ) {Z : Scheme.{0}} (f : D.Y (n + 1) ⟶ Z), yt' n ≫ r (n + 1) ≫ f = r n ≫ D.yt n ≫ f := fun n Z f => by
    rw [← Category.assoc, hyt'r, Category.assoc]
  have hyt'b' : ∀ (n : ℕ) {Z : Scheme.{0}} (f : _ ⟶ Z), yt' n ≫ yb' (n + 1) ≫ f = yb' n ≫ τ' n ≫ f := fun n Z f => by
    rw [← Category.assoc, hyt'b, Category.assoc]

  have hsq : ∀ n : ℕ, IsPullback (q n) (p' n) (D.p n) (r n) := fun n => by
    refine IsPullback.of_bot ?_ (hp'r n).symm (show IsPullback (r n) (yb' n) (D.yb n) (σ n) by
      rw [hr, hyb']; exact IsPullback.of_hasPullback (D.yb n) (σ n))
    rw [hp'b, D.p_over]; exact hq n
  have hbase : ∀ n : ℕ, IsPullback (r n) (yb' n) (D.yb n) (σ n) := fun n => by
    rw [hr, hyb']; exact IsPullback.of_hasPullback (D.yb n) (σ n)
  have hp_xt : ∀ n : ℕ, xt' n ≫ p' (n + 1) = p' n ≫ yt' n := by
    intro n
    apply pullback.hom_ext
    · rw [← hr]
      simp only [Category.assoc, hp'r, hyt'r, hp'r']
      rw [← Category.assoc, hq_xt, Category.assoc, D.p_xt]
    · rw [← hyb']
      simp only [Category.assoc, hp'b, hyt'b, hp'b']
      exact (hcart' n).w
  have hp_inv : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ p' n = p' n := by
    intro n g
    apply pullback.hom_ext
    · rw [← hr]
      simp only [Category.assoc, hp'r]
      rw [← Category.assoc, hq_a, Category.assoc, D.p_inv]
    · rw [← hyb']
      simp only [Category.assoc, hp'b]
      exact ha'_over n g

  have hrflat : ∀ n : ℕ, Flat (r n) := fun n =>
    MorphismProperty.of_isPullback (P := @Flat) (hbase n).flip
      (AlgebraicGeometry.flat_specMap_quotientMap_pow_of_flat 𝒪 π S n)
  refine ⟨{ Y := Y', yb := yb', yt := yt',
            yt_isPullback := ?_, yb_isProper := ?_, yb_flat := ?_,
            p := p', p_over := hp'b, p_xt := ?_, p_isPullback := ?_, p_inv := ?_, p_isFinite := ?_,
            p_surjective := ?_, p_epi_loc := ?_, univ_loc := ?_, fib := ?_, adicFib := ?_ }, r, ?_, hp'r, hyt'r⟩
  ·
    intro n
    have outer := (hbase n).paste_horiz (D.yt_isPullback n)
    rw [← hyt'r, hστ] at outer
    exact outer.of_right (hyt'b n) (hbase (n + 1))
  ·
    intro n; haveI := D.yb_isProper n; rw [hyb']; infer_instance
  ·
    intro n; haveI := D.yb_flat n; rw [hyb']; infer_instance
  ·
    exact hp_xt
  ·
    intro n
    have outer := (hsq n).paste_horiz (D.p_isPullback n)
    rw [← hq_xt, ← hyt'r] at outer
    exact outer.of_right (hp_xt n) (hsq (n + 1))
  ·
    exact hp_inv
  ·
    intro n
    haveI := D.p_isFinite n
    exact MorphismProperty.of_isPullback (P := @IsFinite) (hsq n) (D.p_isFinite n)
  ·
    intro n
    exact MorphismProperty.of_isPullback (P := @Surjective) (hsq n) (D.p_surjective n)
  ·
    intro n U
    haveI := D.p_isFinite n
    haveI : Surjective (D.p n) := D.p_surjective n
    haveI := hrflat n
    exact AlgebraicGeometry.epi_morphismRestrict_of_isPullback_of_flat (D.p n) (r n) (p' n) (q n) (hsq n) (D.p_epi_loc n) U
  ·
    exact AlgebraicGeometry.TowerQuotientDatum.univ_loc_of_isPullback_of_flat 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat haff
      G a ha_over ha_xt D S X' xb' xt' a' q hq hcart' hq_xt hq_a ha'_over Y' yb' yt' p' r hbase hsq hyt'r hyt'b hp'b hp_inv hp_xt
  ·
    intro n k _ _ y
    obtain ⟨⟨x₀, hx₀⟩, horb⟩ := D.fib n k (y ≫ r n)
    refine ⟨⟨(hsq n).lift x₀ y (by rw [hx₀]), (hsq n).lift_snd _ _ _⟩, ?_⟩
    intro x x' hx
    have hxq : (x ≫ q n) ≫ D.p n = y ≫ r n := by rw [Category.assoc, ← hp'r, ← Category.assoc, hx]
    constructor
    · intro hx'
      have hx'q : (x' ≫ q n) ≫ D.p n = y ≫ r n := by rw [Category.assoc, ← hp'r, ← Category.assoc, hx']
      obtain ⟨g, hg⟩ := ((horb (x ≫ q n) (x' ≫ q n) hxq).1 hx'q)
      refine ⟨g, (hsq n).hom_ext ?_ ?_⟩
      · rw [hg, Category.assoc, Category.assoc, hq_a]
      · rw [hx', Category.assoc, hp_inv, hx]
    · rintro ⟨g, rfl⟩
      rw [Category.assoc, hp_inv, hx]
  ·
    intro R _ _ _ _ hRc hRac y hyb hyt
    letI instOR : Algebra 𝒪 R := ((algebraMap S R).comp (algebraMap 𝒪 S)).toAlgebra
    have hϖ : algebraMap 𝒪 R π = algebraMap S R (algebraMap 𝒪 S π) := rfl

    have hyb₀ : ∀ n : ℕ, (y n ≫ r n) ≫ D.yb n =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)}) (algebraMap 𝒪 R)
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) := by
      intro n
      rw [Category.assoc, hY', ← Category.assoc, hyb n]
      simp only [σ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      apply Ideal.Quotient.ringHom_ext
      ext x
      rfl
    have hyt₀ : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ (y (n + 1) ≫ r (n + 1)) =
        (y n ≫ r n) ≫ D.yt n := by
      intro n
      rw [← Category.assoc, hyt n, Category.assoc, hyt'r, Category.assoc]
    obtain ⟨⟨x₀, hx₀p, hx₀t⟩, huniq⟩ := D.adicFib R hRc hRac (fun n => y n ≫ r n) hyb₀ hyt₀
    refine ⟨⟨fun n => (hsq n).lift (x₀ n) (y n) (hx₀p n), fun n => (hsq n).lift_snd _ _ _, fun n => ?_⟩, ?_⟩
    · apply (hsq (n + 1)).hom_ext
      · beta_reduce
        rw [Category.assoc, (hsq (n + 1)).lift_fst, hx₀t n, Category.assoc, hq_xt, ← Category.assoc, (hsq n).lift_fst]
      · beta_reduce
        rw [Category.assoc, (hsq (n + 1)).lift_snd, Category.assoc, hp_xt, ← Category.assoc, (hsq n).lift_snd]
        exact hyt n
    · intro x x' hx hx' hxt hx't
      have key : ∀ z : ∀ n : ℕ, _ ⟶ X' n, (∀ n, z n ≫ p' n = y n) →
          (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
            (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ z (n + 1) = z n ≫ xt' n) →
          (∀ n, (z n ≫ q n) ≫ D.p n = y n ≫ r n) ∧
          (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
            (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ (z (n + 1) ≫ q (n + 1)) =
            (z n ≫ q n) ≫ xt n) := by
        intro z hz hzt
        refine ⟨fun n => by rw [Category.assoc, ← hp'r, ← Category.assoc, hz], fun n => ?_⟩
        rw [← Category.assoc, hzt n, Category.assoc, hq_xt, Category.assoc]
      obtain ⟨h1, h2⟩ := key x hx hxt
      obtain ⟨h1', h2'⟩ := key x' hx' hx't
      obtain ⟨g, hg⟩ := huniq (fun n => x n ≫ q n) (fun n => x' n ≫ q n) h1 h1' h2 h2'
      refine ⟨g, fun n => (hsq n).hom_ext ?_ ?_⟩
      · rw [hg n, Category.assoc, Category.assoc, hq_a]
      · rw [hx', Category.assoc, hp_inv, hx]
  ·
    intro n
    show IsPullback (r n) (yb' n) (D.yb n) (σ n)
    rw [hr, hyb']
    exact IsPullback.of_hasPullback (D.yb n) (σ n)

end S_AlgebraicGeometry_TowerQuotientDatum_exists_baseChange_of_flat_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_baseChange_of_flat_of_isPullback (solution)
