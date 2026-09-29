-- Prove2me | solution 1 for AlgebraicGeometry.TowerQuotientDatum.exists_ringEquiv_fixedPoints_quotient_basicOpen_of_isPullback_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/12f9a361-cbb6-5b4d-95ee-e4c6608a1335

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Theorems.Thm_AlgebraicGeometry_exists_addMonoidHom_tmul_sections_preimage_of_isPullback
import Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_quotient_sections_of_isPullback_of_flat
import Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_basicOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_fixedPoints_quotient_basicOpen_of_isPullback_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

namespace ChartAsm

theorem smul_injective_of_flat (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (π : 𝒪) (hπ : π ≠ 0)
    (S : Type) [CommRing S] [Algebra 𝒪 S] [Module.Flat 𝒪 S] : ∀ s : S, algebraMap 𝒪 S π * s = 0 → s = 0 := by
  intro s hs
  have hinj0 : Function.Injective (π • (LinearMap.id : 𝒪 →ₗ[𝒪] 𝒪)) := by
    intro x y hxy
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at hxy
    exact mul_left_cancel₀ hπ hxy
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := S) _ hinj0
  have h1 : LinearMap.rTensor S (π • (LinearMap.id : 𝒪 →ₗ[𝒪] 𝒪)) ((1 : 𝒪) ⊗ₜ[𝒪] s) = 0 := by
    rw [LinearMap.rTensor_tmul, LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.smul_tmul, Algebra.smul_def, hs,
      TensorProduct.tmul_zero]
  have h2 : (1 : 𝒪) ⊗ₜ[𝒪] s = 0 := hinj (by rw [h1, map_zero])
  have h3 := congrArg (TensorProduct.lid 𝒪 S) h2
  rwa [TensorProduct.lid_tmul, one_smul, map_zero] at h3

theorem comm_of_isPullback {X₀ X₁ X₀' X₁' B₀ B₁ C₁ : Scheme.{0}} {q₀ : X₀' ⟶ X₀} {q₁ : X₁' ⟶ X₁} {xb₀ : X₀' ⟶ B₀}
    {xb₁ : X₁' ⟶ B₁} {xt : X₀ ⟶ X₁} {xt' : X₀' ⟶ X₁'} {t : B₀ ⟶ B₁} {α₀ : X₀ ⟶ X₀} {α₁ : X₁ ⟶ X₁}
    {α₀' : X₀' ⟶ X₀'} {α₁' : X₁' ⟶ X₁'} {xbX₁ : X₁ ⟶ C₁} {g₁ : B₁ ⟶ C₁}
    (hq₁ : IsPullback q₁ xb₁ xbX₁ g₁) (hq_xt : xt' ≫ q₁ = q₀ ≫ xt) (hq_a₀ : α₀' ≫ q₀ = q₀ ≫ α₀)
    (hq_a₁ : α₁' ≫ q₁ = q₁ ≫ α₁) (ha_xt : α₀ ≫ xt = xt ≫ α₁) (hw : xt' ≫ xb₁ = xb₀ ≫ t) (ha₀ : α₀' ≫ xb₀ = xb₀)
    (ha₁ : α₁' ≫ xb₁ = xb₁) : α₀' ≫ xt' = xt' ≫ α₁' := by
  apply hq₁.hom_ext
  · calc (α₀' ≫ xt') ≫ q₁ = α₀' ≫ (q₀ ≫ xt) := by rw [Category.assoc, hq_xt]
      _ = (q₀ ≫ α₀) ≫ xt := by rw [← Category.assoc, hq_a₀]
      _ = q₀ ≫ (xt ≫ α₁) := by rw [Category.assoc, ha_xt]
      _ = (xt' ≫ α₁') ≫ q₁ := by rw [Category.assoc, hq_a₁, ← Category.assoc xt' q₁, hq_xt, Category.assoc]
  · rw [Category.assoc, hw, ← Category.assoc, ha₀, Category.assoc, ha₁, hw]

end ChartAsm

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
    (ha'_over : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ xb' n = xb' n)

    (Y' : ℕ → Scheme.{0})
    (yb' : ∀ n : ℕ, Y' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
    (yt' : ∀ n : ℕ, Y' n ⟶ Y' (n + 1)) (p' : ∀ n : ℕ, X' n ⟶ Y' n) (r : ∀ n : ℕ, Y' n ⟶ D.Y n)
    (hbase : ∀ n : ℕ, IsPullback (r n) (yb' n) (D.yb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hsq : ∀ n : ℕ, IsPullback (q n) (p' n) (D.p n) (r n))
    (hyt'r : ∀ n : ℕ, yt' n ≫ r (n + 1) = r n ≫ D.yt n)
    (hyt'b : ∀ n : ℕ, yt' n ≫ yb' (n + 1) = yb' n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1)))))))
    (hp'_over : ∀ n : ℕ, p' n ≫ yb' n = xb' n)
    (hp'_inv : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ p' n = p' n)
    (hp'_xt : ∀ n : ℕ, xt' n ≫ p' (n + 1) = p' n ≫ yt' n)
    (V : ∀ n : ℕ, (D.Y n).Opens) (hVa : ∀ n : ℕ, IsAffineOpen (V n))
    (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n)
    (R : Type) [CommRing R] [Algebra 𝒪 R] [MulSemiringAction G R] [SMulCommClass G 𝒪 R]
    (hRc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (hRtf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0)
    (hRft : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}))
    (lvl : ∀ n : ℕ, (R ⧸ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) ≃+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)))
    (μ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 R G) ⧸
      Ideal.span {algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π ^ (n + 1)}) ≃+* Γ(D.Y n, V n))
    (hlvl_xt : ∀ (n : ℕ) (x : R), (xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((D.p n) ⁻¹ᵁ (V n))
        (by rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hV])
        (lvl (n + 1) (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ x))
    (hlvl_smul : ∀ (n : ℕ) (g : G) (x : R), (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n))
        (by rw [← Scheme.Hom.comp_preimage, D.p_inv]) (lvl n (Ideal.Quotient.mk _ x)) =
        lvl n (Ideal.Quotient.mk _ (g • x)))
    (hlvl_xb : ∀ (n : ℕ) (o : 𝒪), lvl n (Ideal.Quotient.mk _ (algebraMap 𝒪 R o)) =
        (xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)))
    (hμ_yt : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.yt n).appLE (V (n + 1)) (V n) (by rw [hV])
        (μ (n + 1) (Ideal.Quotient.mk _ x)) = μ n (Ideal.Quotient.mk _ x))
    (hμ_p : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.p n).appLE (V n) ((D.p n) ⁻¹ᵁ (V n)) le_rfl
        (μ n (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ (x : R)))
    (hμ_yb : ∀ (n : ℕ) (o : 𝒪), μ n (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o)) =
        (D.yb n).appLE ⊤ (V n) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)))
    (b : ↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) :
    ∃ (φ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) →+ Γ(Y' n, (r n) ⁻¹ᵁ (V n))),

      (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)) (s : S), φ n (x ⊗ₜ[𝒪] s) =
          (r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl (μ n (Ideal.Quotient.mk _ x)) *
          (yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top
            ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) ∧
      (∀ n : ℕ, Function.Surjective (φ n)) ∧

      ∃ (hV' : ∀ n : ℕ, (yt' n) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b)) = ((Y' n).basicOpen (φ n b))),

      ∃ (R' : Type) (_ : CommRing R') (_ : Algebra S R') (_ : MulSemiringAction G R') (_ : SMulCommClass G S R'),
        IsAdicComplete (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) R' ∧
        (∀ x : R', algebraMap S R' (algebraMap 𝒪 S π) * x = 0 → x = 0) ∧
        IsAdicComplete (Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) (algebraMap 𝒪 S π)}) ↥(FixedPoints.subalgebra S R' G) ∧
        ∃ (lvl' : ∀ n : ℕ, (R' ⧸ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)}) ≃+*
            Γ(X' n, (p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))))
          (μ' : ∀ n : ℕ, (↥(FixedPoints.subalgebra S R' G) ⧸ Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) (algebraMap 𝒪 S π) ^ (n + 1)}) ≃+*
            Γ(Y' n, ((Y' n).basicOpen (φ n b)))),
          (∀ (n : ℕ) (x : R'), (xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)))
              (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hV'])
              (lvl' (n + 1) (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ x)) ∧
          (∀ (n : ℕ) (g : G) (x : R'), (a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)))
              (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) (lvl' n (Ideal.Quotient.mk _ x)) =
              lvl' n (Ideal.Quotient.mk _ (g • x))) ∧
          (∀ (n : ℕ) (s : S), lvl' n (Ideal.Quotient.mk _ (algebraMap S R' s)) =
              (xb' n).appLE ⊤ ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_top
                ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) ∧
          (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra S R' G)), (yt' n).appLE ((Y' (n + 1)).basicOpen (φ (n + 1) b)) ((Y' n).basicOpen (φ n b)) (by rw [hV'])
              (μ' (n + 1) (Ideal.Quotient.mk _ x)) = μ' n (Ideal.Quotient.mk _ x)) ∧
          (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra S R' G)), (p' n).appLE ((Y' n).basicOpen (φ n b)) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_rfl
              (μ' n (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ (x : R'))) ∧
          (∀ (n : ℕ) (s : S), μ' n (Ideal.Quotient.mk _ (algebraMap S ↥(FixedPoints.subalgebra S R' G) s)) =
              (yb' n).appLE ⊤ ((Y' n).basicOpen (φ n b)) le_top
                ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) := by

  obtain ⟨φ, hφ, hφs, hV'all⟩ := AlgebraicGeometry.exists_addMonoidHom_tmul_sections_preimage_of_isPullback 𝒪 π D.Y D.yb D.yt S Y' yb' yt' r
    hbase hyt'r hyt'b V hVa hV ↥(FixedPoints.subalgebra 𝒪 R G) μ hμ_yt hμ_yb
  have hV' : ∀ n : ℕ, (yt' n) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b)) = (Y' n).basicOpen (φ n b) := hV'all b

  have hϖ : ∀ s : S, algebraMap 𝒪 S π * s = 0 → s = 0 := ChartAsm.smul_injective_of_flat 𝒪 π hπ.ne_zero S
  have hflat' : ∀ n : ℕ, Flat (xb' n) := fun n => MorphismProperty.of_isPullback (hq n) (hflat n)
  have ha'_xt : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ xt' n = xt' n ≫ (a' (n + 1) g).hom := fun n g =>
    ChartAsm.comm_of_isPullback (hq (n + 1)) (hq_xt n) (hq_a n g) (hq_a (n + 1) g) (ha_xt n g) (hcart' n).w (ha'_over n g)
      (ha'_over (n + 1) g)
  have hrVa : ∀ n : ℕ, IsAffineOpen ((r n) ⁻¹ᵁ (V n)) := fun n => by
    haveI : IsAffineHom (r n) := MorphismProperty.of_isPullback (hbase n).flip inferInstance
    exact (hVa n).preimage (r n)
  haveI hp'aff : ∀ n : ℕ, IsAffineHom (p' n) := fun n => by
    haveI := D.p_isFinite n
    exact MorphismProperty.of_isPullback (hsq n) (inferInstance : IsAffineHom (D.p n))
  have hW'a : ∀ n : ℕ, IsAffineOpen ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) := fun n =>
    ((hrVa n).basicOpen (φ n b)).preimage (p' n)
  have hW'c : ∀ n : ℕ, (xt' n) ⁻¹ᵁ ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) =
      (p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)) := fun n => by
    rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hV']
  have hW's : ∀ (n : ℕ) (g : G), (a' n g).hom ⁻¹ᵁ ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) =
      (p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)) := fun n g => by
    rw [← Scheme.Hom.comp_preimage, hp'_inv]

  obtain ⟨R', i1, i2, i3, i4, hR'c, hR'tf, lvl', h1, h2, h3⟩ :=
    AlgebraicGeometry.exists_ringEquiv_quotient_sections_of_isPullback_of_flat S (algebraMap 𝒪 S π) hϖ X' xb' xt' hcart' hflat'
      G a' ha'_over ha'_xt (fun n => (p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) hW'a hW'c hW's

  obtain ⟨hAc, μ', l1, l2, l3⟩ :=
    AlgebraicGeometry.TowerQuotientDatum.isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_basicOpen 𝒪 hdvr π hπ hcomplete X xb xt
      hcart hproper hflat haff G a ha_over ha_xt D S X' xb' xt' a' q hq hcart' hq_xt hq_a ha'_over Y' yb' yt' p' r hbase hsq hyt'r hyt'b
      hp'_over hp'_inv hp'_xt V hVa hV R hRc hRtf hRft lvl μ hlvl_xt hlvl_smul hlvl_xb hμ_yt hμ_p hμ_yb b φ hφ hφs hV' R' hR'c hR'tf
      lvl' h1 h2 h3
  exact ⟨φ, hφ, hφs, hV', R', i1, i2, i3, i4, hR'c, hR'tf, hAc, lvl', μ', h1, h2, h3, l1, l2, l3⟩

end S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_fixedPoints_quotient_basicOpen_of_isPullback_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_fixedPoints_quotient_basicOpen_of_isPullback_of_flat (solution)
