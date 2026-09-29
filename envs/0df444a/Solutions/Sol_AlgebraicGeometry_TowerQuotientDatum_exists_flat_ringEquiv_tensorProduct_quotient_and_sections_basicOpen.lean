-- Prove2me | solution 1 for AlgebraicGeometry.TowerQuotientDatum.exists_flat_ringEquiv_tensorProduct_quotient_and_sections_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e622d013-5bb4-5e31-8444-26a87c8a85a0

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_quotient_sections_preimage_and_basicOpen
import Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_tensorProduct_quotient_of_ringEquiv_sections_basicOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_flat_ringEquiv_tensorProduct_quotient_and_sections_basicOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
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
    (b : ↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)

    (φ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) →+ Γ(Y' n, (r n) ⁻¹ᵁ (V n)))
    (hφ : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)) (s : S), φ n (x ⊗ₜ[𝒪] s) =
        (r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl (μ n (Ideal.Quotient.mk _ x)) *
        (yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))
    (hφs : ∀ n : ℕ, Function.Surjective (φ n))
    (hV' : ∀ n : ℕ, (yt' n) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b)) = (Y' n).basicOpen (φ n b))

    (R' : Type) [CommRing R'] [Algebra S R'] [MulSemiringAction G R'] [SMulCommClass G S R']
    (hR'c : IsAdicComplete (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) R')
    (hR'tf : ∀ x : R', algebraMap S R' (algebraMap 𝒪 S π) * x = 0 → x = 0)
    (lvl' : ∀ n : ℕ, (R' ⧸ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)}) ≃+*
      Γ(X' n, (p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))))
    (hlvl'_xt : ∀ (n : ℕ) (x : R'), (xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)))
        (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hV'])
        (lvl' (n + 1) (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ x))
    (hlvl'_smul : ∀ (n : ℕ) (g : G) (x : R'), (a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)))
        (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) (lvl' n (Ideal.Quotient.mk _ x)) =
        lvl' n (Ideal.Quotient.mk _ (g • x)))
    (hlvl'_xb : ∀ (n : ℕ) (s : S), lvl' n (Ideal.Quotient.mk _ (algebraMap S R' s)) =
        (xb' n).appLE ⊤ ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) :
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A') (_ : Module.Flat ↥(FixedPoints.subalgebra 𝒪 R G) A')
      (σ : S →+* A')
      (τ : ∀ n : ℕ, ((R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') ⧸
          Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) ≃+*
        (R' ⧸ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)}))
      (θ : ∀ n : ℕ, (A' ⧸ Ideal.span {σ (algebraMap 𝒪 S π) ^ (n + 1)}) ≃+* Γ(Y' n, ((Y' n).basicOpen (φ n b)))),

      (∀ o : 𝒪, σ (algebraMap 𝒪 S o) = algebraMap ↥(FixedPoints.subalgebra 𝒪 R G) A' (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o)) ∧

      (∀ (n : ℕ) (z : R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') (y : R'),
        τ (n + 1) (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y → τ n (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y) ∧
      (∀ (n : ℕ) (g : G) (x : R) (w : A') (y : R'),
        τ n (Ideal.Quotient.mk _ (x ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ y →
        τ n (Ideal.Quotient.mk _ ((g • x) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ (g • y)) ∧
      (∀ (n : ℕ) (s : S),
        τ n (Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] σ s)) = Ideal.Quotient.mk _ (algebraMap S R' s)) ∧

      (∀ (n : ℕ) (w : A'), (yt' n).appLE ((Y' (n + 1)).basicOpen (φ (n + 1) b)) ((Y' n).basicOpen (φ n b)) (by rw [hV'])
          (θ (n + 1) (Ideal.Quotient.mk _ w)) = θ n (Ideal.Quotient.mk _ w)) ∧
      (∀ (n : ℕ) (s : S), θ n (Ideal.Quotient.mk _ (σ s)) =
          (yb' n).appLE ⊤ ((Y' n).basicOpen (φ n b)) le_top
            ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) ∧
      (∀ (n : ℕ) (w : A') (y : R'), τ n (Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ y →
          (p' n).appLE ((Y' n).basicOpen (φ n b)) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_rfl (θ n (Ideal.Quotient.mk _ w)) = lvl' n (Ideal.Quotient.mk _ y)) := by
  classical
  have hY := AlgebraicGeometry.TowerQuotientDatum.exists_ringEquiv_quotient_sections_preimage_and_basicOpen 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat haff G a ha_over ha_xt D S X' xb' xt' a' q hq hcart' hq_xt hq_a ha'_over Y' yb' yt' p' r hbase hsq hyt'r hyt'b hp'_over hp'_inv hp'_xt V hVa hV R hRc hRtf hRft lvl μ hlvl_xt hlvl_smul hlvl_xb hμ_yt hμ_p hμ_yb b φ hφ hφs hV' R' hR'c hR'tf lvl' hlvl'_xt hlvl'_smul hlvl'_xb
  obtain ⟨β, θ, hβ, hθyt, hθyb, hθE⟩ := hY
  have hX := AlgebraicGeometry.TowerQuotientDatum.exists_ringEquiv_tensorProduct_quotient_of_ringEquiv_sections_basicOpen 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat haff G a ha_over ha_xt D S X' xb' xt' a' q hq hcart' hq_xt hq_a ha'_over Y' yb' yt' p' r hbase hsq hyt'r hyt'b hp'_over hp'_inv hp'_xt V hVa hV R hRc hRtf hRft lvl μ hlvl_xt hlvl_smul hlvl_xb hμ_yt hμ_p hμ_yb b φ hφ hφs hV' R' hR'c hR'tf lvl' hlvl'_xt hlvl'_smul hlvl'_xb
    (Localization.Away b) β hβ θ hθE
  obtain ⟨τ, hτs, hτg, hτσ, hθp⟩ := hX
  haveI hflat : Module.Flat ↥(FixedPoints.subalgebra 𝒪 R G) (Localization.Away b) := Module.Flat.trans ↥(FixedPoints.subalgebra 𝒪 R G) (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b)
  refine ⟨Localization.Away b, inferInstance, inferInstance, hflat,
    (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b)).comp (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom,
    τ, θ, ?_, hτs, hτg, hτσ, hθyt, hθyb, hθp⟩
  intro o
  show algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b) ((1 : ↥(FixedPoints.subalgebra 𝒪 R G)) ⊗ₜ[𝒪] algebraMap 𝒪 S o) =
    algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b) (algebraMap ↥(FixedPoints.subalgebra 𝒪 R G) (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o))
  congr 1
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]

end S_AlgebraicGeometry_TowerQuotientDatum_exists_flat_ringEquiv_tensorProduct_quotient_and_sections_basicOpen
end P2MW
export P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_flat_ringEquiv_tensorProduct_quotient_and_sections_basicOpen (solution)
