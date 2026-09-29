-- Prove2me | solution 1 for AlgebraicGeometry.TowerQuotientDatum.isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6ff9af72-bd2c-58da-972b-1e12cd2e99c1

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Theorems.Thm_AlgebraicGeometry_AdmissibleAlgebra_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_of_ringEquiv_tensorProduct_quotient
import Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_exists_flat_ringEquiv_tensorProduct_quotient_and_sections_basicOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_basicOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

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
    IsAdicComplete (Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) (algebraMap 𝒪 S π)}) ↥(FixedPoints.subalgebra S R' G) ∧
    ∃ (μ' : ∀ n : ℕ, (↥(FixedPoints.subalgebra S R' G) ⧸ Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) (algebraMap 𝒪 S π) ^ (n + 1)}) ≃+*
        Γ(Y' n, ((Y' n).basicOpen (φ n b)))),
      (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra S R' G)), (yt' n).appLE ((Y' (n + 1)).basicOpen (φ (n + 1) b)) ((Y' n).basicOpen (φ n b)) (by rw [hV'])
          (μ' (n + 1) (Ideal.Quotient.mk _ x)) = μ' n (Ideal.Quotient.mk _ x)) ∧
      (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra S R' G)), (p' n).appLE ((Y' n).basicOpen (φ n b)) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_rfl
          (μ' n (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ (x : R'))) ∧
      (∀ (n : ℕ) (s : S), μ' n (Ideal.Quotient.mk _ (algebraMap S ↥(FixedPoints.subalgebra S R' G) s)) =
          (yb' n).appLE ⊤ ((Y' n).basicOpen (φ n b)) le_top
            ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) := by

  have hgeo := AlgebraicGeometry.TowerQuotientDatum.exists_flat_ringEquiv_tensorProduct_quotient_and_sections_basicOpen
    𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat haff G a ha_over ha_xt D S X' xb' xt' a' q hq hcart' hq_xt hq_a ha'_over
    Y' yb' yt' p' r hbase hsq hyt'r hyt'b hp'_over hp'_inv hp'_xt V hVa hV R hRc hRtf hRft lvl μ hlvl_xt hlvl_smul hlvl_xb
    hμ_yt hμ_p hμ_yb b φ hφ hφs hV' R' hR'c hR'tf lvl' hlvl'_xt hlvl'_smul hlvl'_xb
  obtain ⟨A', instCR, instAlg, instFlat, σ, τ, θ, hσ, hτ_succ, hτ_smul, hτ_σ, hθ_yt, hθ_yb, hθ_p⟩ := hgeo

  have halg := AlgebraicGeometry.AdmissibleAlgebra.isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_of_ringEquiv_tensorProduct_quotient
    𝒪 hdvr π hπ hcomplete R hRc hRtf hRft G S A' σ hσ R' hR'c hR'tf τ hτ_succ hτ_smul hτ_σ
  obtain ⟨hcompl, α, hα_succ, hα_τ, hα_σ⟩ := halg
  refine ⟨hcompl, fun n => (α n).symm.trans (θ n), ?_, ?_, ?_⟩
  · intro n x
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective ((α (n + 1)).symm (Ideal.Quotient.mk _ x))
    have h1 : α (n + 1) (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ x := by
      rw [hw, RingEquiv.apply_symm_apply]
    have h0 : (α n).symm (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ w := by
      rw [← hα_succ n w x h1, RingEquiv.symm_apply_apply]
    show (yt' n).appLE _ _ _ (θ (n + 1) ((α (n + 1)).symm (Ideal.Quotient.mk _ x))) = θ n ((α n).symm (Ideal.Quotient.mk _ x))
    rw [← hw, h0]
    exact hθ_yt n w
  · intro n x
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective ((α n).symm (Ideal.Quotient.mk _ x))
    have h1 : α n (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ x := by
      rw [hw, RingEquiv.apply_symm_apply]
    show (p' n).appLE _ _ _ (θ n ((α n).symm (Ideal.Quotient.mk _ x))) = lvl' n (Ideal.Quotient.mk _ (x : R'))
    rw [← hw]
    exact hθ_p n w x (hα_τ n w x h1)
  · intro n s
    show θ n ((α n).symm (Ideal.Quotient.mk _ (algebraMap S _ s))) = _
    rw [← hα_σ n s, RingEquiv.symm_apply_apply]
    exact hθ_yb n s

end S_AlgebraicGeometry_TowerQuotientDatum_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_basicOpen
end P2MW
export P2MW.S_AlgebraicGeometry_TowerQuotientDatum_isAdicComplete_fixedPoints_and_exists_ringEquiv_quotient_basicOpen (solution)
