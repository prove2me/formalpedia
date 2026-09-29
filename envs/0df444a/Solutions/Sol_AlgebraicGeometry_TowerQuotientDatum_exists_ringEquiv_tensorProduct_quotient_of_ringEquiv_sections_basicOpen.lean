-- Prove2me | solution 1 for AlgebraicGeometry.TowerQuotientDatum.exists_ringEquiv_tensorProduct_quotient_of_ringEquiv_sections_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e0ad0632-8e2e-52f0-b7e7-3c1af454ef5a

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_tensorProduct_quotient_of_ringEquiv_sections_basicOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

universe u

namespace C3GeoX

theorem appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) : f.appLE ⊤ ⊤ le_top = f.appTop :=
  Scheme.Hom.appLE_eq_app _

theorem appLE_appLE_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = ((f ≫ g).appLE U W e₃).hom x := by
  have := congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂)
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using this

theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (x : R) :
    (Spec.map φ).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x) = (Scheme.ΓSpecIso S).inv.hom (φ.hom x) := by
  have := congrArg (fun ψ => ψ.hom x) (Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  exact this.symm

theorem ΓSpecIso_hom_inv_apply (R : CommRingCat.{u}) (x : R) :
    (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom x) = x := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_apply]

theorem map_appLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V V' : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V)
    (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom x) = (f.appLE U V' (h.trans e)).hom x := by
  have := congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_map f e (homOfLE h).op)
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using this

theorem appLE_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (U U' : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (h : U ≤ U')
    (e' : V ≤ f ⁻¹ᵁ U') (x : Γ(Y, U')) :
    (f.appLE U V e).hom ((Y.presheaf.map (homOfLE h).op).hom x) = (f.appLE U' V e').hom x := by
  have := congrArg (fun φ => φ.hom x) (Scheme.Hom.map_appLE f e (homOfLE h).op)
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using this

theorem app_apply_eq_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x : Γ(Y, U)) :
    (f.app U).hom x = (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom x := by
  rw [Scheme.Hom.app_eq_appLE]

set_option maxHeartbeats 6400000 in

theorem P2
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
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))

    (A' : Type) [CommRing A'] [Algebra (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A'] [IsLocalization.Away b A']
    [Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A'] [IsScalarTower ↥(FixedPoints.subalgebra 𝒪 R G) (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A']

    (β : ∀ n : ℕ, ((↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) ⧸ (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})) ≃+* Γ(Y' n, (r n) ⁻¹ᵁ (V n)))
    (hβ : ∀ (n : ℕ) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)), β n (Ideal.Quotient.mk _ z) = φ n z)
    (θ : ∀ n : ℕ, (A' ⧸ (Ideal.span {((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A').comp (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) (algebraMap 𝒪 S π) ^ (n + 1)})) ≃+* Γ(Y' n, ((Y' n).basicOpen (φ n b))))
    (hθ : ∀ (n : ℕ) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)), θ n (Ideal.Quotient.mk _ (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A' z)) = ((Y' n).presheaf.map (homOfLE ((Y' n).basicOpen_le (φ n b))).op) (φ n z)) (n : ℕ) :
    @IsLocalization.Away (Γ(X' n, ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))) _ ((((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) b) (Γ(X' n, ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))))) _ (((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom).toAlgebra := by

  haveI : IsAffineHom (q n) := MorphismProperty.of_isPullback (P := @IsAffineHom) (hq n).flip inferInstance
  haveI : IsAffineHom (D.p n) := by have := D.p_isFinite n; infer_instance
  have hpV : IsAffineOpen ((D.p n) ⁻¹ᵁ (V n)) := (hVa n).preimage (D.p n)
  have hWeq : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) = (q n) ⁻¹ᵁ ((D.p n) ⁻¹ᵁ (V n)) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]
  have hWa : IsAffineOpen ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) := by rw [hWeq]; exact hpV.preimage (q n)

  have hu₂b : (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) b = ((p' n).app ((r n) ⁻¹ᵁ (V n))).hom (φ n b) := by
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hβ]
  have hW' : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) = (X' n).basicOpen ((((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) b) := by
    rw [hu₂b]
    exact Scheme.preimage_basicOpen (p' n) (φ n b)
  exact hWa.isLocalization_of_eq_basicOpen _ (homOfLE _) hW'

set_option maxHeartbeats 12800000 in

theorem laws
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
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))

    (A' : Type) [CommRing A'] [Algebra (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A'] [IsLocalization.Away b A']
    [Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A'] [IsScalarTower ↥(FixedPoints.subalgebra 𝒪 R G) (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A']

    (β : ∀ n : ℕ, ((↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) ⧸ (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})) ≃+* Γ(Y' n, (r n) ⁻¹ᵁ (V n)))
    (hβ : ∀ (n : ℕ) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)), β n (Ideal.Quotient.mk _ z) = φ n z)
    (θ : ∀ n : ℕ, (A' ⧸ (Ideal.span {((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A').comp (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) (algebraMap 𝒪 S π) ^ (n + 1)})) ≃+* Γ(Y' n, ((Y' n).basicOpen (φ n b))))
    (hθ : ∀ (n : ℕ) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)), θ n (Ideal.Quotient.mk _ (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A' z)) = ((Y' n).presheaf.map (homOfLE ((Y' n).basicOpen_le (φ n b))).op) (φ n z)) (n : ℕ) :
    (∀ (hle : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (xt' n) ⁻¹ᵁ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1))))) (x : R),
        ((xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) hle).hom ((((q (n + 1)).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq (n + 1)).w]))).hom.comp ((lvl (n + 1)).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ ((n + 1) + 1)})))) x) = (((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) x) ∧
    (∀ (hle : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (xt' n) ⁻¹ᵁ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1))))) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)),
        ((xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) hle).hom ((((p' (n + 1)).app ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))).hom.comp ((β (n + 1)).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ ((n + 1) + 1)})))) z) = (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) z) ∧
    (∀ (g : G) (hle : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (a' n g⁻¹).hom ⁻¹ᵁ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n)))) (x : R),
        ((a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) hle).hom ((((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) x) = (((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) (g • x)) ∧
    (∀ (g : G) (hle : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (a' n g⁻¹).hom ⁻¹ᵁ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n)))) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)),
        ((a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) hle).hom ((((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) z) = (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) z) ∧
    (∀ s : S, (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) ((1 : ↥(FixedPoints.subalgebra 𝒪 R G)) ⊗ₜ[𝒪] s) =
        ((xb' n).appLE ⊤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) ∧
    (∀ a : ↥(FixedPoints.subalgebra 𝒪 R G), (((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) (a : R) = (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) (a ⊗ₜ[𝒪] (1 : S))) ∧
    (∀ z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S), ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom ((((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) z) =
        ((p' n).app ((Y' n).basicOpen (φ n b))).hom (θ n (Ideal.Quotient.mk _ (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A' z)))) ∧
    (∀ (hle : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (xt' n) ⁻¹ᵁ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1))))) (hle' : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ (xt' n) ⁻¹ᵁ ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))))
        (t : Γ(X' (n + 1), ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))))),
        ((xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) hle').hom (((X' (n + 1)).presheaf.map (homOfLE ((fun x hx => (Y' (n + 1)).basicOpen_le (φ (n + 1) b) hx) : ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ≤ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))))).op).hom t) = ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom (((xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) hle).hom t)) ∧
    (∀ (g : G) (hle : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (a' n g⁻¹).hom ⁻¹ᵁ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n)))) (hle' : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ (a' n g⁻¹).hom ⁻¹ᵁ ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))))
        (t : Γ(X' n, ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))),
        ((a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) hle').hom (((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom t) = ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom (((a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) hle).hom t)) ∧
    (∀ t : Γ(Spec (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)})), ⊤),
        ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom (((xb' n).appLE ⊤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) le_top).hom t) = ((xb' n).appLE ⊤ ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_top).hom t) := by
  classical

  have hWq : ∀ m : ℕ, ((p' m) ⁻¹ᵁ ((r m) ⁻¹ᵁ (V m))) = (q m) ⁻¹ᵁ ((D.p m) ⁻¹ᵁ (V m)) := fun m => by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq m).w]
  have hpVxt : ((D.p n) ⁻¹ᵁ (V n)) ≤ (xt n) ⁻¹ᵁ ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) :=
    le_of_eq (by rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hV])
  have hrVyt : ((r n) ⁻¹ᵁ (V n)) ≤ (yt' n) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1))) :=
    le_of_eq (by rw [← Scheme.Hom.comp_preimage, hyt'r, Scheme.Hom.comp_preimage, hV])
  have hpVa : ∀ g : G, ((D.p n) ⁻¹ᵁ (V n)) ≤ (a n g⁻¹).hom ⁻¹ᵁ ((D.p n) ⁻¹ᵁ (V n)) := fun g =>
    le_of_eq (by rw [← Scheme.Hom.comp_preimage, D.p_inv])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hle x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [appLE_appLE_apply (xt' n) (q (n + 1)) _ _ _ _ hle (by rw [hq_xt, Scheme.Hom.comp_preimage]; exact (hWq n).le.trans ((q n).preimage_mono hpVxt)),
      appLE_congr_hom (hq_xt n) _ _ _ (by rw [Scheme.Hom.comp_preimage]; exact (hWq n).le.trans ((q n).preimage_mono hpVxt)),
      ← appLE_appLE_apply (q n) (xt n) _ ((D.p n) ⁻¹ᵁ (V n)) _ hpVxt (hWq n).le, hlvl_xt]
  ·
    intro hle z
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hβ]
    (try simp only [app_apply_eq_appLE])
    rw [appLE_appLE_apply (xt' n) (p' (n + 1)) _ _ _ _ hle (by rw [hp'_xt, Scheme.Hom.comp_preimage]; exact (p' n).preimage_mono hrVyt),
      appLE_congr_hom (hp'_xt n) _ _ _ (by rw [Scheme.Hom.comp_preimage]; exact (p' n).preimage_mono hrVyt),
      ← appLE_appLE_apply (p' n) (yt' n) _ ((r n) ⁻¹ᵁ (V n)) _ hrVyt le_rfl]
    congr 1

    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x s =>
      rw [hφ, hφ, map_mul]
      congr 1
      · rw [appLE_appLE_apply (yt' n) (r (n + 1)) _ _ _ _ hrVyt (by rw [hyt'r, Scheme.Hom.comp_preimage]; exact (r n).preimage_mono (le_of_eq (hV n).symm)),
          appLE_congr_hom (hyt'r n) _ _ _ (by rw [Scheme.Hom.comp_preimage]; exact (r n).preimage_mono (le_of_eq (hV n).symm)),
          ← appLE_appLE_apply (r n) (D.yt n) _ (V n) _ (le_of_eq (hV n).symm) le_rfl, hμ_yt]
      · rw [appLE_appLE_apply (yt' n) (yb' (n + 1)) _ _ _ _ hrVyt le_top, appLE_congr_hom (hyt'b n) _ _ _ le_top,
          ← appLE_appLE_apply (yb' n) (Spec.map _) ⊤ ⊤ _ le_top le_top, appLE_top_top]
        congr 1
        change (Spec.map _).appTop.hom ((Scheme.ΓSpecIso _).inv.hom _) = (Scheme.ΓSpecIso _).inv.hom _
        rw [appTop_ΓSpecIso_inv]
        rfl
  ·
    intro g hle x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [appLE_appLE_apply (a' n g⁻¹).hom (q n) _ _ _ _ hle (by rw [hq_a, Scheme.Hom.comp_preimage]; exact (hWq n).le.trans ((q n).preimage_mono (hpVa g))),
      appLE_congr_hom (hq_a n g⁻¹) _ _ _ (by rw [Scheme.Hom.comp_preimage]; exact (hWq n).le.trans ((q n).preimage_mono (hpVa g))),
      ← appLE_appLE_apply (q n) (a n g⁻¹).hom _ ((D.p n) ⁻¹ᵁ (V n)) _ (hpVa g) (hWq n).le, hlvl_smul]
  ·
    intro g hle z
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    (try simp only [app_apply_eq_appLE])
    rw [appLE_appLE_apply (a' n g⁻¹).hom (p' n) _ _ _ _ hle (by rw [hp'_inv]), appLE_congr_hom (hp'_inv n g⁻¹)]
  ·
    intro s
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hβ, hφ]
    rw [show (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π ^ (n + 1)})) (1 : ↥(FixedPoints.subalgebra 𝒪 R G)) = 1 from map_one _, map_one, map_one,
      one_mul]
    (try simp only [app_apply_eq_appLE])
    rw [appLE_appLE_apply (p' n) (yb' n) ⊤ _ _ le_top le_rfl le_top, appLE_congr_hom (hp'_over n)]
  ·
    intro a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hβ, hφ]
    rw [map_one, map_one, map_one, mul_one, ← hμ_p, appLE_appLE_apply (q n) (D.p n) (V n) _ _ le_rfl (hWq n).le
        (by rw [(hsq n).w, Scheme.Hom.comp_preimage]),
      appLE_congr_hom ((hsq n).w) _ _ _ (by rw [Scheme.Hom.comp_preimage])]
    (try simp only [app_apply_eq_appLE])
    rw [← appLE_appLE_apply (p' n) (r n) (V n) ((r n) ⁻¹ᵁ (V n)) _ le_rfl le_rfl]
  ·
    intro z
    rw [hθ n z]
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hβ]
    (try simp only [app_apply_eq_appLE])
    rw [map_appLE_apply,
      appLE_map_apply (p' n) ((Y' n).basicOpen (φ n b)) ((r n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_rfl ((Y' n).basicOpen_le (φ n b))
        (fun x hx => (Y' n).basicOpen_le (φ n b) hx)]
  ·
    intro hle hle' t
    rw [map_appLE_apply, appLE_map_apply]
  ·
    intro g hle hle' t
    rw [map_appLE_apply, appLE_map_apply]
  ·
    intro t
    rw [map_appLE_apply]

end C3GeoX

namespace GEOX
p2m_open "AlgebraicGeometry.Scheme TensorProduct"

theorem isAffineOpen_preimage_of_isPullback
    {Y Y' : Scheme.{u}} {B C : CommRingCat.{u}} (yb : Y ⟶ Spec B) (yb' : Y' ⟶ Spec C) (r : Y' ⟶ Y) (f : B ⟶ C)
    (hbase : IsPullback r yb' yb (Spec.map f)) (V : Y.Opens) (hVa : IsAffineOpen V) : IsAffineOpen (r ⁻¹ᵁ V) := by
  have hUY : r ⁻¹ᵁ V = r ⁻¹ᵁ V ⊓ yb' ⁻¹ᵁ ⊤ := by simp
  have hT : IsAffineOpen (⊤ : (Spec C).Opens) := isAffineOpen_top _
  have hS : IsAffineOpen (⊤ : (Spec B).Opens) := isAffineOpen_top _
  have : IsAffine _ := hS
  have : IsAffine _ := hT
  have : IsAffine _ := hVa
  exact .of_isIso (Scheme.Hom.isPullback_resLE hbase (US := ⊤) (UT := ⊤) (UX := V) le_top le_top hUY).isoPullback.hom

set_option maxHeartbeats 3200000 in

theorem P1_core
    {A R P : Type} [CommRing R] [CommRing P] (iR : A → R) (iP : A → P)
    (X X' Y Y' : Scheme.{0}) (q : X' ⟶ X) (p' : X' ⟶ Y') (p : X ⟶ Y) (r : Y' ⟶ Y) (hsq : IsPullback q p' p r)
    (V : Y.Opens) (hVa : IsAffineOpen V) (hpV : IsAffineOpen (p ⁻¹ᵁ V)) (hrV : IsAffineOpen (r ⁻¹ᵁ V))
    (e : p' ⁻¹ᵁ (r ⁻¹ᵁ V) ≤ q ⁻¹ᵁ (p ⁻¹ᵁ V))
    (t : R) (tP : P) (lvl : (R ⧸ Ideal.span {t}) ≃+* Γ(X, p ⁻¹ᵁ V)) (β : (P ⧸ Ideal.span {tP}) ≃+* Γ(Y', r ⁻¹ᵁ V))
    (μmk : A → Γ(Y, V)) (hμs : Function.Surjective μmk)
    (hμ_p : ∀ a, p.appLE V (p ⁻¹ᵁ V) le_rfl (μmk a) = lvl (Ideal.Quotient.mk _ (iR a)))
    (hμ_r : ∀ a, r.appLE V (r ⁻¹ᵁ V) le_rfl (μmk a) = β (Ideal.Quotient.mk _ (iP a)))
    (a₀ : A) (ht : iR a₀ = t) (htP : iP a₀ = tP)
    (T : Type) [CommRing T] (f : R →+* T) (g : P →+* T) (hft : f t = 0) (hfg : ∀ a, f (iR a) = g (iP a)) :
    ∃! h : Γ(X', p' ⁻¹ᵁ (r ⁻¹ᵁ V)) →+* T,
      h.comp ((q.appLE (p ⁻¹ᵁ V) (p' ⁻¹ᵁ (r ⁻¹ᵁ V)) e).hom.comp (lvl.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {t})))) = f ∧
      h.comp ((p'.app (r ⁻¹ᵁ V)).hom.comp (β.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {tP})))) = g := by
  have hUY : p' ⁻¹ᵁ (r ⁻¹ᵁ V) = q ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (r ⁻¹ᵁ V) := (inf_eq_right.mpr e).symm
  have key := (isIso_pushoutSection_iff hsq le_rfl le_rfl hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hsq le_rfl le_rfl hUY hVa hrV hpV)
  have happ : ∀ y, (p'.app (r ⁻¹ᵁ V)).hom y = (p'.appLE (r ⁻¹ᵁ V) (p' ⁻¹ᵁ (r ⁻¹ᵁ V)) le_rfl).hom y := fun y => by
    rw [Scheme.Hom.appLE_eq_app]

  have hfI : ∀ z ∈ Ideal.span {t}, f z = 0 := by
    intro z hz; rw [Ideal.mem_span_singleton] at hz; obtain ⟨c, rfl⟩ := hz; rw [map_mul, hft, zero_mul]
  have hgI : ∀ z ∈ Ideal.span {tP}, g z = 0 := by
    intro z hz; rw [Ideal.mem_span_singleton] at hz; obtain ⟨c, rfl⟩ := hz
    rw [map_mul, ← htP, ← hfg, ht, hft, zero_mul]
  let fb : Γ(X, p ⁻¹ᵁ V) →+* T := (Ideal.Quotient.lift _ f hfI).comp lvl.symm.toRingHom
  let gb : Γ(Y', r ⁻¹ᵁ V) →+* T := (Ideal.Quotient.lift _ g hgI).comp β.symm.toRingHom
  have hfb : ∀ x, fb (lvl (Ideal.Quotient.mk _ x)) = f x := by
    intro x; show Ideal.Quotient.lift _ f hfI (lvl.symm (lvl _)) = _; rw [RingEquiv.symm_apply_apply]; rfl
  have hgb : ∀ z, gb (β (Ideal.Quotient.mk _ z)) = g z := by
    intro z; show Ideal.Quotient.lift _ g hgI (β.symm (β _)) = _; rw [RingEquiv.symm_apply_apply]; rfl
  have hw : p.appLE V (p ⁻¹ᵁ V) le_rfl ≫ CommRingCat.ofHom fb = r.appLE V (r ⁻¹ᵁ V) le_rfl ≫ CommRingCat.ofHom gb := by
    apply CommRingCat.hom_ext; apply RingHom.ext; intro y
    obtain ⟨a, rfl⟩ := hμs y
    show fb ((p.appLE V (p ⁻¹ᵁ V) le_rfl).hom (μmk a)) = gb ((r.appLE V (r ⁻¹ᵁ V) le_rfl).hom (μmk a))
    change fb (p.appLE V (p ⁻¹ᵁ V) le_rfl (μmk a)) = gb (r.appLE V (r ⁻¹ᵁ V) le_rfl (μmk a))
    rw [hμ_p, hμ_r, hfb, hgb, hfg]
  have hinl : ∀ y, (key.desc _ _ hw).hom ((q.appLE (p ⁻¹ᵁ V) (p' ⁻¹ᵁ (r ⁻¹ᵁ V)) e).hom y) = fb y := by
    intro y
    have := congrArg (fun φ => φ.hom y) (key.inl_desc _ _ hw)
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] using this
  have hinr : ∀ y, (key.desc _ _ hw).hom ((p'.appLE (r ⁻¹ᵁ V) (p' ⁻¹ᵁ (r ⁻¹ᵁ V)) le_rfl).hom y) = gb y := by
    intro y
    have := congrArg (fun φ => φ.hom y) (key.inr_desc _ _ hw)
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] using this
  refine ⟨(key.desc _ _ hw).hom, ⟨?_, ?_⟩, ?_⟩
  · apply RingHom.ext; intro x
    show (key.desc _ _ hw).hom ((q.appLE (p ⁻¹ᵁ V) (p' ⁻¹ᵁ (r ⁻¹ᵁ V)) e).hom (lvl (Ideal.Quotient.mk _ x))) = f x
    rw [hinl, hfb]
  · apply RingHom.ext; intro z
    show (key.desc _ _ hw).hom ((p'.app (r ⁻¹ᵁ V)).hom (β (Ideal.Quotient.mk _ z))) = g z
    rw [happ, hinr, hgb]
  · rintro h' ⟨h1, h2⟩
    have H : CommRingCat.ofHom h' = CommRingCat.ofHom (key.desc _ _ hw).hom := by
      apply key.hom_ext
      · apply CommRingCat.hom_ext; apply RingHom.ext; intro y
        obtain ⟨x', rfl⟩ := lvl.surjective y
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x'
        show h' ((q.appLE (p ⁻¹ᵁ V) (p' ⁻¹ᵁ (r ⁻¹ᵁ V)) e).hom (lvl (Ideal.Quotient.mk _ x))) =
          (key.desc _ _ hw).hom ((q.appLE (p ⁻¹ᵁ V) (p' ⁻¹ᵁ (r ⁻¹ᵁ V)) e).hom (lvl (Ideal.Quotient.mk _ x)))
        rw [hinl, hfb]
        exact RingHom.congr_fun h1 x
      · apply CommRingCat.hom_ext; apply RingHom.ext; intro y
        obtain ⟨z', rfl⟩ := β.surjective y
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z'
        show h' ((p'.appLE (r ⁻¹ᵁ V) (p' ⁻¹ᵁ (r ⁻¹ᵁ V)) le_rfl).hom (β (Ideal.Quotient.mk _ z))) =
          (key.desc _ _ hw).hom ((p'.appLE (r ⁻¹ᵁ V) (p' ⁻¹ᵁ (r ⁻¹ᵁ V)) le_rfl).hom (β (Ideal.Quotient.mk _ z)))
        rw [hinr, hgb, ← happ]
        exact RingHom.congr_fun h2 z
    exact congrArg CommRingCat.Hom.hom H

end GEOX

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem C3GeoX.P1
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
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))

    (A' : Type) [CommRing A'] [Algebra (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A'] [IsLocalization.Away b A']
    [Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A'] [IsScalarTower ↥(FixedPoints.subalgebra 𝒪 R G) (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A']

    (β : ∀ n : ℕ, ((↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) ⧸ (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})) ≃+* Γ(Y' n, (r n) ⁻¹ᵁ (V n)))
    (hβ : ∀ (n : ℕ) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)), β n (Ideal.Quotient.mk _ z) = φ n z)
    (θ : ∀ n : ℕ, (A' ⧸ (Ideal.span {((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A').comp (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) (algebraMap 𝒪 S π) ^ (n + 1)})) ≃+* Γ(Y' n, ((Y' n).basicOpen (φ n b))))
    (hθ : ∀ (n : ℕ) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)), θ n (Ideal.Quotient.mk _ (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A' z)) = ((Y' n).presheaf.map (homOfLE ((Y' n).basicOpen_le (φ n b))).op) (φ n z)) (n : ℕ) :
    (∀ (T : Type) [CommRing T] (f : R →+* T) (g : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) →+* T),
        f (algebraMap 𝒪 R π ^ (n + 1)) = 0 → (∀ a : ↥(FixedPoints.subalgebra 𝒪 R G), f (a : R) = g (a ⊗ₜ[𝒪] (1 : S))) →
        ∃! h : Γ(X' n, ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n)))) →+* T, h.comp (((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) = f ∧ h.comp (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) = g) := by
  intro T _ f g hft hfg
  haveI : IsFinite (D.p n) := D.p_isFinite n
  have hpV : IsAffineOpen ((D.p n) ⁻¹ᵁ (V n)) := (hVa n).preimage (D.p n)
  have hrV : IsAffineOpen ((r n) ⁻¹ᵁ (V n)) := GEOX.isAffineOpen_preimage_of_isPullback _ _ _ _ (hbase n) (V n) (hVa n)
  have hμ_r : ∀ a : ↥(FixedPoints.subalgebra 𝒪 R G), (r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl (μ n (Ideal.Quotient.mk _ a)) =
      β n (Ideal.Quotient.mk _ (a ⊗ₜ[𝒪] (1 : S))) := by
    intro a
    rw [hβ, hφ, map_one, map_one, map_one, mul_one]
  have ht : ((algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π ^ (n + 1) : ↥(FixedPoints.subalgebra 𝒪 R G)) : R) =
      algebraMap 𝒪 R π ^ (n + 1) := by
    simp only [SubmonoidClass.coe_pow]; rfl
  have htP : (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π ^ (n + 1)) ⊗ₜ[𝒪] (1 : S) =
      algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_pow, one_pow]
  exact GEOX.P1_core (fun a : ↥(FixedPoints.subalgebra 𝒪 R G) => (a : R)) (fun a => a ⊗ₜ[𝒪] (1 : S))
    (X n) (X' n) (D.Y n) (Y' n) (q n) (p' n) (D.p n) (r n) (hsq n) (V n) (hVa n) hpV hrV _
    (algebraMap 𝒪 R π ^ (n + 1)) (algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)) (lvl n) (β n)
    (fun a => μ n (Ideal.Quotient.mk _ a)) ((μ n).surjective.comp Ideal.Quotient.mk_surjective)
    (hμ_p n) hμ_r (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π ^ (n + 1)) ht htP T f g hft hfg

namespace C3GeoX

set_option maxHeartbeats 6400000 in

theorem sections_package
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
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))

    (A' : Type) [CommRing A'] [Algebra (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A'] [IsLocalization.Away b A']
    [Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A'] [IsScalarTower ↥(FixedPoints.subalgebra 𝒪 R G) (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A']

    (β : ∀ n : ℕ, ((↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) ⧸ (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})) ≃+* Γ(Y' n, (r n) ⁻¹ᵁ (V n)))
    (hβ : ∀ (n : ℕ) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)), β n (Ideal.Quotient.mk _ z) = φ n z)
    (θ : ∀ n : ℕ, (A' ⧸ (Ideal.span {((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A').comp (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) (algebraMap 𝒪 S π) ^ (n + 1)})) ≃+* Γ(Y' n, ((Y' n).basicOpen (φ n b))))
    (hθ : ∀ (n : ℕ) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)), θ n (Ideal.Quotient.mk _ (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A' z)) = ((Y' n).presheaf.map (homOfLE ((Y' n).basicOpen_le (φ n b))).op) (φ n z)) (n : ℕ) :

    (∀ (T : Type) [CommRing T] (f : R →+* T) (g : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) →+* T),
        f (algebraMap 𝒪 R π ^ (n + 1)) = 0 → (∀ a : ↥(FixedPoints.subalgebra 𝒪 R G), f (a : R) = g (a ⊗ₜ[𝒪] (1 : S))) →
        ∃! h : Γ(X' n, ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n)))) →+* T, h.comp (((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) = f ∧ h.comp (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) = g) ∧

    @IsLocalization.Away (Γ(X' n, ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))) _ ((((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) b) (Γ(X' n, ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))))) _ (((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom).toAlgebra ∧

    (∀ (hle : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (xt' n) ⁻¹ᵁ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1))))) (x : R),
        ((xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) hle).hom ((((q (n + 1)).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq (n + 1)).w]))).hom.comp ((lvl (n + 1)).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ ((n + 1) + 1)})))) x) = (((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) x) ∧
    (∀ (hle : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (xt' n) ⁻¹ᵁ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1))))) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)),
        ((xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) hle).hom ((((p' (n + 1)).app ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))).hom.comp ((β (n + 1)).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ ((n + 1) + 1)})))) z) = (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) z) ∧
    (∀ (g : G) (hle : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (a' n g⁻¹).hom ⁻¹ᵁ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n)))) (x : R),
        ((a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) hle).hom ((((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) x) = (((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) (g • x)) ∧
    (∀ (g : G) (hle : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (a' n g⁻¹).hom ⁻¹ᵁ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n)))) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)),
        ((a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) hle).hom ((((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) z) = (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) z) ∧
    (∀ s : S, (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) ((1 : ↥(FixedPoints.subalgebra 𝒪 R G)) ⊗ₜ[𝒪] s) =
        ((xb' n).appLE ⊤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) ∧
    (∀ a : ↥(FixedPoints.subalgebra 𝒪 R G), (((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) (a : R) = (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) (a ⊗ₜ[𝒪] (1 : S))) ∧

    (∀ z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S), ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom ((((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) z) =
        ((p' n).app ((Y' n).basicOpen (φ n b))).hom (θ n (Ideal.Quotient.mk _ (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A' z)))) ∧

    (∀ (hle : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (xt' n) ⁻¹ᵁ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1))))) (hle' : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ (xt' n) ⁻¹ᵁ ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))))
        (t : Γ(X' (n + 1), ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))))),
        ((xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) hle').hom (((X' (n + 1)).presheaf.map (homOfLE ((fun x hx => (Y' (n + 1)).basicOpen_le (φ (n + 1) b) hx) : ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ≤ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))))).op).hom t) = ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom (((xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) hle).hom t)) ∧
    (∀ (g : G) (hle : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (a' n g⁻¹).hom ⁻¹ᵁ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n)))) (hle' : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ (a' n g⁻¹).hom ⁻¹ᵁ ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))))
        (t : Γ(X' n, ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))),
        ((a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) hle').hom (((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom t) = ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom (((a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) hle).hom t)) ∧
    (∀ t : Γ(Spec (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)})), ⊤),
        ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom (((xb' n).appLE ⊤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) le_top).hom t) = ((xb' n).appLE ⊤ ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_top).hom t) :=
  ⟨C3GeoX.P1 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat haff G a ha_over ha_xt D S X' xb' xt' a' q hq hcart' hq_xt hq_a ha'_over Y' yb' yt' p' r hbase hsq hyt'r hyt'b hp'_over hp'_inv hp'_xt V hVa hV R hRc hRtf hRft lvl μ hlvl_xt hlvl_smul hlvl_xb hμ_yt hμ_p hμ_yb b φ hφ hφs hV' R' hR'c hR'tf lvl' hlvl'_xt hlvl'_smul hlvl'_xb A' β hβ θ hθ n, C3GeoX.P2 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat haff G a ha_over ha_xt D S X' xb' xt' a' q hq hcart' hq_xt hq_a ha'_over Y' yb' yt' p' r hbase hsq hyt'r hyt'b hp'_over hp'_inv hp'_xt V hVa hV R hRc hRtf hRft lvl μ hlvl_xt hlvl_smul hlvl_xb hμ_yt hμ_p hμ_yb b φ hφ hφs hV' R' hR'c hR'tf lvl' hlvl'_xt hlvl'_smul hlvl'_xb A' β hβ θ hθ n, C3GeoX.laws 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat haff G a ha_over ha_xt D S X' xb' xt' a' q hq hcart' hq_xt hq_a ha'_over Y' yb' yt' p' r hbase hsq hyt'r hyt'b hp'_over hp'_inv hp'_xt V hVa hV R hRc hRtf hRft lvl μ hlvl_xt hlvl_smul hlvl_xb hμ_yt hμ_p hμ_yb b φ hφ hφs hV' R' hR'c hR'tf lvl' hlvl'_xt hlvl'_smul hlvl'_xb A' β hβ θ hθ n⟩

end C3GeoX

set_option autoImplicit false

open TensorProduct

namespace GeoXAlg

theorem ringHom_ext_tmul {A R A' T : Type} [CommRing A] [CommRing R] [CommRing A'] [Semiring T]
    [Algebra A R] [Algebra A A'] {f g : R ⊗[A] A' →+* T} (h : ∀ (x : R) (w : A'), f (x ⊗ₜ w) = g (x ⊗ₜ w)) :
    f = g := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x w => exact h x w
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem ringHom_ext_quot_tmul {A R A' T : Type} [CommRing A] [CommRing R] [CommRing A'] [Semiring T]
    [Algebra A R] [Algebra A A'] (I : Ideal (R ⊗[A] A')) {f g : (R ⊗[A] A') ⧸ I →+* T}
    (h : ∀ (x : R) (w : A'), f (Ideal.Quotient.mk I (x ⊗ₜ w)) = g (Ideal.Quotient.mk I (x ⊗ₜ w))) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  exact ringHom_ext_tmul (fun x w => h x w)

section Core

variable {A R AS A' : Type} [CommRing A] [CommRing R] [CommRing AS] [CommRing A']
  [Algebra A R] [Algebra A AS] [Algebra AS A'] [Algebra A A'] [IsScalarTower A AS A']
  (b : AS) [IsLocalization.Away b A']
  (πA : A) (πR : R) (hπR : algebraMap A R πA = πR) (k : ℕ)
  {P : Type} [CommRing P] (u₁ : R →+* P) (u₂ : AS →+* P)
  (hu : ∀ a : A, u₁ (algebraMap A R a) = u₂ (algebraMap A AS a))
  (hu₁π : u₁ (πR ^ k) = 0)
  (P1 : ∀ (T : Type) [CommRing T] (f : R →+* T) (g : AS →+* T), f (πR ^ k) = 0 →
    (∀ a : A, f (algebraMap A R a) = g (algebraMap A AS a)) → ∃! h : P →+* T, h.comp u₁ = f ∧ h.comp u₂ = g)
  {QD : Type} [CommRing QD] [Algebra P QD] [IsLocalization.Away (u₂ b) QD]
  (vD : A' →+* QD) (hvD : ∀ z : AS, vD (algebraMap AS A' z) = algebraMap P QD (u₂ z))

abbrev IB : Ideal (R ⊗[A] A') := Ideal.span {(πR ^ k) ⊗ₜ[A] (1 : A')}

noncomputable def fwd₀ : R ⊗[A] A' →+* QD :=
  letI : Algebra A QD := ((algebraMap P QD).comp (u₁.comp (algebraMap A R))).toAlgebra
  (Algebra.TensorProduct.lift
    ({ toRingHom := (algebraMap P QD).comp u₁, commutes' := fun _ => rfl } : R →ₐ[A] QD)
    ({ toRingHom := vD
       commutes' := fun a => by
        show vD (algebraMap A A' a) = algebraMap P QD (u₁ (algebraMap A R a))
        rw [IsScalarTower.algebraMap_apply A AS A', hvD, hu] } : A' →ₐ[A] QD)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem fwd₀_tmul (x : R) (w : A') :
    fwd₀ (u₁ := u₁) (u₂ := u₂) (hu := hu) (vD := vD) (hvD := hvD) (x ⊗ₜ w) = algebraMap P QD (u₁ x) * vD w := rfl

include hu₁π in
theorem fwd₀_vanishes : ∀ z ∈ IB (A' := A') πR k, fwd₀ (u₁ := u₁) (u₂ := u₂) (hu := hu) (vD := vD) (hvD := hvD) z = 0 := by
  intro z hz
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  rw [map_mul, fwd₀_tmul, hu₁π, map_zero, zero_mul, mul_zero]

noncomputable def fwd : (R ⊗[A] A') ⧸ IB (A' := A') πR k →+* QD :=
  Ideal.Quotient.lift _ (fwd₀ (u₁ := u₁) (u₂ := u₂) (hu := hu) (vD := vD) (hvD := hvD))
    (fwd₀_vanishes (πR := πR) (k := k) (u₁ := u₁) (u₂ := u₂) (hu := hu) (hu₁π := hu₁π) (vD := vD) (hvD := hvD))

theorem fwd_mk_tmul (x : R) (w : A') :
    fwd (πR := πR) (k := k) (u₁ := u₁) (u₂ := u₂) (hu := hu) (hu₁π := hu₁π) (vD := vD) (hvD := hvD)
      (Ideal.Quotient.mk _ (x ⊗ₜ w)) = algebraMap P QD (u₁ x) * vD w := rfl

noncomputable def inL : R →+* (R ⊗[A] A') ⧸ IB (A' := A') πR k :=
  (Ideal.Quotient.mk _).comp (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := R) (B := A'))

noncomputable def inR : AS →+* (R ⊗[A] A') ⧸ IB (A' := A') πR k :=
  (Ideal.Quotient.mk _).comp ((Algebra.TensorProduct.includeRight (R := A) (A := R) (B := A')).toRingHom.comp (algebraMap AS A'))

theorem inL_apply (x : R) : inL (A := A) (A' := A') πR k x = Ideal.Quotient.mk _ (x ⊗ₜ (1 : A')) := rfl
theorem inR_apply (z : AS) : inR (A := A) (R := R) (A' := A') πR k z = Ideal.Quotient.mk _ ((1 : R) ⊗ₜ algebraMap AS A' z) := rfl

theorem inL_pow : inL (A := A) (A' := A') πR k (πR ^ k) = 0 := by
  rw [inL_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

theorem inL_inR (a : A) : inL (A := A) (A' := A') πR k (algebraMap A R a) = inR (A := A) (R := R) (A' := A') πR k (algebraMap A AS a) := by
  rw [inL_apply, inR_apply, ← IsScalarTower.algebraMap_apply A AS A', Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

include P1 in

theorem exists_bwd₀ : ∃ h : P →+* (R ⊗[A] A') ⧸ IB (A' := A') πR k,
    h.comp u₁ = inL (A := A) (A' := A') πR k ∧ h.comp u₂ = inR (A := A) (R := R) (A' := A') πR k :=
  (P1 ((R ⊗[A] A') ⧸ IB (A' := A') πR k) (inL (A := A) (A' := A') πR k) (inR (A := A) (R := R) (A' := A') πR k)
    (inL_pow (A := A) (A' := A') πR k) (inL_inR (R := R) (A' := A') πR k)).exists

include b hπR hu hu₁π P1 hvD in

theorem exists_kappa :
    ∃ κ : ((R ⊗[A] A') ⧸ IB (A' := A') πR k) ≃+* QD,
      ∀ (x : R) (w : A'), κ (Ideal.Quotient.mk _ (x ⊗ₜ w)) = algebraMap P QD (u₁ x) * vD w := by
  classical
  obtain ⟨h, hh₁, hh₂⟩ := exists_bwd₀ (A' := A') (πR := πR) (k := k) (u₁ := u₁) (u₂ := u₂) (P1 := P1)
  have hh₁' : ∀ x : R, h (u₁ x) = Ideal.Quotient.mk _ (x ⊗ₜ (1 : A')) := fun x => by
    rw [← RingHom.comp_apply, hh₁]; rfl
  have hh₂' : ∀ z : AS, h (u₂ z) = Ideal.Quotient.mk _ ((1 : R) ⊗ₜ algebraMap AS A' z) := fun z => by
    rw [← RingHom.comp_apply, hh₂]; rfl

  have hunit : IsUnit (h (u₂ b)) := by
    rw [hh₂']
    exact ((IsLocalization.Away.algebraMap_isUnit (S := A') b).map
      (Algebra.TensorProduct.includeRight (R := A) (A := R) (B := A'))).map (Ideal.Quotient.mk _)

  let ψ : QD →+* (R ⊗[A] A') ⧸ IB (A' := A') πR k :=
    IsLocalization.Away.lift (S := QD) (P := (R ⊗[A] A') ⧸ IB (A' := A') πR k) (u₂ b) hunit
  have hψ : ∀ p : P, ψ (algebraMap P QD p) = h p := fun p =>
    IsLocalization.Away.lift_eq (S := QD) (P := (R ⊗[A] A') ⧸ IB (A' := A') πR k) (u₂ b) hunit p

  let φ : (R ⊗[A] A') ⧸ IB (A' := A') πR k →+* QD :=
    fwd (πR := πR) (k := k) (u₁ := u₁) (u₂ := u₂) (hu := hu) (hu₁π := hu₁π) (vD := vD) (hvD := hvD)
  have hφ : ∀ (x : R) (w : A'), φ (Ideal.Quotient.mk _ (x ⊗ₜ w)) = algebraMap P QD (u₁ x) * vD w := fun x w => rfl

  have hψv : ψ.comp vD =
      (Ideal.Quotient.mk _).comp (Algebra.TensorProduct.includeRight (R := A) (A := R) (B := A')).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers b)
    refine RingHom.ext fun z => ?_
    show ψ (vD (algebraMap AS A' z)) = Ideal.Quotient.mk _ ((1 : R) ⊗ₜ algebraMap AS A' z)
    rw [hvD, hψ, hh₂']
  have hψv' : ∀ w : A', ψ (vD w) = Ideal.Quotient.mk _ ((1 : R) ⊗ₜ w) := fun w =>
    (RingHom.congr_fun hψv w : _)

  have left : ψ.comp φ = RingHom.id _ := by
    apply ringHom_ext_quot_tmul
    intro x w
    show ψ (φ (Ideal.Quotient.mk _ (x ⊗ₜ w))) = Ideal.Quotient.mk _ (x ⊗ₜ w)
    rw [hφ, map_mul, hψ, hh₁', hψv', ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

  have hφh : φ.comp h = algebraMap P QD := by
    have H := P1 QD ((algebraMap P QD).comp u₁) ((algebraMap P QD).comp u₂)
      (by rw [RingHom.comp_apply, hu₁π, map_zero]) (fun a => by rw [RingHom.comp_apply, RingHom.comp_apply, hu])
    obtain ⟨h', -, huniq⟩ := H
    have e1 : φ.comp h = h' := huniq _ ⟨?_, ?_⟩
    · have e2 : algebraMap P QD = h' := huniq _ ⟨rfl, rfl⟩
      exact e1.trans e2.symm
    · refine RingHom.ext fun x => ?_
      show φ (h (u₁ x)) = algebraMap P QD (u₁ x)
      rw [hh₁', hφ, map_one, mul_one]
    · refine RingHom.ext fun z => ?_
      show φ (h (u₂ z)) = algebraMap P QD (u₂ z)
      rw [hh₂', hφ, map_one, map_one, one_mul, hvD]

  have right : φ.comp ψ = RingHom.id QD := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (u₂ b))
    rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, hφh, RingHom.id_comp]
  exact ⟨RingEquiv.ofRingHom φ ψ right left, fun x w => hφ x w⟩

end Core

section Laws

theorem ext_away {AS A' X : Type} [CommRing AS] [CommRing A'] [Semiring X] [Algebra AS A'] (b : AS)
    [IsLocalization.Away b A'] (f g : A' →+* X) (h : ∀ z : AS, f (algebraMap AS A' z) = g (algebraMap AS A' z)) :
    ∀ w : A', f w = g w :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers b) (RingHom.ext fun z => h z))

theorem transfer_of_generators {A R A' P P' QD QD' : Type} [CommRing A] [CommRing R] [CommRing A']
    [Algebra A R] [Algebra A A'] [CommRing P] [CommRing P'] [CommRing QD] [CommRing QD']
    (I I' : Ideal (R ⊗[A] A')) (κ : ((R ⊗[A] A') ⧸ I) ≃+* QD) (κ' : ((R ⊗[A] A') ⧸ I') ≃+* QD')
    (ρ : P →+* QD) (ρ' : P' →+* QD') (u₁ : R →+* P) (u₁' : R →+* P') (vD : A' →+* QD) (vD' : A' →+* QD')
    (hκ : ∀ (x : R) (w : A'), κ (Ideal.Quotient.mk I (x ⊗ₜ w)) = ρ (u₁ x) * vD w)
    (hκ' : ∀ (x : R) (w : A'), κ' (Ideal.Quotient.mk I' (x ⊗ₜ w)) = ρ' (u₁' x) * vD' w)
    (T : QD' →+* QD) (ha : ∀ x : R, T (ρ' (u₁' x)) = ρ (u₁ x)) (hb : ∀ w : A', T (vD' w) = vD w) :
    ∀ z : R ⊗[A] A', T (κ' (Ideal.Quotient.mk I' z)) = κ (Ideal.Quotient.mk I z) := by
  have := ringHom_ext_tmul (A := A) (R := R) (A' := A')
    (f := T.comp (κ'.toRingHom.comp (Ideal.Quotient.mk I'))) (g := κ.toRingHom.comp (Ideal.Quotient.mk I))
    (fun x w => by
      show T (κ' (Ideal.Quotient.mk I' (x ⊗ₜ w))) = κ (Ideal.Quotient.mk I (x ⊗ₜ w))
      rw [hκ, hκ', map_mul, ha, hb])
  intro z
  exact RingHom.congr_fun this z

theorem law_transfer {D D' QD QD' RQ RQ' : Type} [CommRing D] [CommRing D'] [CommRing QD] [CommRing QD']
    [CommRing RQ] [CommRing RQ']
    (κ : D ≃+* QD) (κ' : D' ≃+* QD') (L : RQ ≃+* QD) (L' : RQ' ≃+* QD') (T : QD' →+* QD)
    (x' : D') (x : D) (Hx : T (κ' x') = κ x) (a' : RQ') (a : RQ) (HL : T (L' a') = L a)
    (h : (κ'.trans L'.symm) x' = a') : (κ.trans L.symm) x = a := by
  rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq] at h ⊢
  rw [← Hx, h, HL]

theorem law_of_eq {D QD RQ : Type} [CommRing D] [CommRing QD] [CommRing RQ]
    (κ : D ≃+* QD) (L : RQ ≃+* QD) (x : D) (a : RQ) (h : κ x = L a) : (κ.trans L.symm) x = a := by
  rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq, h]

theorem eq_of_law {D QD RQ : Type} [CommRing D] [CommRing QD] [CommRing RQ]
    (κ : D ≃+* QD) (L : RQ ≃+* QD) (x : D) (a : RQ) (h : (κ.trans L.symm) x = a) : κ x = L a := by
  rwa [RingEquiv.trans_apply, RingEquiv.symm_apply_eq] at h

end Laws

end GeoXAlg

open GeoXAlg in
set_option maxHeartbeats 16000000 in
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
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))

    (A' : Type) [CommRing A'] [Algebra (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A'] [IsLocalization.Away b A']
    [Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A'] [IsScalarTower ↥(FixedPoints.subalgebra 𝒪 R G) (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A']

    (β : ∀ n : ℕ, ((↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) ⧸ (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})) ≃+* Γ(Y' n, (r n) ⁻¹ᵁ (V n)))
    (hβ : ∀ (n : ℕ) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)), β n (Ideal.Quotient.mk _ z) = φ n z)
    (θ : ∀ n : ℕ, (A' ⧸ (Ideal.span {((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A').comp (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) (algebraMap 𝒪 S π) ^ (n + 1)})) ≃+* Γ(Y' n, ((Y' n).basicOpen (φ n b))))
    (hθ : ∀ (n : ℕ) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)), θ n (Ideal.Quotient.mk _ (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A' z)) = ((Y' n).presheaf.map (homOfLE ((Y' n).basicOpen_le (φ n b))).op) (φ n z)) :
    ∃ (τ : ∀ n : ℕ, ((R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') ⧸
          Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) ≃+*
        (R' ⧸ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)})),
      (∀ (n : ℕ) (z : R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') (y : R'),
        τ (n + 1) (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y → τ n (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ y) ∧
      (∀ (n : ℕ) (g : G) (x : R) (w : A') (y : R'),
        τ n (Ideal.Quotient.mk _ (x ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ y →
        τ n (Ideal.Quotient.mk _ ((g • x) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ (g • y)) ∧
      (∀ (n : ℕ) (s : S),
        τ n (Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] ((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A').comp (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) s)) = Ideal.Quotient.mk _ (algebraMap S R' s)) ∧
      (∀ (n : ℕ) (w : A') (y : R'), τ n (Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w)) = Ideal.Quotient.mk _ y →
          (p' n).appLE ((Y' n).basicOpen (φ n b)) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_rfl (θ n (Ideal.Quotient.mk _ w)) = lvl' n (Ideal.Quotient.mk _ y)) := by
  classical

  have hpack := fun n : ℕ => C3GeoX.sections_package 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat haff G a ha_over ha_xt D S X' xb' xt' a' q hq hcart' hq_xt hq_a ha'_over Y' yb' yt' p' r hbase hsq hyt'r hyt'b hp'_over hp'_inv hp'_xt V hVa hV R hRc hRtf hRft lvl μ hlvl_xt hlvl_smul hlvl_xb hμ_yt hμ_p hμ_yb b φ hφ hφs hV' R' hR'c hR'tf lvl' hlvl'_xt hlvl'_smul hlvl'_xb A' β hβ θ hθ n

  have key : ∀ n : ℕ, ∃ κ : ((R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A') ⧸ Ideal.span {(algebraMap 𝒪 R π ^ (n + 1)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) ≃+* Γ(X' n, ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)))),
      ∀ (x : R) (w : A'), κ (Ideal.Quotient.mk _ (x ⊗ₜ w)) = ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom ((((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) x) * (((p' n).app ((Y' n).basicOpen (φ n b))).hom.comp ((θ n).toRingHom.comp (Ideal.Quotient.mk _))) w := by
    intro n
    obtain ⟨P1, P2, -, -, -, -, -, L6, L7, -, -, -⟩ := hpack n
    letI instAlg : Algebra Γ(X' n, ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n)))) Γ(X' n, ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)))) := (((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom).toAlgebra
    haveI : IsLocalization.Away ((((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) b) Γ(X' n, ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)))) := P2
    have hu : ∀ a' : ↥(FixedPoints.subalgebra 𝒪 R G), (((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) (algebraMap ↥(FixedPoints.subalgebra 𝒪 R G) R a') = (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) (algebraMap ↥(FixedPoints.subalgebra 𝒪 R G) (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) a') :=
      fun a' => L6 a'
    have hu₁π : (((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) (algebraMap 𝒪 R π ^ (n + 1)) = 0 := by
      have h0 : Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (algebraMap 𝒪 R π ^ (n + 1)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      rw [RingHom.comp_apply, RingHom.comp_apply, h0, map_zero, map_zero]
    have hvD : ∀ z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S), (((p' n).app ((Y' n).basicOpen (φ n b))).hom.comp ((θ n).toRingHom.comp (Ideal.Quotient.mk _))) (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A' z) = algebraMap Γ(X' n, ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n)))) Γ(X' n, ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)))) ((((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) z) :=
      fun z => (L7 z).symm
    exact GeoXAlg.exists_kappa (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (R := R) (AS := (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)) (A' := A') b (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π) (algebraMap 𝒪 R π) rfl (n + 1)
      (((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) (((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) hu hu₁π
      (fun T _ f g hf hfg => P1 T f g hf (fun a' => hfg a')) (((p' n).app ((Y' n).basicOpen (φ n b))).hom.comp ((θ n).toRingHom.comp (Ideal.Quotient.mk _))) hvD
  choose κ hκ using key
  refine ⟨fun n => (κ n).trans (lvl' n).symm, ?_, ?_, ?_, ?_⟩
  ·
    intro n z y h
    dsimp only at h ⊢
    obtain ⟨-, -, L1, L2, -, -, -, -, L7, L8, -, -⟩ := hpack n
    obtain ⟨-, -, -, -, -, -, -, -, L7', -, -, -⟩ := hpack (n + 1)
    have hleW : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (xt' n) ⁻¹ᵁ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))) := by
      rw [show (xt' n) ⁻¹ᵁ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))) = ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) from ?_]
      simp only [← Scheme.Hom.comp_preimage]
      rw [← Category.assoc, hp'_xt, Category.assoc, hyt'r, ← Category.assoc, Scheme.Hom.comp_preimage, hV]
    have ha : ∀ x : R, ((xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hV'])).hom (((X' (n + 1)).presheaf.map (homOfLE ((fun x hx => (Y' (n + 1)).basicOpen_le (φ (n + 1) b) hx) : ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ≤ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))))).op).hom ((((q (n + 1)).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq (n + 1)).w]))).hom.comp ((lvl (n + 1)).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ ((n + 1) + 1)})))) x)) =
        ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom ((((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) x) := fun x => by
      rw [L8 hleW (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hV']), L1 hleW]
    have hb := GeoXAlg.ext_away (AS := (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)) b
      (((xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hV'])).hom.comp (((p' (n + 1)).app ((Y' (n + 1)).basicOpen (φ (n + 1) b))).hom.comp ((θ (n + 1)).toRingHom.comp (Ideal.Quotient.mk _)))) (((p' n).app ((Y' n).basicOpen (φ n b))).hom.comp ((θ n).toRingHom.comp (Ideal.Quotient.mk _))) (fun z => by
        have e1 : (((p' (n + 1)).app ((Y' (n + 1)).basicOpen (φ (n + 1) b))).hom.comp ((θ (n + 1)).toRingHom.comp (Ideal.Quotient.mk _))) (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A' z) = ((X' (n + 1)).presheaf.map (homOfLE ((fun x hx => (Y' (n + 1)).basicOpen_le (φ (n + 1) b) hx) : ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ≤ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))))).op).hom ((((p' (n + 1)).app ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))).hom.comp ((β (n + 1)).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ ((n + 1) + 1)})))) z) := (L7' z).symm
        have e2 : (((p' n).app ((Y' n).basicOpen (φ n b))).hom.comp ((θ n).toRingHom.comp (Ideal.Quotient.mk _))) (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A' z) = ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom ((((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) z) := (L7 z).symm
        rw [RingHom.comp_apply, e1, e2, L8 hleW (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hV']), L2 hleW])
    have Hz := GeoXAlg.transfer_of_generators _ _ (κ n) (κ (n + 1)) ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom ((X' (n + 1)).presheaf.map (homOfLE ((fun x hx => (Y' (n + 1)).basicOpen_le (φ (n + 1) b) hx) : ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ≤ ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))))).op).hom (((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) (((q (n + 1)).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((p' (n + 1)) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1)))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq (n + 1)).w]))).hom.comp ((lvl (n + 1)).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ ((n + 1) + 1)}))))
      (((p' n).app ((Y' n).basicOpen (φ n b))).hom.comp ((θ n).toRingHom.comp (Ideal.Quotient.mk _))) (((p' (n + 1)).app ((Y' (n + 1)).basicOpen (φ (n + 1) b))).hom.comp ((θ (n + 1)).toRingHom.comp (Ideal.Quotient.mk _))) (hκ n) (hκ (n + 1)) _ ha hb
    rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq] at h ⊢
    rw [← Hz z, h]
    exact hlvl'_xt n y
  ·
    intro n g x w y h
    dsimp only at h ⊢
    obtain ⟨-, -, -, -, L3, L4, -, -, L7, -, L9, -⟩ := hpack n
    have hleA : ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) ≤ (a' n g⁻¹).hom ⁻¹ᵁ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) := by
      rw [show (a' n g⁻¹).hom ⁻¹ᵁ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) = ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) from ?_]
      simp only [← Scheme.Hom.comp_preimage]
      rw [← Category.assoc, hp'_inv]
    have ha : ((a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) (by rw [← Scheme.Hom.comp_preimage, hp'_inv])).hom (((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom ((((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) x)) =
        ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom ((((q n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))) (le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, (hsq n).w]))).hom.comp ((lvl n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})))) (g • x)) := by
      rw [L9 g hleA (by rw [← Scheme.Hom.comp_preimage, hp'_inv]), L3 g hleA]
    have hb := GeoXAlg.ext_away (AS := (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)) b
      (((a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) (by rw [← Scheme.Hom.comp_preimage, hp'_inv])).hom.comp (((p' n).app ((Y' n).basicOpen (φ n b))).hom.comp ((θ n).toRingHom.comp (Ideal.Quotient.mk _)))) (((p' n).app ((Y' n).basicOpen (φ n b))).hom.comp ((θ n).toRingHom.comp (Ideal.Quotient.mk _))) (fun z => by
        have e2 : (((p' n).app ((Y' n).basicOpen (φ n b))).hom.comp ((θ n).toRingHom.comp (Ideal.Quotient.mk _))) (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A' z) = ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom ((((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) z) := (L7 z).symm
        rw [RingHom.comp_apply, e2, L9 g hleA (by rw [← Scheme.Hom.comp_preimage, hp'_inv]), L4 g hleA])
    have hb' : ∀ w' : A', ((a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) (by rw [← Scheme.Hom.comp_preimage, hp'_inv])).hom ((((p' n).app ((Y' n).basicOpen (φ n b))).hom.comp ((θ n).toRingHom.comp (Ideal.Quotient.mk _))) w') = (((p' n).app ((Y' n).basicOpen (φ n b))).hom.comp ((θ n).toRingHom.comp (Ideal.Quotient.mk _))) w' := hb
    have Hx : ((a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) (by rw [← Scheme.Hom.comp_preimage, hp'_inv])).hom ((κ n) (Ideal.Quotient.mk _ (x ⊗ₜ w))) =
        (κ n) (Ideal.Quotient.mk _ ((g • x) ⊗ₜ w)) := by
      rw [hκ, hκ, map_mul, ha, hb']
    rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq] at h ⊢
    rw [← Hx, h]
    exact hlvl'_smul n g y
  ·
    intro n s
    dsimp only
    obtain ⟨-, -, -, -, -, -, L5, -, L7, -, -, L10⟩ := hpack n
    rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq, hκ, map_one, map_one, one_mul]
    have e : (((p' n).app ((Y' n).basicOpen (φ n b))).hom.comp ((θ n).toRingHom.comp (Ideal.Quotient.mk _))) (((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) A').comp (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) s) = ((X' n).presheaf.map (homOfLE ((fun x hx => (Y' n).basicOpen_le (φ n b) hx) : ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ≤ ((p' n) ⁻¹ᵁ ((r n) ⁻¹ᵁ (V n))))).op).hom ((((p' n).app ((r n) ⁻¹ᵁ (V n))).hom.comp ((β n).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})))) ((1 : ↥(FixedPoints.subalgebra 𝒪 R G)) ⊗ₜ[𝒪] s)) := (L7 _).symm
    rw [e, L5, L10]
    exact (hlvl'_xb n s).symm
  ·
    intro n w y h
    dsimp only at h
    rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq, hκ, map_one, map_one, one_mul] at h
    rw [Scheme.Hom.appLE_eq_app]
    exact h

end S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_tensorProduct_quotient_of_ringEquiv_sections_basicOpen
end P2MW
export P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_tensorProduct_quotient_of_ringEquiv_sections_basicOpen (solution)
