-- Prove2me | solution 1 for AlgebraicGeometry.TowerQuotientDatum.univ_loc_of_isPullback_of_flat_of_forall_exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f0e0816e-8f41-5780-b2c2-3c37531bed48

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Theorems.Thm_AlgebraicGeometry_epi_morphismRestrict_of_isPullback_of_flat
import Theorems.Thm_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat
import Theorems.Thm_AlgebraicGeometry_flat_specMap_quotientMap_pow_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_univ_loc_of_isPullback_of_flat_of_forall_exists_chart

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

namespace W2GEO

noncomputable def homSpecOf (S : Scheme.{0}) (B : CommRingCat.{0}) (φ : B ⟶ Γ(S, ⊤)) : S ⟶ Spec B :=
  S.toSpecΓ ≫ Spec.map φ

theorem homSpecOf_appTop (S : Scheme.{0}) (B : CommRingCat.{0}) (φ : B ⟶ Γ(S, ⊤)) :
    (homSpecOf S B φ).appTop = (Scheme.ΓSpecIso B).hom ≫ φ := by
  rw [homSpecOf, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  exact Scheme.ΓSpecIso_naturality φ

theorem hom_Spec_ext (S : Scheme.{0}) (B : CommRingCat.{0}) (f g : S ⟶ Spec B)
    (h : (Scheme.ΓSpecIso B).inv ≫ f.appTop = (Scheme.ΓSpecIso B).inv ≫ g.appTop) : f = g :=
  ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso B).inv).mp h)

theorem eq_homSpecOf (S : Scheme.{0}) (B : CommRingCat.{0}) (f : S ⟶ Spec B) :
    f = homSpecOf S B ((Scheme.ΓSpecIso B).inv ≫ f.appTop) := by
  apply ext_of_isAffine
  rw [homSpecOf_appTop, Iso.hom_inv_id_assoc]

noncomputable def secOf {Z : Scheme.{0}} (V : Z.Opens) (B : CommRingCat.{0}) (w : (↑V : Scheme.{0}) ⟶ Spec B) :
    B →+* Γ(Z, V) :=
  ((Scheme.ΓSpecIso B).inv ≫ w.appTop ≫ V.topIso.hom).hom

theorem secOf_resLE {Z Z' : Scheme.{0}} (q : Z ⟶ Z') (V : Z.Opens) (V' : Z'.Opens) (e : V ≤ q ⁻¹ᵁ V')
    (B : CommRingCat.{0}) (w : (↑V' : Scheme.{0}) ⟶ Spec B) (b : B) :
    secOf V B (q.resLE V' V e ≫ w) b = q.appLE V' V e (secOf V' B w b) := by
  simp only [secOf, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  have key := Scheme.Hom.resLE_app_top q e
  rw [← Scheme.Hom.appTop] at key
  rw [key]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  exact Iso.inv_hom_id_apply V.topIso _

theorem eq_of_secOf_eq {Z : Scheme.{0}} (V : Z.Opens) (B : CommRingCat.{0}) (w w' : (↑V : Scheme.{0}) ⟶ Spec B)
    (h : ∀ b : B, secOf V B w b = secOf V B w' b) : w = w' := by
  apply hom_Spec_ext
  rw [← cancel_mono V.topIso.hom]
  ext b
  simpa only [secOf, Category.assoc] using h b

theorem secOf_homSpecOf {Z : Scheme.{0}} (V : Z.Opens) (B : CommRingCat.{0}) (χ : B →+* Γ(Z, V)) (b : B) :
    secOf V B (homSpecOf (↑V) B (CommRingCat.ofHom χ ≫ V.topIso.inv)) b = χ b := by
  simp only [secOf, homSpecOf_appTop, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
    CommRingCat.hom_ofHom]

theorem secOf_comp_SpecMap {Z : Scheme.{0}} (V : Z.Opens) (B B' : CommRingCat.{0}) (w : (↑V : Scheme.{0}) ⟶ Spec B')
    (ψ : B ⟶ B') (b : B) : secOf V B (w ≫ Spec.map ψ) b = secOf V B' w (ψ b) := by
  simp only [secOf, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 2
  have h1 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso B).inv b)) (Scheme.ΓSpecIso_naturality ψ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [Iso.inv_hom_id_apply (Scheme.ΓSpecIso B)] at h1
  rw [← h1]
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso B') _).symm

section Chart

variable {G : Type} [Group G] [Finite G]
  {S : Type} [CommRing S] (t : S)
  {Xs Ys : ℕ → Scheme.{0}} (ps : ∀ n : ℕ, Xs n ⟶ Ys n) (xts : ∀ n : ℕ, Xs n ⟶ Xs (n + 1))
  (yts : ∀ n : ℕ, Ys n ⟶ Ys (n + 1)) (as : ∀ n : ℕ, G →* Aut (Xs n))
  (hps_inv : ∀ (n : ℕ) (g : G), (as n g).hom ≫ ps n = ps n)
  (hps_xt : ∀ n : ℕ, xts n ≫ ps (n + 1) = ps n ≫ yts n)
  (Vp : ∀ n : ℕ, (Ys n).Opens) (hVp : ∀ n : ℕ, (yts n) ⁻¹ᵁ (Vp (n + 1)) = Vp n)
  (R' : Type) [CommRing R'] [Algebra S R'] [MulSemiringAction G R'] [SMulCommClass G S R']
  (hR'c : IsAdicComplete (Ideal.span {algebraMap S R' t}) R')
  (lvl' : ∀ n : ℕ, (R' ⧸ Ideal.span {algebraMap S R' t ^ (n + 1)}) ≃+* Γ(Xs n, (ps n) ⁻¹ᵁ (Vp n)))
  (μ' : ∀ n : ℕ, (↥(FixedPoints.subalgebra S R' G) ⧸
      Ideal.span {algebraMap S ↥(FixedPoints.subalgebra S R' G) t ^ (n + 1)}) ≃+* Γ(Ys n, Vp n))
  (hl_xt : ∀ (n : ℕ) (x : R'), (xts n).appLE ((ps (n + 1)) ⁻¹ᵁ (Vp (n + 1))) ((ps n) ⁻¹ᵁ (Vp n))
      (by rw [← Scheme.Hom.comp_preimage, hps_xt, Scheme.Hom.comp_preimage, hVp])
      (lvl' (n + 1) (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ x))
  (hl_smul : ∀ (n : ℕ) (g : G) (x : R'), (as n g⁻¹).hom.appLE ((ps n) ⁻¹ᵁ (Vp n)) ((ps n) ⁻¹ᵁ (Vp n))
      (by rw [← Scheme.Hom.comp_preimage, hps_inv]) (lvl' n (Ideal.Quotient.mk _ x)) =
      lvl' n (Ideal.Quotient.mk _ (g • x)))
  (hm_p : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra S R' G)), (ps n).appLE (Vp n) ((ps n) ⁻¹ᵁ (Vp n)) le_rfl
      (μ' n (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ (x : R')))

include hR'c hl_xt hl_smul in

theorem exists_lift (B : Type) [CommRing B] (ψ : ∀ m : ℕ, B →+* Γ(Xs m, (ps m) ⁻¹ᵁ (Vp m)))
    (hψt : ∀ (m : ℕ) (b : B), (xts m).appLE ((ps (m + 1)) ⁻¹ᵁ (Vp (m + 1))) ((ps m) ⁻¹ᵁ (Vp m))
      (by rw [← Scheme.Hom.comp_preimage, hps_xt, Scheme.Hom.comp_preimage, hVp]) (ψ (m + 1) b) = ψ m b)
    (hψg : ∀ (m : ℕ) (g : G) (b : B), (as m g⁻¹).hom.appLE ((ps m) ⁻¹ᵁ (Vp m)) ((ps m) ⁻¹ᵁ (Vp m))
      (by rw [← Scheme.Hom.comp_preimage, hps_inv]) (ψ m b) = ψ m b) :
    ∃ Φ : B →+* R', (∀ (m : ℕ) (b : B), lvl' m (Ideal.Quotient.mk _ (Φ b)) = ψ m b) ∧
      ∀ (g : G) (b : B), g • Φ b = Φ b := by
  classical
  haveI := hR'c
  let I : Ideal R' := Ideal.span {algebraMap S R' t}
  have hI : ∀ m : ℕ, I ^ (m + 1) = Ideal.span {algebraMap S R' t ^ (m + 1)} := fun m =>
    Ideal.span_singleton_pow _ _
  let e : ∀ m : ℕ, (R' ⧸ I ^ (m + 1)) ≃+* (R' ⧸ Ideal.span {algebraMap S R' t ^ (m + 1)}) := fun m =>
    Ideal.quotEquivOfEq (hI m)
  let f : ∀ m : ℕ, B →+* R' ⧸ I ^ (m + 1) := fun m =>
    (e m).symm.toRingHom.comp ((lvl' m).symm.toRingHom.comp (ψ m))
  have hf0 : ∀ (m : ℕ) (b : B), lvl' m (e m (f m b)) = ψ m b := by
    intro m b
    simp [f]
  have ha : StrictMono (fun n : ℕ => n + 1) := fun _ _ h => Nat.succ_lt_succ h
  have hf : ∀ {m : ℕ}, (Ideal.Quotient.factorPow I (ha.monotone m.le_succ)).comp (f (m + 1)) = f m := by
    intro m
    ext b
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f (m + 1) b)
    have h1 : ψ (m + 1) b = lvl' (m + 1) (Ideal.Quotient.mk _ r) := by
      rw [← hf0 (m + 1) b, ← hr, Ideal.quotEquivOfEq_mk]
    have h2 : ψ m b = lvl' m (Ideal.Quotient.mk _ r) := by
      rw [← hψt m b, h1, hl_xt]
    apply (e m).injective
    apply (lvl' m).injective
    rw [RingHom.comp_apply, ← hr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, hf0, h2,
      Ideal.quotEquivOfEq_mk]
  refine ⟨IsAdicComplete.StrictMono.liftRingHom I ha f hf, ?_, ?_⟩
  · intro m b
    have := IsAdicComplete.StrictMono.mk_liftRingHom I ha f hf (n := m) b
    rw [← hf0 m b, ← this, Ideal.quotEquivOfEq_mk]
  · intro g b
    set Φ := IsAdicComplete.StrictMono.liftRingHom I ha f hf with hΦ
    have key : ∀ (m : ℕ) (b : B), lvl' m (Ideal.Quotient.mk _ (Φ b)) = ψ m b := by
      intro m b
      have := IsAdicComplete.StrictMono.mk_liftRingHom I ha f hf (n := m) b
      rw [← hf0 m b, ← this, Ideal.quotEquivOfEq_mk]
    have : (MulSemiringAction.toRingHom G R' g).comp Φ = Φ := by
      rw [hΦ]
      apply IsAdicComplete.StrictMono.eq_liftRingHom I ha f hf
      intro m
      ext b'
      apply (e m).injective
      apply (lvl' m).injective
      rw [RingHom.comp_apply, RingHom.comp_apply, MulSemiringAction.toRingHom_apply, Ideal.quotEquivOfEq_mk,
        ← hl_smul m g, ← hΦ, key, hψg, hf0]
    exact congrArg (fun F : B →+* R' => F b) this

include hR'c hl_xt hl_smul hm_p in

theorem univ_chart (B : CommRingCat.{0})
    (w : ∀ m : ℕ, (↑((ps m) ⁻¹ᵁ (Vp m)) : Scheme.{0}) ⟶ Spec B)
    (hwg : ∀ (m : ℕ) (g : G), (as m g).hom.resLE ((ps m) ⁻¹ᵁ (Vp m)) ((ps m) ⁻¹ᵁ (Vp m))
      (by rw [← Scheme.Hom.comp_preimage, hps_inv]) ≫ w m = w m)
    (hwt : ∀ m : ℕ, (xts m).resLE ((ps (m + 1)) ⁻¹ᵁ (Vp (m + 1))) ((ps m) ⁻¹ᵁ (Vp m))
      (by rw [← Scheme.Hom.comp_preimage, hps_xt, Scheme.Hom.comp_preimage, hVp]) ≫ w (m + 1) = w m) :
    ∃ v : ∀ m : ℕ, (↑(Vp m) : Scheme.{0}) ⟶ Spec B, ∀ m : ℕ, (ps m) ∣_ (Vp m) ≫ v m = w m := by
  let ψ : ∀ m : ℕ, (B : Type) →+* Γ(Xs m, (ps m) ⁻¹ᵁ (Vp m)) := fun m => secOf ((ps m) ⁻¹ᵁ (Vp m)) B (w m)
  have hψt : ∀ (m : ℕ) (b : B), (xts m).appLE ((ps (m + 1)) ⁻¹ᵁ (Vp (m + 1))) ((ps m) ⁻¹ᵁ (Vp m))
      (by rw [← Scheme.Hom.comp_preimage, hps_xt, Scheme.Hom.comp_preimage, hVp]) (ψ (m + 1) b) = ψ m b := by
    intro m b
    simp only [ψ]
    rw [← secOf_resLE, hwt]
  have hψg : ∀ (m : ℕ) (g : G) (b : B), (as m g⁻¹).hom.appLE ((ps m) ⁻¹ᵁ (Vp m)) ((ps m) ⁻¹ᵁ (Vp m))
      (by rw [← Scheme.Hom.comp_preimage, hps_inv]) (ψ m b) = ψ m b := by
    intro m g b
    simp only [ψ]
    rw [← secOf_resLE, hwg]
  obtain ⟨Φ, hΦ, hΦG⟩ := exists_lift t ps xts yts as hps_inv hps_xt Vp hVp R' hR'c lvl' hl_xt hl_smul B ψ hψt hψg
  let ΦA : (B : Type) →+* ↥(FixedPoints.subalgebra S R' G) :=
    Φ.codRestrict (FixedPoints.subalgebra S R' G).toSubring (fun b g => hΦG g b)
  let χ : ∀ m : ℕ, (B : Type) →+* Γ(Ys m, Vp m) := fun m =>
    (μ' m).toRingHom.comp ((Ideal.Quotient.mk _).comp ΦA)
  refine ⟨fun m => homSpecOf _ B (CommRingCat.ofHom (χ m) ≫ (Vp m).topIso.inv), fun m => ?_⟩
  have e0 : (ps m) ∣_ (Vp m) = (ps m).resLE (Vp m) ((ps m) ⁻¹ᵁ (Vp m)) le_rfl := by
    simp [Scheme.Hom.resLE]
  rw [e0]
  apply eq_of_secOf_eq
  intro b
  rw [secOf_resLE, secOf_homSpecOf]
  change (ps m).appLE (Vp m) ((ps m) ⁻¹ᵁ (Vp m)) _ (μ' m (Ideal.Quotient.mk _ (ΦA b))) = ψ m b
  rw [hm_p m (ΦA b)]
  exact hΦ m b

end Chart

theorem surjective_SpecMap_factor (A : Type) [CommRing A] (t : A) (n : ℕ)
    (hST : Ideal.span {t ^ (n + 1 + 1)} ≤ Ideal.span {t ^ (n + 1)}) :
    Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hST))).base := by
  have key : Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.factor hST)) := by
    intro x
    have hx : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor hST)) := by
      rw [range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective hST)]
      intro z hz
      obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective z
      have ho : o ∈ Ideal.span {t ^ (n + 1)} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.factor_mk hST]
        exact hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ho
      have hπx : Ideal.Quotient.mk (Ideal.span {t ^ (n + 1 + 1)}) t ∈ x.asIdeal := by
        apply x.isPrime.mem_of_pow_mem (n + 1 + 1)
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
        exact x.asIdeal.zero_mem
      rw [map_mul, map_pow]
      exact x.asIdeal.mul_mem_left _ (x.asIdeal.pow_mem_of_mem hπx _ (Nat.succ_pos _))
    exact hx
  intro x
  obtain ⟨y, hy⟩ := key x
  refine ⟨y, ?_⟩
  rw [← hy]
  erw [Spec.map_apply, CommRingCat.hom_ofHom]

section Global

variable
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

include hcart' in
theorem surjective_xt' (n : ℕ) : Function.Surjective (xt' n).base := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1))))))) :=
    ⟨surjective_SpecMap_factor S (algebraMap 𝒪 S π) n _⟩
  exact (MorphismProperty.of_isPullback (P := @Surjective) (hcart' n).flip this).surj

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt in
include hcart' hp'_xt in
theorem surjective_yt' (hsurj : ∀ n : ℕ, Function.Surjective (p' n).base) (n : ℕ) :
    Function.Surjective (yt' n).base := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj (n + 1) y
  obtain ⟨x', rfl⟩ := surjective_xt' 𝒪 π S X' xb' xt' hcart' n x
  refine ⟨(p' n).base x', ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hp'_xt, Scheme.Hom.comp_apply]

theorem isHomeomorph_yt (n : ℕ) : IsClosedImmersion (D.yt n) ∧ IsHomeomorph (D.yt n).base := by
  have hle : Ideal.span {π ^ (n + 1 + 1)} ≤ Ideal.span {π ^ (n + 1)} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle))) :=
    IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective hle)
  haveI : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle))) :=
    ⟨surjective_SpecMap_factor 𝒪 π n hle⟩
  haveI : IsClosedImmersion (D.yt n) := MorphismProperty.of_isPullback (D.yt_isPullback n).flip inferInstance
  haveI : Surjective (D.yt n) := MorphismProperty.of_isPullback (D.yt_isPullback n).flip inferInstance
  exact ⟨inferInstance, isHomeomorph_iff_isEmbedding_surjective.2 ⟨(D.yt n).isClosedEmbedding.isEmbedding, (D.yt n).surjective⟩⟩

include hπ in

theorem exists_affine_family (n : ℕ) (y : D.Y n) :
    ∃ (V : ∀ k : ℕ, (D.Y k).Opens), (∀ k, IsAffineOpen (V k)) ∧ (∀ k, (D.yt k) ⁻¹ᵁ (V (k + 1)) = V k) ∧ y ∈ V n := by
  classical
  have hhom := fun k => (isHomeomorph_yt 𝒪 π X xb xt G a D k).2

  have key : ∀ y₀ : D.Y 0, ∃ (V : ∀ k : ℕ, (D.Y k).Opens), (∀ k, IsAffineOpen (V k)) ∧
      (∀ k, (D.yt k) ⁻¹ᵁ (V (k + 1)) = V k) ∧ y₀ ∈ V 0 := by
    intro y₀
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
      (D.Y 0).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y₀) isOpen_univ
    let V : ∀ k : ℕ, (D.Y k).Opens := fun k =>
      Nat.rec (motive := fun k => (D.Y k).Opens) W
        (fun k Vk => ⟨(D.yt k).base '' (Vk : Set (D.Y k)), (hhom k).isOpenMap _ Vk.isOpen⟩) k
    have hV0 : V 0 = W := rfl
    have hV : ∀ k, (D.yt k) ⁻¹ᵁ (V (k + 1)) = V k := by
      intro k
      ext z
      show (D.yt k).base z ∈ (D.yt k).base '' (V k : Set _) ↔ z ∈ (V k : Set _)
      exact (hhom k).injective.mem_set_image
    have hVa : ∀ k, IsAffineOpen (V k) := by
      intro k
      induction k with
      | zero => exact hW
      | succ k ih =>
        exact AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat 𝒪 π hπ D.Y D.yb D.yt
          D.yt_isPullback D.yb_flat k (V (k + 1)) (by rw [hV]; exact ih)
    exact ⟨V, hVa, hV, hyW⟩
  induction n with
  | zero => exact key y
  | succ n ih =>
    obtain ⟨y', rfl⟩ := (hhom n).surjective y
    obtain ⟨V, hVa, hV, hy'⟩ := ih y'
    refine ⟨V, hVa, hV, ?_⟩
    show y' ∈ (D.yt n) ⁻¹ᵁ (V (n + 1))
    rw [hV]
    exact hy'

end Global

theorem glue_local {X' Y' T : Scheme.{0}} (p' : X' ⟶ Y') (hepi : ∀ O : Y'.Opens, Epi (p' ∣_ O))
    (U : Y'.Opens) (u : (↑(p' ⁻¹ᵁ U) : Scheme.{0}) ⟶ T)
    (hloc : ∀ y : Y', y ∈ U → ∃ (W : Y'.Opens) (hWU : W ≤ U), y ∈ W ∧
      ∃ v : (↑W : Scheme.{0}) ⟶ T, p' ∣_ W ≫ v = X'.homOfLE (p'.preimage_mono hWU) ≫ u) :
    ∃ vn : (↑U : Scheme.{0}) ⟶ T, p' ∣_ U ≫ vn = u := by
  classical
  choose W hWU hyW v hv using hloc

  have agree : ∀ (y : Y') (hy : y ∈ U) (O : Y'.Opens) (hO : O ≤ W y hy),
      p' ∣_ O ≫ Y'.homOfLE hO ≫ v y hy = X'.homOfLE ((p'.preimage_mono hO).trans (p'.preimage_mono (hWU y hy))) ≫ u := by
    intro y hy O hO
    have e2 : p' ∣_ O ≫ Y'.homOfLE hO = X'.homOfLE (p'.preimage_mono hO) ≫ p' ∣_ (W y hy) := by
      simp [← cancel_mono (Scheme.Opens.ι _)]
    rw [← Category.assoc, e2, Category.assoc, hv y hy, ← Category.assoc, Scheme.homOfLE_homOfLE]
  let 𝒰 : (↑U : Scheme.{0}).OpenCover :=
    { I₀ := ↥U
      X := fun y => ↑(W y.1 y.2)
      f := fun y => Y'.homOfLE (hWU y.1 y.2)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ⟨x, ⟨x.1, hyW x.1 x.2⟩, Subtype.ext (by simp)⟩, inferInstance⟩ }
  have hcompat : ∀ i j : 𝒰.I₀, Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ v i.1 i.2 =
      Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ v j.1 j.2 := by
    intro i j
    refine (cancel_epi (isPullback_opens_inf_le (hWU i.1 i.2) (hWU j.1 j.2)).isoPullback.hom).mp ?_
    simp only [𝒰, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    haveI := hepi (W i.1 i.2 ⊓ W j.1 j.2)
    rw [← cancel_epi (p' ∣_ (W i.1 i.2 ⊓ W j.1 j.2)), agree i.1 i.2 _ inf_le_left, agree j.1 j.2 _ inf_le_right]
  refine ⟨𝒰.glueMorphisms (fun y => v y.1 y.2) hcompat, ?_⟩
  let 𝒱 : (↑(p' ⁻¹ᵁ U) : Scheme.{0}).OpenCover :=
    { I₀ := ↥U
      X := fun y => ↑(p' ⁻¹ᵁ (W y.1 y.2))
      f := fun y => X'.homOfLE (p'.preimage_mono (hWU y.1 y.2))
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ⟨⟨p'.base x.1, x.2⟩, ⟨x.1, hyW _ x.2⟩, Subtype.ext (by simp)⟩, inferInstance⟩ }
  refine 𝒱.hom_ext _ _ fun y => ?_
  have e3 : X'.homOfLE (p'.preimage_mono (hWU y.1 y.2)) ≫ p' ∣_ U = p' ∣_ (W y.1 y.2) ≫ Y'.homOfLE (hWU y.1 y.2) := by
    simp [← cancel_mono (Scheme.Opens.ι _)]
  simp only [𝒱]
  rw [← Category.assoc, e3, Category.assoc]
  change p' ∣_ (W y.1 y.2) ≫ 𝒰.f y ≫ 𝒰.glueMorphisms (fun y => v y.1 y.2) hcompat = _
  rw [Scheme.Cover.ι_glueMorphisms]
  exact hv y.1 y.2

section Global2

variable
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

include hcart' hp'_xt hp'_inv hπ hbase hsq in
omit hdvr hcomplete hcart hproper hflat haff ha_over ha_xt in

theorem univ_loc_Spec
    (hP : ∀ n : ℕ, (Function.Surjective (p' n).base ∧ IsClosedMap (p' n).base ∧
      (∀ x x' : X' n, (p' n).base x = (p' n).base x' → ∃ g : G, (a' n g).hom.base x = x') ∧
      (∀ O : (X' n).Opens, (∀ g : G, (a' n g).hom ⁻¹ᵁ O = O) → ∃ U' : (Y' n).Opens, (p' n) ⁻¹ᵁ U' = O)))
    (hchart : ∀ (V : ∀ n : ℕ, (D.Y n).Opens) (hVa : ∀ n : ℕ, IsAffineOpen (V n))
      (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n),
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra 𝒪 R) (_ : MulSemiringAction G R) (_ : SMulCommClass G 𝒪 R),
      IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R ∧
      (∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0) ∧
      Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}) ∧
      ∃ (lvl : ∀ n : ℕ, (R ⧸ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) ≃+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)))
        (μ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 R G) ⧸
          Ideal.span {algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π ^ (n + 1)}) ≃+* Γ(D.Y n, V n)),
        (∀ (n : ℕ) (x : R), (xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((D.p n) ⁻¹ᵁ (V n))
            (by rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hV])
            (lvl (n + 1) (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ x)) ∧
        (∀ (n : ℕ) (g : G) (x : R), (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n))
            (by rw [← Scheme.Hom.comp_preimage, D.p_inv]) (lvl n (Ideal.Quotient.mk _ x)) =
            lvl n (Ideal.Quotient.mk _ (g • x))) ∧
        (∀ (n : ℕ) (o : 𝒪), lvl n (Ideal.Quotient.mk _ (algebraMap 𝒪 R o)) =
            (xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top
              ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) ∧
        (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.yt n).appLE (V (n + 1)) (V n) (by rw [hV])
            (μ (n + 1) (Ideal.Quotient.mk _ x)) = μ n (Ideal.Quotient.mk _ x)) ∧
        (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.p n).appLE (V n) ((D.p n) ⁻¹ᵁ (V n)) le_rfl
            (μ n (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ (x : R))) ∧
        (∀ (n : ℕ) (o : 𝒪), μ n (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o)) =
            (D.yb n).appLE ⊤ (V n) le_top
              ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) ∧
        ∀ (b : ↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S),
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
                ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))))
    (B : CommRingCat.{0})
    (U : ∀ n : ℕ, (Y' n).Opens) (hU : ∀ n : ℕ, (yt' n) ⁻¹ᵁ (U (n + 1)) = U n)
    (u : ∀ n : ℕ, (↑((p' n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ Spec B)
    (hug : ∀ (n : ℕ) (g : G),
      Scheme.Hom.resLE (a' n g).hom ((p' n) ⁻¹ᵁ (U n)) ((p' n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) ≫ u n = u n)
    (hut : ∀ n : ℕ,
      Scheme.Hom.resLE (xt' n) ((p' (n + 1)) ⁻¹ᵁ (U (n + 1))) ((p' n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hU]) ≫ u (n + 1) = u n) :
    ∃ v : ∀ n : ℕ, (↑(U n) : Scheme.{0}) ⟶ Spec B, ∀ n : ℕ, (p' n) ∣_ (U n) ≫ v n = u n := by
  classical
  have hsurj : ∀ n : ℕ, Function.Surjective (p' n).base := fun n => (hP n).1
  have hyt' := surjective_yt' 𝒪 π S X' xb' xt' hcart' Y' yt' p' hp'_xt hsurj
  have hepi : ∀ (n : ℕ) (O : (Y' n).Opens), Epi ((p' n) ∣_ O) := by
    intro n O
    haveI := D.p_isFinite n
    haveI : Surjective (D.p n) := D.p_surjective n
    haveI : Flat (r n) := MorphismProperty.of_isPullback (P := @Flat) (hbase n).flip
      (AlgebraicGeometry.flat_specMap_quotientMap_pow_of_flat 𝒪 π S n)
    exact AlgebraicGeometry.epi_morphismRestrict_of_isPullback_of_flat (D.p n) (r n) (p' n) (q n) (hsq n)
      (D.p_epi_loc n) O

  have hloc : ∀ (n : ℕ) (y : Y' n), y ∈ U n → ∃ (W : (Y' n).Opens) (hWU : W ≤ U n), y ∈ W ∧
      ∃ v : (↑W : Scheme.{0}) ⟶ Spec B, (p' n) ∣_ W ≫ v = (X' n).homOfLE ((p' n).preimage_mono hWU) ≫ u n := by
    intro n y hy
    obtain ⟨V, hVa, hV, hyV⟩ := exists_affine_family 𝒪 π hπ X xb xt G a D n ((r n).base y)
    obtain ⟨R, _, _, _, _, hRc, hRtf, hRft, lvl, μ, hl1, hl2, hl3, hm1, hm2, hm3, hrest⟩ := hchart V hVa hV
    haveI : IsAffineHom (r n) := MorphismProperty.of_isPullback (P := @IsAffineHom) (hbase n).flip inferInstance
    have hrV : IsAffineOpen ((r n) ⁻¹ᵁ (V n)) := (hVa n).preimage (r n)
    obtain ⟨f, hfU, hyf⟩ := hrV.exists_basicOpen_le ⟨y, hy⟩ hyV
    obtain ⟨φ₀, hφ₀, hφ₀s, -⟩ := hrest 0
    obtain ⟨c, hc⟩ := hφ₀s n f
    obtain ⟨φ, hφ, hφs, hV', R', _, _, _, _, hR'c, hR'tf, hA'c, lvl', μ', m1, m2, m3, m4, m5, m6⟩ := hrest c
    have hφφ : ∀ x, φ n x = φ₀ n x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x s => rw [hφ, hφ₀]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    have hc' : φ n c = f := by rw [hφφ, hc]

    have hle_iff : ∀ k : ℕ, (Y' k).basicOpen (φ k c) ≤ U k ↔ (Y' (k + 1)).basicOpen (φ (k + 1) c) ≤ U (k + 1) := by
      intro k
      constructor
      · intro h z hz
        obtain ⟨z', rfl⟩ := hyt' k z
        have hz' : z' ∈ (yt' k) ⁻¹ᵁ (Y' (k + 1)).basicOpen (φ (k + 1) c) := hz
        rw [hV'] at hz'
        have := h hz'
        rw [← hU] at this
        exact this
      · intro h
        rw [← hV', ← hU]
        exact (yt' k).preimage_mono h
    have key : ∀ k : ℕ, ((Y' k).basicOpen (φ k c) ≤ U k ↔ (Y' 0).basicOpen (φ 0 c) ≤ U 0) := by
      intro k
      induction k with
      | zero => exact Iff.rfl
      | succ k ih => exact (hle_iff k).symm.trans ih
    have hn : (Y' n).basicOpen (φ n c) ≤ U n := by rw [hc']; exact hfU
    have hall : ∀ m : ℕ, (Y' m).basicOpen (φ m c) ≤ U m := fun m => (key m).2 ((key n).1 hn)
    have hW : ∀ m : ℕ, (p' m) ⁻¹ᵁ ((Y' m).basicOpen (φ m c)) ≤ (p' m) ⁻¹ᵁ (U m) := fun m => (p' m).preimage_mono (hall m)

    let w : ∀ m : ℕ, (↑((p' m) ⁻¹ᵁ ((Y' m).basicOpen (φ m c))) : Scheme.{0}) ⟶ Spec B := fun m => (X' m).homOfLE (hW m) ≫ u m
    have hwg : ∀ (m : ℕ) (g : G), (a' m g).hom.resLE ((p' m) ⁻¹ᵁ ((Y' m).basicOpen (φ m c))) ((p' m) ⁻¹ᵁ ((Y' m).basicOpen (φ m c)))
        (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) ≫ w m = w m := by
      intro m g
      have e1 : (a' m g).hom.resLE ((p' m) ⁻¹ᵁ ((Y' m).basicOpen (φ m c))) ((p' m) ⁻¹ᵁ ((Y' m).basicOpen (φ m c)))
          (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) ≫ (X' m).homOfLE (hW m) =
          (X' m).homOfLE (hW m) ≫ (a' m g).hom.resLE ((p' m) ⁻¹ᵁ (U m)) ((p' m) ⁻¹ᵁ (U m))
            (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) := by
        simp [← cancel_mono (Scheme.Opens.ι _)]
      simp only [w]
      rw [← Category.assoc, e1, Category.assoc, hug]
    have hwt : ∀ m : ℕ, (xt' m).resLE ((p' (m + 1)) ⁻¹ᵁ ((Y' (m + 1)).basicOpen (φ (m + 1) c))) ((p' m) ⁻¹ᵁ ((Y' m).basicOpen (φ m c)))
        (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hV']) ≫ w (m + 1) = w m := by
      intro m
      have e1 : (xt' m).resLE ((p' (m + 1)) ⁻¹ᵁ ((Y' (m + 1)).basicOpen (φ (m + 1) c))) ((p' m) ⁻¹ᵁ ((Y' m).basicOpen (φ m c)))
          (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hV']) ≫ (X' (m + 1)).homOfLE (hW (m + 1)) =
          (X' m).homOfLE (hW m) ≫ (xt' m).resLE ((p' (m + 1)) ⁻¹ᵁ (U (m + 1))) ((p' m) ⁻¹ᵁ (U m))
            (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hU]) := by
        simp [← cancel_mono (Scheme.Opens.ι _)]
      simp only [w]
      rw [← Category.assoc, e1, Category.assoc, hut]
    obtain ⟨v, hv⟩ := univ_chart (algebraMap 𝒪 S π) p' xt' yt' a' hp'_inv hp'_xt (fun m => (Y' m).basicOpen (φ m c)) hV'
      R' hR'c lvl' μ' m1 m2 m5 B w hwg hwt
    exact ⟨(Y' n).basicOpen (φ n c), hall n, by rw [hc']; exact hyf, v n, hv n⟩
  have hglue := fun n => glue_local (p' n) (hepi n) (U n) (u n) (hloc n)
  choose vn hvn using hglue
  exact ⟨vn, hvn⟩

end Global2

theorem preimage_eq_of_inf_eq {Z Z' : Scheme.{0}} (q : Z ⟶ Z') (W : Z.Opens) (W' : Z'.Opens) (D : Z.Opens) (D' : Z'.Opens)
    (hW : q ⁻¹ᵁ W' = W) (hD' : D' ≤ W') (h : W ⊓ q ⁻¹ᵁ D' = D) : q ⁻¹ᵁ D' = D := by
  rw [← h]
  refine (inf_eq_right.2 ?_).symm
  rw [← hW]
  exact q.preimage_mono hD'

section Global3

variable
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

include hcart' hp'_xt hp'_inv hπ hbase hsq in
omit hdvr hcomplete hcart hproper hflat haff ha_over ha_xt in

theorem univ_loc_affine
    (hP : ∀ n : ℕ, (Function.Surjective (p' n).base ∧ IsClosedMap (p' n).base ∧
      (∀ x x' : X' n, (p' n).base x = (p' n).base x' → ∃ g : G, (a' n g).hom.base x = x') ∧
      (∀ O : (X' n).Opens, (∀ g : G, (a' n g).hom ⁻¹ᵁ O = O) → ∃ U' : (Y' n).Opens, (p' n) ⁻¹ᵁ U' = O)))
    (hchart : ∀ (V : ∀ n : ℕ, (D.Y n).Opens) (hVa : ∀ n : ℕ, IsAffineOpen (V n))
      (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n),
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra 𝒪 R) (_ : MulSemiringAction G R) (_ : SMulCommClass G 𝒪 R),
      IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R ∧
      (∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0) ∧
      Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}) ∧
      ∃ (lvl : ∀ n : ℕ, (R ⧸ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) ≃+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)))
        (μ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 R G) ⧸
          Ideal.span {algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π ^ (n + 1)}) ≃+* Γ(D.Y n, V n)),
        (∀ (n : ℕ) (x : R), (xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((D.p n) ⁻¹ᵁ (V n))
            (by rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hV])
            (lvl (n + 1) (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ x)) ∧
        (∀ (n : ℕ) (g : G) (x : R), (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n))
            (by rw [← Scheme.Hom.comp_preimage, D.p_inv]) (lvl n (Ideal.Quotient.mk _ x)) =
            lvl n (Ideal.Quotient.mk _ (g • x))) ∧
        (∀ (n : ℕ) (o : 𝒪), lvl n (Ideal.Quotient.mk _ (algebraMap 𝒪 R o)) =
            (xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top
              ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) ∧
        (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.yt n).appLE (V (n + 1)) (V n) (by rw [hV])
            (μ (n + 1) (Ideal.Quotient.mk _ x)) = μ n (Ideal.Quotient.mk _ x)) ∧
        (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.p n).appLE (V n) ((D.p n) ⁻¹ᵁ (V n)) le_rfl
            (μ n (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ (x : R))) ∧
        (∀ (n : ℕ) (o : 𝒪), μ n (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o)) =
            (D.yb n).appLE ⊤ (V n) le_top
              ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) ∧
        ∀ (b : ↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S),
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
                ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))))
    (T : Scheme.{0}) [IsAffine T]
    (U : ∀ n : ℕ, (Y' n).Opens) (hU : ∀ n : ℕ, (yt' n) ⁻¹ᵁ (U (n + 1)) = U n)
    (u : ∀ n : ℕ, (↑((p' n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T)
    (hug : ∀ (n : ℕ) (g : G),
      Scheme.Hom.resLE (a' n g).hom ((p' n) ⁻¹ᵁ (U n)) ((p' n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) ≫ u n = u n)
    (hut : ∀ n : ℕ,
      Scheme.Hom.resLE (xt' n) ((p' (n + 1)) ⁻¹ᵁ (U (n + 1))) ((p' n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hU]) ≫ u (n + 1) = u n) :
    ∃ v : ∀ n : ℕ, (↑(U n) : Scheme.{0}) ⟶ T, ∀ n : ℕ, (p' n) ∣_ (U n) ≫ v n = u n := by
  obtain ⟨v, hv⟩ := univ_loc_Spec 𝒪 π hπ X xb xt G a D S X' xb' xt' a' q hcart' Y' yb' yt' p' r hbase hsq hp'_inv hp'_xt
    hP hchart Γ(T, ⊤) U hU (fun n => u n ≫ T.isoSpec.hom)
    (fun n g => by rw [← Category.assoc, hug]) (fun n => by rw [← Category.assoc, hut])
  exact ⟨fun n => v n ≫ T.isoSpec.inv, fun n => by
    rw [← Category.assoc, hv, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩

include hcart' hp'_xt hp'_inv hπ hbase hsq in
omit hdvr hcomplete hcart hproper hflat haff ha_over ha_xt in

theorem univ_loc
    (hP : ∀ n : ℕ, (Function.Surjective (p' n).base ∧ IsClosedMap (p' n).base ∧
      (∀ x x' : X' n, (p' n).base x = (p' n).base x' → ∃ g : G, (a' n g).hom.base x = x') ∧
      (∀ O : (X' n).Opens, (∀ g : G, (a' n g).hom ⁻¹ᵁ O = O) → ∃ U' : (Y' n).Opens, (p' n) ⁻¹ᵁ U' = O)))
    (hchart : ∀ (V : ∀ n : ℕ, (D.Y n).Opens) (hVa : ∀ n : ℕ, IsAffineOpen (V n))
      (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n),
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra 𝒪 R) (_ : MulSemiringAction G R) (_ : SMulCommClass G 𝒪 R),
      IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R ∧
      (∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0) ∧
      Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}) ∧
      ∃ (lvl : ∀ n : ℕ, (R ⧸ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) ≃+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)))
        (μ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 R G) ⧸
          Ideal.span {algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π ^ (n + 1)}) ≃+* Γ(D.Y n, V n)),
        (∀ (n : ℕ) (x : R), (xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((D.p n) ⁻¹ᵁ (V n))
            (by rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hV])
            (lvl (n + 1) (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ x)) ∧
        (∀ (n : ℕ) (g : G) (x : R), (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n))
            (by rw [← Scheme.Hom.comp_preimage, D.p_inv]) (lvl n (Ideal.Quotient.mk _ x)) =
            lvl n (Ideal.Quotient.mk _ (g • x))) ∧
        (∀ (n : ℕ) (o : 𝒪), lvl n (Ideal.Quotient.mk _ (algebraMap 𝒪 R o)) =
            (xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top
              ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) ∧
        (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.yt n).appLE (V (n + 1)) (V n) (by rw [hV])
            (μ (n + 1) (Ideal.Quotient.mk _ x)) = μ n (Ideal.Quotient.mk _ x)) ∧
        (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.p n).appLE (V n) ((D.p n) ⁻¹ᵁ (V n)) le_rfl
            (μ n (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ (x : R))) ∧
        (∀ (n : ℕ) (o : 𝒪), μ n (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o)) =
            (D.yb n).appLE ⊤ (V n) le_top
              ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) ∧
        ∀ (b : ↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S),
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
                ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))) :
    ∀ (T : Scheme.{0}) (U : ∀ n : ℕ, (Y' n).Opens) (hU : ∀ n : ℕ, (yt' n) ⁻¹ᵁ (U (n + 1)) = U n)
      (u : ∀ n : ℕ, (↑((p' n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T),
      (∀ (n : ℕ) (g : G),
        Scheme.Hom.resLE (a' n g).hom ((p' n) ⁻¹ᵁ (U n)) ((p' n) ⁻¹ᵁ (U n))
          (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) ≫ u n = u n) →
      (∀ n : ℕ,
        Scheme.Hom.resLE (xt' n) ((p' (n + 1)) ⁻¹ᵁ (U (n + 1))) ((p' n) ⁻¹ᵁ (U n))
          (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hU]) ≫ u (n + 1) = u n) →
      ∃ v : ∀ n : ℕ, (↑(U n) : Scheme.{0}) ⟶ T, ∀ n : ℕ, (p' n) ∣_ (U n) ≫ v n = u n := by
  intro T U hU u hug hut
  classical
  have hsurj : ∀ n : ℕ, Function.Surjective (p' n).base := fun n => (hP n).1
  have hstab : ∀ (n : ℕ) (O : (X' n).Opens), (∀ g : G, (a' n g).hom ⁻¹ᵁ O = O) →
      ∃ U' : (Y' n).Opens, (p' n) ⁻¹ᵁ U' = O := fun n => (hP n).2.2.2
  have hepi : ∀ (n : ℕ) (O : (Y' n).Opens), Epi ((p' n) ∣_ O) := by
    intro n O
    haveI := D.p_isFinite n
    haveI : Surjective (D.p n) := D.p_surjective n
    haveI : Flat (r n) := MorphismProperty.of_isPullback (P := @Flat) (hbase n).flip
      (AlgebraicGeometry.flat_specMap_quotientMap_pow_of_flat 𝒪 π S n)
    exact AlgebraicGeometry.epi_morphismRestrict_of_isPullback_of_flat (D.p n) (r n) (p' n) (q n) (hsq n)
      (D.p_epi_loc n) O
  have le_of_preimage_le : ∀ (n : ℕ) (A B : (Y' n).Opens), (p' n) ⁻¹ᵁ A ≤ (p' n) ⁻¹ᵁ B → A ≤ B := by
    intro n A B h y hy
    obtain ⟨x, rfl⟩ := hsurj n y
    exact h hy
  have eq_of_preimage_eq : ∀ (n : ℕ) (A B : (Y' n).Opens), (p' n) ⁻¹ᵁ A = (p' n) ⁻¹ᵁ B → A = B := fun n A B h =>
    le_antisymm (le_of_preimage_le n A B h.le) (le_of_preimage_le n B A h.ge)
  let J : Type := T.affineOpens

  let O : J → ∀ n : ℕ, (X' n).Opens := fun j n => ((p' n) ⁻¹ᵁ (U n)).ι ''ᵁ ((u n) ⁻¹ᵁ (j : T.Opens))
  have hOle : ∀ (j : J) (n : ℕ), O j n ≤ (p' n) ⁻¹ᵁ (U n) := fun j n => Scheme.Opens.ι_image_le _ _

  have hOg : ∀ (j : J) (n : ℕ) (g : G), (a' n g).hom ⁻¹ᵁ (O j n) = O j n := by
    intro j n g
    have hpre : (a' n g).hom ⁻¹ᵁ ((p' n) ⁻¹ᵁ (U n)) = (p' n) ⁻¹ᵁ (U n) := by
      rw [← Scheme.Hom.comp_preimage, hp'_inv]
    apply preimage_eq_of_inf_eq (a' n g).hom _ _ _ _ hpre (hOle j n)
    have := congrArg (fun W => ((p' n) ⁻¹ᵁ (U n)).ι ''ᵁ W)
      (congrArg (fun f : (↑((p' n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T => f ⁻¹ᵁ (j : T.Opens)) (hug n g))
    simp only [Scheme.Hom.comp_preimage, Scheme.Hom.resLE_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι] at this
    exact this

  have hOt : ∀ (j : J) (n : ℕ), (xt' n) ⁻¹ᵁ (O j (n + 1)) = O j n := by
    intro j n
    have hpre : (xt' n) ⁻¹ᵁ ((p' (n + 1)) ⁻¹ᵁ (U (n + 1))) = (p' n) ⁻¹ᵁ (U n) := by
      rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hU]
    apply preimage_eq_of_inf_eq (xt' n) _ _ _ _ hpre (hOle j (n + 1))
    have := congrArg (fun W => ((p' n) ⁻¹ᵁ (U n)).ι ''ᵁ W)
      (congrArg (fun f : (↑((p' n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T => f ⁻¹ᵁ (j : T.Opens)) (hut n))
    simp only [Scheme.Hom.comp_preimage, Scheme.Hom.resLE_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι] at this
    exact this

  have hdesc := fun (j : J) (n : ℕ) => hstab n (O j n) (hOg j n)
  choose U' hU' using hdesc
  have hU'le : ∀ (j : J) (n : ℕ), U' j n ≤ U n := fun j n =>
    le_of_preimage_le n _ _ (by rw [hU']; exact hOle j n)
  have hU'c : ∀ (j : J) (n : ℕ), (yt' n) ⁻¹ᵁ (U' j (n + 1)) = U' j n := by
    intro j n
    apply eq_of_preimage_eq n
    rw [← Scheme.Hom.comp_preimage, ← hp'_xt, Scheme.Hom.comp_preimage, hU', hOt, hU']
  have hle' : ∀ (j : J) (n : ℕ), (p' n) ⁻¹ᵁ (U' j n) ≤ (p' n) ⁻¹ᵁ (U n) := fun j n =>
    (p' n).preimage_mono (hU'le j n)

  have hrange : ∀ (j : J) (n : ℕ),
      Set.range ((X' n).homOfLE (hle' j n) ≫ u n).base ⊆ Set.range (j : T.Opens).ι.base := by
    rintro j n _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : z.1 ∈ O j n := by rw [← hU']; exact z.2
    obtain ⟨w, hw, hwz⟩ := hz
    have : (X' n).homOfLE (hle' j n) z = w := Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hwz.symm)
    show u n ((X' n).homOfLE (hle' j n) z) ∈ (j : T.Opens)
    rw [this]
    exact hw
  let u' : ∀ (j : J) (n : ℕ), (↑((p' n) ⁻¹ᵁ (U' j n)) : Scheme.{0}) ⟶ ↑(j : T.Opens) := fun j n =>
    IsOpenImmersion.lift (j : T.Opens).ι ((X' n).homOfLE (hle' j n) ≫ u n) (hrange j n)
  have hu' : ∀ (j : J) (n : ℕ), u' j n ≫ (j : T.Opens).ι = (X' n).homOfLE (hle' j n) ≫ u n := fun j n =>
    IsOpenImmersion.lift_fac _ _ _
  have hug' : ∀ (j : J) (n : ℕ) (g : G),
      Scheme.Hom.resLE (a' n g).hom ((p' n) ⁻¹ᵁ (U' j n)) ((p' n) ⁻¹ᵁ (U' j n))
        (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) ≫ u' j n = u' j n := by
    intro j n g
    rw [← cancel_mono (j : T.Opens).ι, Category.assoc, hu']
    have e1 : Scheme.Hom.resLE (a' n g).hom ((p' n) ⁻¹ᵁ (U' j n)) ((p' n) ⁻¹ᵁ (U' j n))
        (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) ≫ (X' n).homOfLE (hle' j n) =
        (X' n).homOfLE (hle' j n) ≫ Scheme.Hom.resLE (a' n g).hom ((p' n) ⁻¹ᵁ (U n)) ((p' n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) := by
      simp [← cancel_mono (Scheme.Opens.ι _)]
    rw [← Category.assoc, e1, Category.assoc, hug]
  have hut' : ∀ (j : J) (n : ℕ),
      Scheme.Hom.resLE (xt' n) ((p' (n + 1)) ⁻¹ᵁ (U' j (n + 1))) ((p' n) ⁻¹ᵁ (U' j n))
        (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hU'c]) ≫ u' j (n + 1) = u' j n := by
    intro j n
    rw [← cancel_mono (j : T.Opens).ι, Category.assoc, hu', hu']
    have e1 : Scheme.Hom.resLE (xt' n) ((p' (n + 1)) ⁻¹ᵁ (U' j (n + 1))) ((p' n) ⁻¹ᵁ (U' j n))
        (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hU'c]) ≫ (X' (n + 1)).homOfLE (hle' j (n + 1)) =
        (X' n).homOfLE (hle' j n) ≫ Scheme.Hom.resLE (xt' n) ((p' (n + 1)) ⁻¹ᵁ (U (n + 1))) ((p' n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hU]) := by
      simp [← cancel_mono (Scheme.Opens.ι _)]
    rw [← Category.assoc, e1, Category.assoc, hut]

  have hv' := fun j : J => by
    haveI : IsAffine (↑(j : T.Opens) : Scheme.{0}) := j.2
    exact univ_loc_affine 𝒪 π hπ X xb xt G a D S X' xb' xt' a' q hcart' Y' yb' yt' p' r hbase hsq hp'_inv hp'_xt
      hP hchart (↑(j : T.Opens)) (U' j) (hU'c j) (u' j) (hug' j) (hut' j)
  choose v' hv' using hv'

  have hloc : ∀ (n : ℕ) (y : Y' n), y ∈ U n → ∃ (W : (Y' n).Opens) (hWU : W ≤ U n), y ∈ W ∧
      ∃ v : (↑W : Scheme.{0}) ⟶ T, (p' n) ∣_ W ≫ v = (X' n).homOfLE ((p' n).preimage_mono hWU) ≫ u n := by
    intro n y hy
    obtain ⟨x, rfl⟩ := hsurj n y
    have ht : u n ⟨x, hy⟩ ∈ (⊤ : T.Opens) := trivial
    rw [← iSup_affineOpens_eq_top, TopologicalSpace.Opens.mem_iSup] at ht
    obtain ⟨j, hj⟩ := ht
    refine ⟨U' j n, hU'le j n, ?_, v' j n ≫ (j : T.Opens).ι, by rw [← Category.assoc, hv', hu']⟩
    show x ∈ (p' n) ⁻¹ᵁ (U' j n)
    rw [hU']
    exact ⟨⟨x, hy⟩, hj, rfl⟩
  have hglue := fun n => glue_local (p' n) (hepi n) (U n) (u n) (hloc n)
  choose v hv using hglue
  exact ⟨v, hv⟩

end Global3

end W2GEO

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
    (hP : ∀ n : ℕ, (Function.Surjective (p' n).base ∧ IsClosedMap (p' n).base ∧
      (∀ x x' : X' n, (p' n).base x = (p' n).base x' → ∃ g : G, (a' n g).hom.base x = x') ∧
      (∀ O : (X' n).Opens, (∀ g : G, (a' n g).hom ⁻¹ᵁ O = O) → ∃ U' : (Y' n).Opens, (p' n) ⁻¹ᵁ U' = O)))
    (hchart : ∀ (V : ∀ n : ℕ, (D.Y n).Opens) (hVa : ∀ n : ℕ, IsAffineOpen (V n))
      (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n),
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra 𝒪 R) (_ : MulSemiringAction G R) (_ : SMulCommClass G 𝒪 R),
      IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R ∧
      (∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0) ∧
      Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}) ∧
      ∃ (lvl : ∀ n : ℕ, (R ⧸ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) ≃+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)))
        (μ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 R G) ⧸
          Ideal.span {algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π ^ (n + 1)}) ≃+* Γ(D.Y n, V n)),
        (∀ (n : ℕ) (x : R), (xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((D.p n) ⁻¹ᵁ (V n))
            (by rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hV])
            (lvl (n + 1) (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ x)) ∧
        (∀ (n : ℕ) (g : G) (x : R), (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n))
            (by rw [← Scheme.Hom.comp_preimage, D.p_inv]) (lvl n (Ideal.Quotient.mk _ x)) =
            lvl n (Ideal.Quotient.mk _ (g • x))) ∧
        (∀ (n : ℕ) (o : 𝒪), lvl n (Ideal.Quotient.mk _ (algebraMap 𝒪 R o)) =
            (xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top
              ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) ∧
        (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.yt n).appLE (V (n + 1)) (V n) (by rw [hV])
            (μ (n + 1) (Ideal.Quotient.mk _ x)) = μ n (Ideal.Quotient.mk _ x)) ∧
        (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.p n).appLE (V n) ((D.p n) ⁻¹ᵁ (V n)) le_rfl
            (μ n (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ (x : R))) ∧
        (∀ (n : ℕ) (o : 𝒪), μ n (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o)) =
            (D.yb n).appLE ⊤ (V n) le_top
              ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) ∧
        ∀ (b : ↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S),
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
                ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))) :
    ∀ (T : Scheme.{0}) (U : ∀ n : ℕ, (Y' n).Opens) (hU : ∀ n : ℕ, (yt' n) ⁻¹ᵁ (U (n + 1)) = U n)
      (u : ∀ n : ℕ, (↑((p' n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T),
      (∀ (n : ℕ) (g : G),
        Scheme.Hom.resLE (a' n g).hom ((p' n) ⁻¹ᵁ (U n)) ((p' n) ⁻¹ᵁ (U n))
          (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) ≫ u n = u n) →
      (∀ n : ℕ,
        Scheme.Hom.resLE (xt' n) ((p' (n + 1)) ⁻¹ᵁ (U (n + 1))) ((p' n) ⁻¹ᵁ (U n))
          (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hU]) ≫ u (n + 1) = u n) →
      ∃ v : ∀ n : ℕ, (↑(U n) : Scheme.{0}) ⟶ T, ∀ n : ℕ, (p' n) ∣_ (U n) ≫ v n = u n :=
  W2GEO.univ_loc 𝒪 π hπ X xb xt G a D S X' xb' xt' a' q hcart' Y' yb' yt' p' r hbase hsq hp'_inv hp'_xt hP hchart

end S_AlgebraicGeometry_TowerQuotientDatum_univ_loc_of_isPullback_of_flat_of_forall_exists_chart
end P2MW
export P2MW.S_AlgebraicGeometry_TowerQuotientDatum_univ_loc_of_isPullback_of_flat_of_forall_exists_chart (solution)
