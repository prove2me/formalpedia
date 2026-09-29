-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_isAlgClosed_typePoints_thetaPt_of_idempotent_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/9ba791be-2885-5437-aaef-3aec7725ef68

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_monoidHom_pt_comp_eq_act_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_ofScalar_act
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_mul_act
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaPt_eq_of_pt_eq_of_forall_act_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isAlgClosed_typePoints_thetaPt_of_idempotent_ne_zero
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

namespace N1Aux

theorem exists_isAlgClosed_ringHom_map_eq_one_of_isIdempotentElem
    {R : Type} [CommRing R] (ε : R) (hε : IsIdempotentElem ε) (hε0 : ε ≠ 0) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (φ : R →+* k), φ ε = 1 := by
  classical

  have hnn : ¬ IsNilpotent ε := by
    rintro ⟨n, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [pow_zero] at hn; exact hε0 (by rw [← one_mul ε, hn, zero_mul])
    · apply hε0
      have : ε ^ n = ε := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        exact hε.pow_succ_eq m
      rw [← this, hn]
  have : ∃ 𝔭 : Ideal R, 𝔭.IsPrime ∧ ε ∉ 𝔭 := by
    by_contra h
    push Not at h
    apply hnn
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro J hJ
    exact h J hJ
  obtain ⟨𝔭, h𝔭, hε𝔭⟩ := this
  haveI := h𝔭
  let k : Type := AlgebraicClosure (FractionRing (R ⧸ 𝔭))
  let g : R ⧸ 𝔭 →+* k := (algebraMap (FractionRing (R ⧸ 𝔭)) k).comp (algebraMap (R ⧸ 𝔭) (FractionRing (R ⧸ 𝔭)))
  have hg : Function.Injective g :=
    (algebraMap (FractionRing (R ⧸ 𝔭)) k).injective.comp (IsFractionRing.injective (R ⧸ 𝔭) (FractionRing (R ⧸ 𝔭)))
  refine ⟨k, inferInstance, inferInstance, g.comp (Ideal.Quotient.mk 𝔭), ?_⟩
  have hne : (g.comp (Ideal.Quotient.mk 𝔭)) ε ≠ 0 := by
    rw [RingHom.comp_apply, map_ne_zero_iff g hg, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hε𝔭
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (hε.map (g.comp (Ideal.Quotient.mk 𝔭))) with h | h
  · exact absurd h hne
  · exact h

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) (P' Q' : SchemeHomOver t₂ f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t₁ P Q).1 = (L.mul t₂ P' Q').1 := by
  subst h
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

end N1Aux

open N1Aux in
theorem solution
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] [NeZero d] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] [Algebra S R]
    (ζ : R) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (x : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S R))) u.f)
    (hx0 : x 0 = u.L.one _) (hx : ∀ h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), x (h + h') = u.L.mul _ (x h) (x h'))
    (hxinj : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k) (h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))),
      Spec.map (CommRingCat.ofHom sk) ≫ (x h).1 = Spec.map (CommRingCat.ofHom sk) ≫ (x h').1 → h = h')
    (hxK : ∀ (R'' : Type) [CommRing R''] [Algebra R R'']
      (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap R R'').comp (algebraMap S R)))) u.f),
      Polarisation.MemKernel u.f u.L u.pol _ y ↔
        ∃ (m : ℕ) (r : Fin m → R''), Ideal.span (Set.range r) = ⊤ ∧ ∀ j, ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))),
          Spec.map (CommRingCat.ofHom (algebraMap R'' (Localization.Away (r j)))) ≫ y.1 =
            Spec.map (CommRingCat.ofHom ((algebraMap R'' (Localization.Away (r j))).comp (algebraMap R R''))) ≫ (x h).1)
    (θ₀ : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap S R)))) (hθ₀ : ∀ k, (θ₀ k).pt = x k)
    (e : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → Rˣ)
    (he : ∀ (k k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))).obj u.pol, ⊤)),
      (θ₀ k).act ((θ₀ k').act s) = baseScalar u.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) (e k k' : R) • (θ₀ k').act ((θ₀ k).act s))
    (ε : ((((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d) → R) (hε : CompleteOrthogonalIdempotents ε)
    (hεe : ∀ (B : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d) (k k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))), ε B * (e k k' : R) = ε B * ζ ^ (B k k').val)
    (B : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ZMod d) (hB : ε B ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (φ : R →+* K), φ (ε B) = 1 ∧
      ∃ (xK : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))) u.f)
        (θK : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R))))),
        (∀ h, (xK h).1 = Spec.map (CommRingCat.ofHom φ) ≫ (x h).1) ∧
        xK 0 = u.L.one _ ∧ (∀ h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), xK (h + h') = u.L.mul _ (xK h) (xK h')) ∧
        Function.Injective xK ∧
        (∀ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))) u.f, Polarisation.MemKernel u.f u.L u.pol _ y → ∃ h, y = xK h) ∧
        (∀ h, (θK h).pt = xK h) ∧
        (∀ (k k' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))))).obj u.pol, ⊤)),
          (θK k).act ((θK k').act s) =
            baseScalar u.f (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))) (φ ζ ^ (B k k').val) • (θK k').act ((θK k).act s)) := by
  classical

  obtain ⟨K, _, _, φ, hφ⟩ := exists_isAlgClosed_ringHom_map_eq_one_of_isIdempotentElem (ε B) (hε.idem B) hB
  refine ⟨K, inferInstance, inferInstance, φ, hφ, ?_⟩

  have hr : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap S R)) =
      Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  let xK : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) →
      SchemeHomOver (Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))) u.f :=
    fun h => schemeHomOverComp (Spec.map (CommRingCat.ofHom φ)) hr (x h)

  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by rw [CommRingCat.ofHom_id, Spec.map_id]
  haveI : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by rw [hid]; infer_instance
  have hg : IsPullback (𝟙 u.A) u.f u.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) :=
    IsPullback.of_horiz_isIso ⟨by rw [hid, Category.id_comp, Category.comp_id]⟩
  have hmul : ∀ {T : Scheme.{0}} (t'' : T ⟶ Spec (CommRingCat.of S)) (a b : SchemeHomOver t'' u.f),
      (u.L.mul t'' a b).1 ≫ 𝟙 u.A =
        (u.L.mul (t'' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)))
          ⟨a.1 ≫ 𝟙 u.A, by rw [Category.assoc, hg.w, ← Category.assoc, a.2]⟩
          ⟨b.1 ≫ 𝟙 u.A, by rw [Category.assoc, hg.w, ← Category.assoc, b.2]⟩).1 := by
    intro T t'' a b
    rw [Category.comp_id]
    exact mul_val_congr u.L (by rw [hid, Category.comp_id]) a b _ _ (Category.comp_id _).symm (Category.comp_id _).symm
  let t := Spec.map (CommRingCat.ofHom (algebraMap S R))
  let t' := Spec.map (CommRingCat.ofHom (φ.comp (algebraMap S R)))
  have hr' : Spec.map (CommRingCat.ofHom φ) ≫ t = t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)) := by
    rw [hid, Category.comp_id]; exact hr
  let b : pullback u.f t' ⟶ pullback u.f t :=
    pullback.lift (pullback.fst u.f t') (pullback.snd u.f t' ≫ Spec.map (CommRingCat.ofHom φ))
      (by rw [pullback.condition, Category.assoc, hr])
  have hb₁ : b ≫ pullback.fst u.f t = pullback.fst u.f t' ≫ 𝟙 u.A := by rw [pullback.lift_fst, Category.comp_id]
  have hb₂ : b ≫ pullback.snd u.f t = pullback.snd u.f t' ≫ Spec.map (CommRingCat.ofHom φ) := pullback.lift_snd _ _ _
  let c : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol) ≅
      (Scheme.Modules.pullback (pullback.fst u.f t')).obj u.pol :=
    (Scheme.Modules.pullbackComp b (pullback.fst u.f t)).app u.pol ≪≫
      (Scheme.Modules.pullbackCongr (show b ≫ pullback.fst u.f t = pullback.fst u.f t' from pullback.lift_fst _ _ _)).app u.pol
  obtain ⟨β, hβpt, hβact, hβsc, -⟩ :=
    AlgebraicGeometry.Polarisation.ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback (RingHom.id S) u.L u.L (𝟙 u.A) hg
      hmul u.pol u.pol t t' φ hr' b hb₁ hb₂ c
  let θK : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol t' := fun h => β (θ₀ h)

  have hgrp : ∀ k k', θ₀ k * θ₀ k' = ThetaPt.ofScalar (e k k') * (θ₀ k' * θ₀ k) := by
    intro k k'
    apply AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_eq_of_pt_eq_of_forall_act_eq u
    · simp only [ThetaPt.mul_pt, ThetaPt.ofScalar_pt, u.L.one_mul, hθ₀, ← hx, add_comm]
    · intro s
      rw [ThetaPt.mul_act, ThetaPt.mul_act, ThetaPt.mul_act, ThetaPt.ofScalar_act, he]
  have hφe : ∀ k k', φ (e k k' : R) = φ ζ ^ (B k k').val := by
    intro k k'
    have := congrArg φ (hεe B k k')
    rw [map_mul, map_mul, hφ, one_mul, one_mul, map_pow] at this
    exact this
  refine ⟨xK, θK, fun h => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    show schemeHomOverComp _ hr (x 0) = _
    rw [hx0]; exact u.L.one_natural _ _ _ hr
  ·
    intro h h'
    show schemeHomOverComp _ hr (x (h + h')) = _
    rw [hx]; exact u.L.mul_natural _ _ _ hr _ _
  ·
    intro h h' hh
    exact hxinj K φ h h' (congrArg Subtype.val hh)
  ·
    intro y hy
    letI : Algebra R K := φ.toAlgebra
    obtain ⟨m, r, hr1, hrj⟩ := (hxK K y).mp hy

    have hex : ∃ j, r j ≠ 0 := by
      by_contra hall
      push Not at hall
      have : Ideal.span (Set.range r) = ⊥ := by
        rw [Ideal.span_eq_bot]; rintro _ ⟨j, rfl⟩; exact hall j
      rw [this] at hr1
      exact bot_ne_top hr1
    obtain ⟨j, hj⟩ := hex
    obtain ⟨h, hh⟩ := hrj j
    refine ⟨h, Subtype.ext ?_⟩

    have hunit : IsUnit (r j) := isUnit_iff_ne_zero.mpr hj
    haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away (r j))))) := by
      have hbij : Function.Bijective (algebraMap K (Localization.Away (r j))) :=
        IsLocalization.atUnits K (Submonoid.powers (r j))
          (by rintro _ ⟨n, rfl⟩; exact hunit.pow n) |>.bijective
      let e : CommRingCat.of K ≅ CommRingCat.of (Localization.Away (r j)) :=
        (RingEquiv.ofBijective (algebraMap K (Localization.Away (r j))) hbij).toCommRingCatIso
      change IsIso (Spec.map e.hom)
      infer_instance
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away (r j))))), hh]
    show _ = _ ≫ Spec.map (CommRingCat.ofHom φ) ≫ (x h).1
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  ·
    intro h
    apply Subtype.ext
    have := hβpt (θ₀ h)
    rw [Category.comp_id, hθ₀] at this
    exact this
  ·
    intro k k' s
    have h1 : θK k * θK k' = ThetaPt.ofScalar (Units.map (φ : R →* K) (e k k')) * (θK k' * θK k) := by
      show β (θ₀ k) * β (θ₀ k') = _ * (β (θ₀ k') * β (θ₀ k))
      rw [← map_mul, hgrp, map_mul, map_mul, hβsc]
    have h2 := congrArg (fun θ : ThetaPt u.f u.L u.pol t' => θ.act s) h1
    simp only [ThetaPt.mul_act, ThetaPt.ofScalar_act] at h2
    rw [h2]
    congr 2
    show ((Units.map (φ : R →* K) (e k k') : Kˣ) : K) = φ ζ ^ (B k k').val
    rw [Units.coe_map]; exact hφe k k'

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isAlgClosed_typePoints_thetaPt_of_idempotent_ne_zero
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isAlgClosed_typePoints_thetaPt_of_idempotent_ne_zero (solution)
