-- Prove2me | Definitions.Def_GroundTheory_FunctionField_PlaceBridge
-- name    : GroundTheory_FunctionField_PlaceBridge
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:29:46.100366+00:00
-- url     : https://prove2.me/theorems/b1ed4dd7-c211-42e6-b132-4fb79b213cac
-- title:
--   Place Bridge
-- statement:
--   Definitions and structural lemmas for Place Bridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBridge.lean

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Theorems.Thm_GroundTheory_FunctionField_Place_eq_of_le
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_le_one_iff
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_lt_one_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply


set_option autoImplicit false
namespace GroundTheory.FunctionField
open IsDedekindDomain IsLocalRing
open scoped WithZero
namespace Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
section General
variable (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra B K] [IsFractionRing B K]
  (hk : ∀ c : k, algebraMap k K c ∈ (algebraMap B K).range)
noncomputable abbrev ofHeightOneSpectrum (P : HeightOneSpectrum B) : Place k K where
  ring := HeightOneSpectrum.valuationSubringAtPrime K P
  ne_top := by
    intro htop
    obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer K
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)
    have hmem : π⁻¹ ∈ (P.valuation K).valuationSubring := hle (htop ▸ ValuationSubring.mem_top _)
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at hmem
    omega
  algebraMap_mem c := by
    obtain ⟨b, hb⟩ := hk c
    rw [← hb]
    exact Subalgebra.algebraMap_mem
      (Localization.subalgebra.ofField K _ P.asIdeal.primeCompl_le_nonZeroDivisors) b
theorem algebraMap_mem_ofHeightOneSpectrum (P : HeightOneSpectrum B) (b : B) :
    algebraMap B K b ∈ (ofHeightOneSpectrum B hk P).ring :=
  Subalgebra.algebraMap_mem (Localization.subalgebra.ofField K _ P.asIdeal.primeCompl_le_nonZeroDivisors) b
noncomputable def centerHom (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) : B →+* v.ring :=
  RingHom.codRestrict (algebraMap B K) v.ring hv
noncomputable def center (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) :
    HeightOneSpectrum B where
  asIdeal := (maximalIdeal v.ring).comap (centerHom B v hv)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h0
    apply v.ne_top
    have hunit : ∀ b : B, b ≠ 0 → v.ring.valuation (algebraMap B K b) = 1 := by
      intro b hb
      refine le_antisymm ((v.ring.valuation_le_one_iff _).2 (hv b)) (not_lt.1 fun hlt => hb ?_)
      have hmem : centerHom B v hv b ∈ maximalIdeal v.ring := (v.ring.valuation_lt_one_iff _).2 hlt
      have : b ∈ (maximalIdeal v.ring).comap (centerHom B v hv) := hmem
      rw [h0] at this
      exact this
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    rw [← v.ring.valuation_le_one_iff, map_div₀, hunit s hs0, div_one]
    exact (v.ring.valuation_le_one_iff _).2 (hv a)
variable [IsFunctionField k K]
theorem ofHeightOneSpectrum_center (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) :
    ofHeightOneSpectrum B hk (center B v hv) = v := by
  refine Place.eq_of_le fun x hx => ?_
  obtain ⟨a, s, hs, rfl⟩ := hx
  have hs' : centerHom B v hv s ∉ maximalIdeal v.ring := hs
  have hs1 : v.ring.valuation (algebraMap B K s) = 1 :=
    le_antisymm ((v.ring.valuation_le_one_iff _).2 (hv s)) (not_lt.1 fun hlt =>
      hs' ((v.ring.valuation_lt_one_iff _).2 hlt))
  have hsinv : (algebraMap B K s)⁻¹ ∈ v.ring := by
    rw [← v.ring.valuation_le_one_iff, map_inv₀, hs1, inv_one]
  exact mul_mem (hv a) hsinv
omit [IsFunctionField k K] in
theorem center_ofHeightOneSpectrum (P : HeightOneSpectrum B) :
    center B (ofHeightOneSpectrum B hk P) (algebraMap_mem_ofHeightOneSpectrum B hk P) = P := by
  ext b
  change centerHom B _ _ b ∈ maximalIdeal (ofHeightOneSpectrum B hk P).ring ↔ b ∈ P.asIdeal
  rw [ValuationSubring.valuation_lt_one_iff]
  change (ofHeightOneSpectrum B hk P).ring.valuation (algebraMap B K b) < 1 ↔ b ∈ P.asIdeal
  have hbmem := algebraMap_mem_ofHeightOneSpectrum B hk P b
  constructor
  · intro hb
    by_contra hbP
    have hinv : (algebraMap B K b)⁻¹ ∈ (ofHeightOneSpectrum B hk P).ring :=
      ⟨1, b, hbP, by simp⟩
    have hb0 : algebraMap B K b ≠ 0 := by
      intro h0
      rw [h0, inv_zero] at hinv
      apply hbP
      have : b = 0 := IsFractionRing.injective B K (h0.trans (map_zero _).symm)
      rw [this]
      exact P.asIdeal.zero_mem
    have h1 := (ofHeightOneSpectrum B hk P).ring.valuation_le_one_iff _ |>.2 hinv
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd hb (not_lt.2 h1)
  · intro hbP
    by_contra hb
    have hb1 : (ofHeightOneSpectrum B hk P).ring.valuation (algebraMap B K b) = 1 :=
      le_antisymm ((ofHeightOneSpectrum B hk P).ring.valuation_le_one_iff _ |>.2 hbmem)
        (not_lt.1 hb)
    have hb0 : algebraMap B K b ≠ 0 := by
      intro h0; rw [h0, map_zero] at hb1; exact zero_ne_one hb1
    have hinv : (algebraMap B K b)⁻¹ ∈ (ofHeightOneSpectrum B hk P).ring := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hb1, inv_one]
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)
    have h1 : P.valuation K (algebraMap B K b)⁻¹ ≤ 1 := hle hinv
    have h2 : P.valuation K (algebraMap B K b) < 1 := (P.valuation_lt_one_iff_mem (K := K) b).2 hbP
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd h2 (not_lt.2 h1)
noncomputable def equivHeightOneSpectrum :
    {v : Place k K // ∀ b : B, algebraMap B K b ∈ v.ring} ≃ HeightOneSpectrum B where
  toFun v := center B v.1 v.2
  invFun P := ⟨ofHeightOneSpectrum B hk P, algebraMap_mem_ofHeightOneSpectrum B hk P⟩
  left_inv v := Subtype.ext (ofHeightOneSpectrum_center B hk v.1 v.2)
  right_inv P := center_ofHeightOneSpectrum B hk P
end General
section RatFunc
open scoped Polynomial
omit [Algebra k K] in

theorem _root_.GroundTheory.FunctionField.IsFunctionField.of_trdeg_eq_one [Algebra k K]
    [Algebra.EssFiniteType k K] (h : Algebra.trdeg k K = 1) : IsFunctionField k K := by
  have : Algebra.Transcendental k K :=
    (trdeg_ne_zero_iff (R := k) (A := K)).1 (by rw [h]; exact one_ne_zero)
  obtain ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := k) (A := K)
  have hbx : IsTranscendenceBasis k ((↑) : ({x} : Set K) → K) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set K))).2 hx)
      (by rw [h, Cardinal.mk_singleton])
  have halg := hbx.isAlgebraic_field
  rw [Subtype.range_coe] at halg
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {x}) K :=
    Algebra.EssFiniteType.of_comp k _ K
  exact ⟨⟨x, hx, Algebra.finite_of_essFiniteType_of_isAlgebraic⟩⟩
omit [Algebra k K] in
theorem _root_.GroundTheory.FunctionField.essFiniteType_ratFunc : Algebra.EssFiniteType k (RatFunc k) := by
  have : Algebra.EssFiniteType k[X] (RatFunc k) :=
    .of_isLocalization _ (nonZeroDivisors k[X])
  exact .comp k k[X] (RatFunc k)
omit [Algebra k K] in

instance _root_.GroundTheory.FunctionField.isFunctionField_ratFunc : IsFunctionField k (RatFunc k) := by
  have := essFiniteType_ratFunc (k := k)
  apply IsFunctionField.of_trdeg_eq_one
  have : Algebra.IsAlgebraic k[X] (RatFunc k) := IsLocalization.isAlgebraic _ (nonZeroDivisors k[X])
  have h := trdeg_add_eq k k[X] (A := RatFunc k)
  rw [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at h
  exact h.symm
end RatFunc
section RingOfIntegers
open scoped Polynomial
variable [IsFunctionField k K] [Algebra k[X] K] [Algebra (RatFunc k) K]
  [IsScalarTower k[X] (RatFunc k) K] [IsScalarTower k k[X] K] [FunctionField k K]
omit [IsFunctionField k K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K]
  [FunctionField k K] in
theorem algebraMap_polynomial_mem (v : Place k K) (hv : algebraMap k[X] K Polynomial.X ∈ v.ring)
    (p : k[X]) : algebraMap k[X] K p ∈ v.ring := by
  have h : algebraMap k[X] K p = Polynomial.aeval (algebraMap k[X] K Polynomial.X) p := by
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [h, ← v.ring.valuation_le_one_iff]
  exact v.valuation_aeval_le_one hv p
omit [IsFunctionField k K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K]
  [FunctionField k K] in

theorem forall_mem_ringOfIntegers_iff (v : Place k K) :
    (∀ b : FunctionField.ringOfIntegers k K, algebraMap _ K b ∈ v.ring) ↔
      algebraMap k[X] K Polynomial.X ∈ v.ring := by
  constructor
  · intro h
    have hX : IsIntegral k[X] (algebraMap k[X] K Polynomial.X) := isIntegral_algebraMap
    have := h (IsIntegralClosure.mk' (FunctionField.ringOfIntegers k K) _ hX)
    rwa [IsIntegralClosure.algebraMap_mk'] at this
  · intro hv b
    let : Algebra k[X] v.ring :=
      (RingHom.codRestrict (algebraMap k[X] K) v.ring (v.algebraMap_polynomial_mem hv)).toAlgebra
    have : IsScalarTower k[X] v.ring K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hb : IsIntegral k[X] (algebraMap (FunctionField.ringOfIntegers k K) K b) :=
      (IsIntegralClosure.isIntegral k[X] K b).map
        (IsScalarTower.toAlgHom k[X] (FunctionField.ringOfIntegers k K) K)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hb.tower_top (A := v.ring))
    rw [← hy]
    exact y.2
omit [IsFunctionField k K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K]
  [FunctionField k K] in
theorem algebraMap_mem_range_ringOfIntegers (c : k) :
    algebraMap k K c ∈ (algebraMap (FunctionField.ringOfIntegers k K) K).range := by
  have hc : IsIntegral k[X] (algebraMap k[X] K (Polynomial.C c)) := isIntegral_algebraMap
  refine ⟨IsIntegralClosure.mk' (FunctionField.ringOfIntegers k K) _ hc, ?_⟩
  rw [IsIntegralClosure.algebraMap_mk', ← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]
noncomputable def equivHeightOneSpectrumRingOfIntegers [Algebra.IsSeparable (RatFunc k) K] :
    {v : Place k K // algebraMap k[X] K Polynomial.X ∈ v.ring} ≃
      HeightOneSpectrum (FunctionField.ringOfIntegers k K) :=
  (Equiv.subtypeEquivRight fun v => (forall_mem_ringOfIntegers_iff v).symm).trans
    (equivHeightOneSpectrum _ algebraMap_mem_range_ringOfIntegers)
end RingOfIntegers
section Separating
open scoped IntermediateField.algebraAdjoinAdjoin
omit [Algebra k K] in

theorem isPrincipalIdealRing_adjoin [Algebra k K] (t : K) :
    IsPrincipalIdealRing (Algebra.adjoin k {t}) := by
  refine IsPrincipalIdealRing.of_surjective
    (Polynomial.aeval (R := k) (⟨t, Algebra.self_mem_adjoin_singleton k t⟩ : Algebra.adjoin k {t})) ?_
  rintro ⟨y, hy⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
  exact ⟨p, Subtype.ext (Polynomial.aeval_subalgebra_coe p _ _)⟩
variable [IsFunctionField k K] (t : K) [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K]
theorem transcendental_of_isSeparable : Transcendental k t := by
  intro ht
  have : FiniteDimensional k (IntermediateField.adjoin k {t}) :=
    IntermediateField.adjoin.finiteDimensional ht.isIntegral
  have : Algebra.IsAlgebraic k (IntermediateField.adjoin k {t}) := Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.trans k (IntermediateField.adjoin k {t}) K
  have h := trdeg_eq_one (k := k) (K := K)
  rw [trdeg_eq_zero] at h
  exact zero_ne_one h
theorem isDedekindDomain_closure_adjoin :
    IsDedekindDomain (integralClosure (Algebra.adjoin k {t}) K) := by
  have := isPrincipalIdealRing_adjoin (k := k) t
  have := finiteDimensional_adjoin (transcendental_of_isSeparable (k := k) t)
  exact IsIntegralClosure.isDedekindDomain (Algebra.adjoin k {t}) (IntermediateField.adjoin k {t}) K _
theorem isFractionRing_closure_adjoin :
    IsFractionRing (integralClosure (Algebra.adjoin k {t}) K) K := by
  have := finiteDimensional_adjoin (transcendental_of_isSeparable (k := k) t)
  exact integralClosure.isFractionRing_of_finite_extension (A := Algebra.adjoin k {t})
    (IntermediateField.adjoin k {t}) K
attribute [local instance] isDedekindDomain_closure_adjoin isFractionRing_closure_adjoin
omit [IsFunctionField k K] [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K] in

theorem forall_mem_closure_adjoin_iff (v : Place k K) :
    (∀ b : integralClosure (Algebra.adjoin k {t}) K, algebraMap _ K b ∈ v.ring) ↔ t ∈ v.ring := by
  constructor
  · intro h
    have hint : IsIntegral (Algebra.adjoin k {t}) t :=
      isIntegral_algebraMap (R := Algebra.adjoin k {t}) (A := K)
        (x := ⟨t, Algebra.self_mem_adjoin_singleton k t⟩)
    exact h ⟨t, hint⟩
  · intro hv b
    have hA : ∀ a : Algebra.adjoin k {t}, (a : K) ∈ v.ring := by
      rintro ⟨y, hy⟩
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
      rw [← v.ring.valuation_le_one_iff]
      exact v.valuation_aeval_le_one hv p
    let : Algebra (Algebra.adjoin k {t}) v.ring :=
      (RingHom.codRestrict (algebraMap (Algebra.adjoin k {t}) K) v.ring hA).toAlgebra
    have : IsScalarTower (Algebra.adjoin k {t}) v.ring K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hb : IsIntegral (Algebra.adjoin k {t}) (b : K) := b.2
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hb.tower_top (A := v.ring))
    show (b : K) ∈ v.ring
    rw [← hy]
    exact y.2
omit [IsFunctionField k K] [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K] in
theorem algebraMap_mem_range_closure_adjoin (c : k) :
    algebraMap k K c ∈ (algebraMap (integralClosure (Algebra.adjoin k {t}) K) K).range := by
  have hc : IsIntegral (Algebra.adjoin k {t}) (algebraMap k K c) :=
    isIntegral_algebraMap (R := Algebra.adjoin k {t}) (A := K)
      (x := ⟨algebraMap k K c, Subalgebra.algebraMap_mem _ c⟩)
  exact ⟨⟨algebraMap k K c, hc⟩, rfl⟩
noncomputable def equivOfSeparating :
    {v : Place k K // t ∈ v.ring} ≃ HeightOneSpectrum (integralClosure (Algebra.adjoin k {t}) K) :=
  (Equiv.subtypeEquivRight fun v => (forall_mem_closure_adjoin_iff t v).symm).trans
    (equivHeightOneSpectrum _ (algebraMap_mem_range_closure_adjoin t))
noncomputable def equivZerosOfSeparating :
    {v : Place k K // v.ring.valuation t < 1} ≃
      {P : HeightOneSpectrum (integralClosure (Algebra.adjoin k {t}) K) //
        (⟨t, isIntegral_algebraMap (R := Algebra.adjoin k {t}) (A := K)
          (x := ⟨t, Algebra.self_mem_adjoin_singleton k t⟩)⟩ :
            integralClosure (Algebra.adjoin k {t}) K) ∈ P.asIdeal} :=
  let e₁ : {v : Place k K // v.ring.valuation t < 1} ≃
      {w : {v : Place k K // t ∈ v.ring} // w.1.ring.valuation t < 1} :=
    { toFun v := ⟨⟨v.1, (v.1.ring.valuation_le_one_iff t).1 v.2.le⟩, v.2⟩
      invFun w := ⟨w.1.1, w.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  e₁.trans (Equiv.subtypeEquiv (equivOfSeparating t) fun w => by
    change _ ↔ centerHom _ w.1 _ _ ∈ maximalIdeal w.1.ring
    rw [ValuationSubring.valuation_lt_one_iff]
    rfl)
end Separating
end Place
end GroundTheory.FunctionField


