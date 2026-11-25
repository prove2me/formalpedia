-- Prove2me | Definitions.Def_GroundTheory_FunctionField_PlaceSum
-- name    : GroundTheory_FunctionField_PlaceSum
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:19:29.20694+00:00
-- url     : https://prove2.me/theorems/4e97940d-debd-4e7f-87e6-97c2c9387b00
-- title:
--   Place Sum
-- statement:
--   Definitions and structural lemmas for Place Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceSum.lean

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_isTorsionFree
import Theorems.Thm_GroundTheory_FunctionField_Place_eq_of_le
import Theorems.Thm_GroundTheory_FunctionField_Place_liesOver_of_le
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
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
noncomputable abbrev algebraExt (v : Place k K) : Algebra v.ring K' :=
  ((algebraMap K K').comp (algebraMap v.ring K)).toAlgebra
attribute [local instance low] algebraExt
omit [Algebra k K'] [IsScalarTower k K K'] in
theorem isScalarTower_ext (v : Place k K) : IsScalarTower v.ring K K' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
attribute [local instance] isScalarTower_ext
omit [Algebra k K'] [IsScalarTower k K K'] in
theorem isTorsionFree_ext (v : Place k K) : Module.IsTorsionFree v.ring K' :=
  Module.isTorsionFree_iff_algebraMap_injective.2
    ((algebraMap K K').injective.comp (IsFractionRing.injective v.ring K))
attribute [local instance] isTorsionFree_ext
section Closure
variable [IsFunctionField k K] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] (v : Place k K)
omit [Algebra k K'] [IsScalarTower k K K'] in
theorem isDedekindDomain_closure : IsDedekindDomain (integralClosure v.ring K') :=
  IsIntegralClosure.isDedekindDomain v.ring K K' _
omit [Algebra k K'] [IsScalarTower k K K'] [IsFunctionField k K] [Algebra.IsSeparable K K'] in
theorem isFractionRing_closure : IsFractionRing (integralClosure v.ring K') K' :=
  integralClosure.isFractionRing_of_finite_extension (A := v.ring) K K'
omit [Algebra k K'] [IsScalarTower k K K'] in
theorem finite_closure : Module.Finite v.ring (integralClosure v.ring K') :=
  IsIntegralClosure.finite v.ring K K' _
omit [Algebra k K'] [IsScalarTower k K K'] [IsFunctionField k K] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] in
theorem isTorsionFree_closure : Module.IsTorsionFree v.ring (integralClosure v.ring K') :=
  IsIntegralClosure.isTorsionFree v.ring K'
attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure
end Closure
section Correspondence
variable [IsFunctionField k K] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] (v : Place k K)
attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure
omit [Algebra k K'] [IsScalarTower k K K'] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] in
theorem ne_bot_of_mem_primesOver {q : Ideal (integralClosure v.ring K')}
    (hq : q ∈ (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) : q ≠ ⊥ := by
  intro h
  have hinj : Function.Injective (algebraMap v.ring (integralClosure v.ring K')) :=
    Module.isTorsionFree_iff_algebraMap_injective.1 (isTorsionFree_closure v)
  apply IsDiscreteValuationRing.not_a_field v.ring
  rw [hq.2.over, h]
  exact Ideal.comap_bot_of_injective _ hinj
noncomputable def primeHS (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    HeightOneSpectrum (integralClosure v.ring K') :=
  ⟨q.1, q.2.1, v.ne_bot_of_mem_primesOver q.2⟩
omit [IsScalarTower k K K'] [IsFunctionField k K] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] in

theorem mem_of_isIntegral_of_liesOver {w : Place k K'} (h : w.LiesOver v) {x : K'}
    (hx : IsIntegral v.ring x) : x ∈ w.ring := by
  let := h.algebra
  have : IsScalarTower v.ring w.ring K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hx.tower_top (A := w.ring))
  rw [← hy]
  exact y.2
noncomputable abbrev placeOfPrime (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    Place k K' where
  ring := HeightOneSpectrum.valuationSubringAtPrime K' (v.primeHS q)
  ne_top := by
    intro htop
    obtain ⟨π, hπ⟩ := (v.primeHS q).valuation_exists_uniformizer K'
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K') (v := v.primeHS q)
    have hmem : π⁻¹ ∈ ((v.primeHS q).valuation K').valuationSubring :=
      hle (htop ▸ ValuationSubring.mem_top _)
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at hmem
    omega
  algebraMap_mem c := by
    have hc : IsIntegral v.ring (algebraMap k K' c) := by
      rw [IsScalarTower.algebraMap_apply k K K']
      exact isIntegral_algebraMap (R := v.ring) (x := (⟨_, v.algebraMap_mem c⟩ : v.ring))
    exact Subalgebra.algebraMap_mem (Localization.subalgebra.ofField K' _
      (v.primeHS q).asIdeal.primeCompl_le_nonZeroDivisors)
      (⟨algebraMap k K' c, hc⟩ : integralClosure v.ring K')
theorem closure_mem_placeOfPrime (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K'))
    (b : integralClosure v.ring K') : (b : K') ∈ (v.placeOfPrime q).ring :=
  Subalgebra.algebraMap_mem (Localization.subalgebra.ofField K' _
    (v.primeHS q).asIdeal.primeCompl_le_nonZeroDivisors) b
theorem placeOfPrime_liesOver (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    (v.placeOfPrime q).LiesOver v :=
  liesOver_of_le fun x hx =>
    v.closure_mem_placeOfPrime q (algebraMap v.ring (integralClosure v.ring K') ⟨x, hx⟩)
end Correspondence
section Sum
variable [IsFunctionField k K] [IsFunctionField k K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] (v : Place k K)
attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure
noncomputable def closureHom {w : Place k K'} (h : w.LiesOver v) :
    integralClosure v.ring K' →+* w.ring :=
  RingHom.codRestrict (algebraMap (integralClosure v.ring K') K') w.ring fun b =>
    v.mem_of_isIntegral_of_liesOver h ((mem_integralClosure_iff v.ring K').1 b.2)
noncomputable def primeOfPlace {w : Place k K'} (h : w.LiesOver v) :
    (maximalIdeal v.ring).primesOver (integralClosure v.ring K') :=
  ⟨(maximalIdeal w.ring).comap (v.closureHom h), Ideal.comap_isPrime _ _, ⟨by
    let := h.algebra
    have := h.isLocalHom
    have hc : (v.closureHom h).comp (algebraMap v.ring (integralClosure v.ring K')) =
        algebraMap v.ring w.ring := RingHom.ext fun a => Subtype.ext rfl
    change maximalIdeal v.ring = Ideal.comap (algebraMap v.ring (integralClosure v.ring K'))
      (Ideal.comap (v.closureHom h) (maximalIdeal w.ring))
    rw [Ideal.comap_comap, hc]
    have hlo : (maximalIdeal w.ring).LiesOver (maximalIdeal v.ring) := inferInstance
    exact hlo.over⟩⟩
theorem placeOfPrime_primeOfPlace {w : Place k K'} (h : w.LiesOver v) :
    v.placeOfPrime (v.primeOfPlace h) = w := by
  refine Place.eq_of_le fun x hx => ?_
  obtain ⟨a, s, hs, rfl⟩ := hx
  have ha : ((a : integralClosure v.ring K') : K') ∈ w.ring := (v.closureHom h a).2
  have hsw : ((s : integralClosure v.ring K') : K') ∈ w.ring := (v.closureHom h s).2
  have hs' : v.closureHom h s ∉ maximalIdeal w.ring := hs
  have hs1 : w.ring.valuation (s : K') = 1 :=
    le_antisymm (w.ring.valuation_le_one_iff _ |>.2 hsw) (not_lt.1 fun hlt =>
      hs' ((w.ring.valuation_lt_one_iff _).2 hlt))
  have hsinv : ((s : integralClosure v.ring K') : K')⁻¹ ∈ w.ring := by
    rw [← w.ring.valuation_le_one_iff, map_inv₀, hs1, inv_one]
  exact mul_mem ha hsinv
omit [IsFunctionField k K'] in
theorem primeOfPlace_placeOfPrime
    (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    v.primeOfPlace (v.placeOfPrime_liesOver q) = q := by
  apply Subtype.ext
  ext b
  change v.closureHom _ b ∈ maximalIdeal (v.placeOfPrime q).ring ↔ b ∈ q.1
  rw [ValuationSubring.valuation_lt_one_iff]
  change (v.placeOfPrime q).ring.valuation (b : K') < 1 ↔ b ∈ q.1
  constructor
  · intro hb
    by_contra hbq
    have hinv : ((b : integralClosure v.ring K') : K')⁻¹ ∈ (v.placeOfPrime q).ring :=
      ⟨1, b, hbq, by simp⟩
    have hbmem := v.closure_mem_placeOfPrime q b
    have hb0 : (b : K') ≠ 0 := by
      intro h0
      rw [h0, inv_zero] at hinv
      exact hbq (by
        have : b = 0 := Subtype.ext h0
        rw [this]; exact q.1.zero_mem)
    have h1 := (v.placeOfPrime q).ring.valuation_le_one_iff _ |>.2 hinv
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd hb (not_lt.2 h1)
  · intro hbq
    by_contra hb
    have hb1 : (v.placeOfPrime q).ring.valuation (b : K') = 1 :=
      le_antisymm ((v.placeOfPrime q).ring.valuation_le_one_iff _ |>.2
        (v.closure_mem_placeOfPrime q b)) (not_lt.1 hb)
    have hb0 : (b : K') ≠ 0 := by
      intro h0; rw [h0, map_zero] at hb1; exact zero_ne_one hb1
    have hinv : ((b : integralClosure v.ring K') : K')⁻¹ ∈ (v.placeOfPrime q).ring := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hb1, inv_one]
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K') (v := v.primeHS q)
    have h1 : (v.primeHS q).valuation K' (b : K')⁻¹ ≤ 1 := hle hinv
    have h2 : (v.primeHS q).valuation K' (algebraMap (integralClosure v.ring K') K' b) < 1 :=
      ((v.primeHS q).valuation_lt_one_iff_mem (K := K') b).2 hbq
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd h2 (not_lt.2 h1)
noncomputable def primesOverEquiv :
    (maximalIdeal v.ring).primesOver (integralClosure v.ring K') ≃
      {w : Place k K' // w.LiesOver v} where
  toFun q := ⟨v.placeOfPrime q, v.placeOfPrime_liesOver q⟩
  invFun w := v.primeOfPlace w.2
  left_inv q := v.primeOfPlace_placeOfPrime q
  right_inv w := Subtype.ext (v.placeOfPrime_primeOfPlace w.2)
theorem finite_liesOver : {w : Place k K' | w.LiesOver v}.Finite := by
  have hfin : ((maximalIdeal v.ring).primesOver (integralClosure v.ring K')).Finite :=
    Algebra.QuasiFinite.finite_primesOver _
  have := hfin.to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ v.primesOverEquiv)
noncomputable def heightOneSpectrumEquiv :
    {P : HeightOneSpectrum (integralClosure v.ring K') //
        P.asIdeal.LiesOver (maximalIdeal v.ring)} ≃
      (maximalIdeal v.ring).primesOver (integralClosure v.ring K') where
  toFun P := ⟨P.1.asIdeal, P.1.isPrime, P.2⟩
  invFun q := ⟨v.primeHS q, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable def heightOneSpectrumEquivPlaces :
    {P : HeightOneSpectrum (integralClosure v.ring K') //
        P.asIdeal.LiesOver (maximalIdeal v.ring)} ≃ {w : Place k K' // w.LiesOver v} :=
  v.heightOneSpectrumEquiv.trans v.primesOverEquiv
end Sum
end Place
end GroundTheory.FunctionField


