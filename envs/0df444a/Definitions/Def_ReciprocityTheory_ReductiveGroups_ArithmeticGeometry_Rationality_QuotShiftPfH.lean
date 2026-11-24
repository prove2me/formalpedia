-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotShiftPfH
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotShiftPfH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:47.316021+00:00
-- url     : https://prove2.me/theorems/350456a9-1671-44d5-b9c2-d93ad717d2c4
-- title:
--   Quot Shift Pf H
-- statement:
--   Definitions and structural lemmas for Quot Shift Pf H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QuotShiftPfH.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
open IsDedekindDomain
noncomputable abbrev Rv {R : Type*} [CommRing R] [IsDedekindDomain R] (F : Type*) [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) : Subring F :=
  (v.valuationSubringAtPrime F).toSubring
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] (v : HeightOneSpectrum R)
lemma val_eq_exp {x : F} (hx : x ≠ 0) : v.valuation F x = WithZero.exp (-(ordAt v x)) := by
  unfold ordAt
  rw [neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx)]
lemma mem_Rv_iff (x : F) : x ∈ Rv F v ↔ v.valuation F x ≤ 1 := by
  show x ∈ v.valuationSubringAtPrime F ↔ _
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring v]
  exact Valuation.mem_valuationSubring_iff (v.valuation F) x
lemma mem_Rv_iff_ord {x : F} (hx : x ≠ 0) : x ∈ Rv F v ↔ 0 ≤ ordAt v x := by
  rw [mem_Rv_iff, val_eq_exp v hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
  exact neg_nonpos
lemma ordAt_mul' {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) : ordAt v (x * y) = ordAt v x + ordAt v y := by
  unfold ordAt
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy),
    neg_add]
lemma ordAt_zpow' {x : F} (k : ℤ) : ordAt v (x ^ k) = k * ordAt v x := by
  unfold ordAt
  rw [map_zpow₀, WithZero.log_zpow, smul_eq_mul, mul_neg]
lemma ordAt_one' : ordAt v (1 : F) = 0 := by
  unfold ordAt
  rw [map_one, WithZero.log_one, neg_zero]
lemma ord_nonneg (a : Rv F v) (ha : (a : F) ≠ 0) : 0 ≤ ordAt v (a : F) := by
  exact (mem_Rv_iff_ord v ha).mp a.2
lemma isUnit_of_ord_zero (a : Rv F v) (ha : (a : F) ≠ 0) (h0 : ordAt v (a : F) = 0) : IsUnit a := by
  have hinv : ordAt v ((a : F)⁻¹) = 0 := by
    rw [← zpow_neg_one, ordAt_zpow', h0, mul_zero]
  have hmem : (a : F)⁻¹ ∈ Rv F v := (mem_Rv_iff_ord v (inv_ne_zero ha)).mpr hinv.ge
  have hab : a * ⟨_, hmem⟩ = 1 := Subtype.ext (mul_inv_cancel₀ ha)
  exact ⟨⟨a, ⟨_, hmem⟩, hab, by rw [mul_comm]; exact hab⟩, rfl⟩
lemma ord_zero_of_isUnit (a : Rv F v) (ha : IsUnit a) : ordAt v (a : F) = 0 := by
  obtain ⟨u, rfl⟩ := ha
  have h1 : ((u : Rv F v) : F) * (((u⁻¹ : (Rv F v)ˣ) : Rv F v) : F) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  have hne1 : ((u : Rv F v) : F) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hne2 : (((u⁻¹ : (Rv F v)ˣ) : Rv F v) : F) ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have hs := congrArg (ordAt v) h1
  rw [ordAt_mul' v hne1 hne2, ordAt_one'] at hs
  have ha1 := ord_nonneg v _ hne1
  have ha2 := ord_nonneg v _ hne2
  omega
lemma exists_ord_one : ∃ π : F, π ≠ 0 ∧ ordAt v π = 1 := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer F v
  have h0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨π, h0, ?_⟩
  unfold ordAt
  rw [hπ, WithZero.log_exp, neg_neg]
lemma irreducible_of_ord_one {π : F} (h0 : π ≠ 0) (h1 : ordAt v π = 1) :
    Irreducible (⟨π, (mem_Rv_iff_ord v h0).mpr (by omega)⟩ : Rv F v) := by
  rw [irreducible_iff]
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := ord_zero_of_isUnit v _ hu
    simp only at this
    omega
  · have hF : π = (a : F) * (b : F) := congrArg Subtype.val hab
    have ha0 : (a : F) ≠ 0 := fun h => h0 (by rw [hF, h, zero_mul])
    have hb0 : (b : F) ≠ 0 := fun h => h0 (by rw [hF, h, mul_zero])
    have hsum : ordAt v π = ordAt v (a : F) + ordAt v (b : F) := by rw [hF, ordAt_mul' v ha0 hb0]
    have hna := ord_nonneg v a ha0
    have hnb := ord_nonneg v b hb0
    by_cases hz : ordAt v (a : F) = 0
    · exact Or.inl (isUnit_of_ord_zero v a ha0 hz)
    · exact Or.inr (isUnit_of_ord_zero v b hb0 (by omega))
lemma eq_unit_mul_pow {π : F} (h0 : π ≠ 0) (h1 : ordAt v π = 1) (x : Rv F v) (hx : (x : F) ≠ 0) :
    ∃ u : (Rv F v)ˣ, x = (u : Rv F v) * (⟨π, (mem_Rv_iff_ord v h0).mpr (by omega)⟩ : Rv F v) ^
      (ordAt v (x : F)).toNat := by
  obtain ⟨n, hn⟩ : ∃ n, n = (ordAt v (x : F)).toNat := ⟨_, rfl⟩
  rw [← hn]
  have hnz : (n : ℤ) = ordAt v (x : F) := by rw [hn]; exact Int.toNat_of_nonneg (ord_nonneg v x hx)
  have hπn : π ^ n ≠ 0 := pow_ne_zero _ h0
  have hy0 : (x : F) / π ^ n ≠ 0 := div_ne_zero hx hπn
  have hyord : ordAt v ((x : F) / π ^ n) = 0 := by
    rw [div_eq_mul_inv, ordAt_mul' v hx (inv_ne_zero hπn), ← zpow_neg_one, ordAt_zpow',
      ← zpow_natCast, ordAt_zpow', h1]
    omega
  have hymem : (x : F) / π ^ n ∈ Rv F v := (mem_Rv_iff_ord v hy0).mpr hyord.ge
  have hu := isUnit_of_ord_zero v ⟨_, hymem⟩ hy0 hyord
  refine ⟨hu.unit, Subtype.ext ?_⟩
  rw [IsUnit.unit_spec]
  show (x : F) = (x : F) / π ^ n * π ^ n
  rw [div_mul_cancel₀ _ hπn]
lemma hasFactorization : IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization (Rv F v) := by
  obtain ⟨π, h0, h1⟩ := exists_ord_one (F := F) v
  refine ⟨_, irreducible_of_ord_one v h0 h1, ?_⟩
  intro x hx
  have hxF : (x : F) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨u, hu⟩ := eq_unit_mul_pow v h0 h1 x hxF
  exact ⟨_, u, by rw [hu, mul_comm]⟩
instance dvr_Rv : IsDiscreteValuationRing (Rv F v) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    (hasFactorization v)
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH


