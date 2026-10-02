-- Prove2me | Definitions.Def_Yukon_7ac04eb8d9104a96b1b2bba0
-- name    : Yukon_7ac04eb8d9104a96b1b2bba0
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T10:11:33.295979+00:00
-- url     : https://prove2.me/theorems/d5e42388-5bcc-4dfa-a31d-cced2652595d
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.WeightedPlaceOrder6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.WeightedPlaceOrder6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/WeightedPlaceOrder6807.lean
--
--   yukon-proof-operation:foundation-direct-1cff6d9cce04483d55bcf1b7ca91d6f7b3f49c7c9f5347c6e03e5fdf7a79acbd
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNWY4YjUzZjYwY2NkYTZmZTI1OTJkZjJmOTRhOTA2NDJlNjEzMWM4NDRjYWJkZWM5N2RkOWQ5ZTE1OWI2NzA3ZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTFjZmY2ZDljY2UwNDQ4M2Q1NWJjZjFiN2NhOTFkNmY3YjNmNDljN2M5ZjUzNDdjNmUwM2U1ZmRmN2E3OWFjYmQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83YWMwNGViOGQ5MTA0YTk2YjFiMmJiYTAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_9d89c768274d20327591ec1d

/-
UNCOMPILED. Ideal-power multiplicities at the original affine-model places.
No equality of multiplicities after base change is required. A point valuation
is nonpositive on the affine coordinate ring and strictly positive in order on
the point's maximal ideal. Ideal powers then give the full lower bound mu.
-/












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.WeightedPlaceOrder6807
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

section ValuationFiltration
variable {A L : Type*} [CommRing A] [Field L]
  (iota : A →+* L) (v : Valuation L (WithZero (Multiplicative ℤ)))
  (hbound : ∀ a : A, v (iota a) ≤ 1)

/-- Functions having order at least n. All affine functions have order >= 0,
so this subset really is an ideal, not just an additive subgroup. -/
def orderIdeal (n : ℕ) : Ideal A where
  carrier := {a | v (iota a) ≤ WithZero.exp (-(n : ℤ))}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change v (iota (a+b)) ≤ _
    rw [map_add]
    exact (v.map_add _ _).trans (max_le ha hb)
  smul_mem' := by
    intro r a ha
    change v (iota (r*a)) ≤ _
    rw [map_mul, map_mul]
    simpa only [one_mul] using mul_le_mul' (hbound r) ha

theorem ideal_pow_value_le (J : Ideal A)
    (hvanish : ∀ a ∈ J, v (iota a) < 1) (n : ℕ) :
    J^n ≤ orderIdeal iota v hbound n := by
  induction n with
  | zero =>
    intro a _
    change v (iota a) ≤ WithZero.exp (-(0 : ℤ))
    simpa only [neg_zero, WithZero.exp_zero] using hbound a
  | succ n ih =>
    rw [pow_succ]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    have h1 : v (iota b) ≤ WithZero.exp (-1 : ℤ) :=
      RCN359.value_le_exp_neg_one (hvanish b hb)
    have hn : v (iota a) ≤ WithZero.exp (-(n : ℤ)) := ih ha
    change v (iota (a*b)) ≤ WithZero.exp (-((n+1 : ℕ) : ℤ))
    rw [map_mul, map_mul]
    have hm := mul_le_mul' hn h1
    have he : WithZero.exp (-(n : ℤ)) * WithZero.exp (-1 : ℤ) =
        WithZero.exp (-((n+1 : ℕ) : ℤ)) := by
      rw [← WithZero.exp_add]
      congr 1
      push_cast
      ring
    exact hm.trans_eq he

theorem order_ge_of_value_le (x : L) (hx : x ≠ 0) (n : ℕ)
    (hn : v x ≤ WithZero.exp (-(n : ℤ))) :
    (n : ℤ) ≤ -(v x).log := by
  have hv0 : v x ≠ 0 := (Valuation.ne_zero_iff v).mpr hx
  have hlog : (v x).log ≤ -(n : ℤ) := by
    have h := (WithZero.log_le_log hv0 (by simp)).2 hn
    simpa only [WithZero.log_exp] using h
  omega

include hbound in
/-- A denominator nonvanishing at the point has valuation exactly one.
It need not already have an inverse inside the affine coordinate ring. -/
theorem normalized_order_ge_pow {K : Type*} [Field K] [Algebra K A]
    (phi : A →ₐ[K] K)
    (hpoint : ∀ a, v (iota a) < 1 ↔ phi a = 0)
    (n : ℕ) (a b : A) (ha : a ∈ (RingHom.ker phi.toRingHom)^n)
    (hb : phi b ≠ 0) (hx : iota a / iota b ≠ 0) :
    (n : ℤ) ≤ -(v (iota a / iota b)).log := by
  have hbval : v (iota b) = 1 := by
    apply le_antisymm (hbound b)
    apply le_of_not_gt
    intro h
    exact hb ((hpoint b).mp h)
  have han : v (iota a) ≤ WithZero.exp (-(n : ℤ)) :=
    ideal_pow_value_le iota v hbound (RingHom.ker phi.toRingHom)
      (fun a ha => (hpoint a).mpr ha) n ha
  apply order_ge_of_value_le v _ hx n
  simpa only [map_div₀, hbval, div_one] using han

end ValuationFiltration

section ActualAffinePlaces
variable (K A L : Type*) [Field K] [IsAlgClosed K]
  [CommRing A] [IsDomain A] [Field L]
  [Algebra K A] [Algebra K L] [Algebra A L] [IsFractionRing A L]
  [Algebra (Polynomial K) A] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) A] [IsScalarTower K (Polynomial K) L]
  [IsScalarTower K A L] [IsScalarTower (Polynomial K) A L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

local instance  _root_.ProximityPrize.SubmissionLower.WeightedPlaceOrder6807.instIsScalarTowerRatFunc_proximityPrize : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K),
      ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) L,
      ← IsScalarTower.algebraMap_apply K (Polynomial K) L]

/-- Multiplicity at the same actualPointPlace used by the pinned zero-counting
infrastructure. This does not posit a new low-cost abstract place. -/
theorem actual_normalized_order_ge_pow (phi : A →ₐ[K] K)
    (n : ℕ) (a b : A) (ha : a ∈ (RingHom.ker phi.toRingHom)^n)
    (hb : phi b ≠ 0)
    (hx : algebraMap A L a / algebraMap A L b ≠ 0) :
    (n : ℤ) ≤ RCN026.order K L (RCN344.modelPlace K L A phi)
      (algebraMap A L a / algebraMap A L b) := by
  exact normalized_order_ge_pow (algebraMap A L)
    ((RCN000.actualPointPlace K A L phi).valuation L)
    (RCN000.actual_model_value_le_one K A L phi) phi
    (RCN000.actual_model_value_lt_one_iff K A L phi) n a b ha hb hx

end ActualAffinePlaces
end
end ProximityPrize.SubmissionLower.WeightedPlaceOrder6807


