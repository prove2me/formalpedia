-- Prove2me | Definitions.Def_Yukon_88acd699d7b2611ef3b71a58
-- name    : Yukon_88acd699d7b2611ef3b71a58
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:43:21.234132+00:00
-- url     : https://prove2.me/theorems/4807677d-38c8-42ca-9b3a-a0da702074d2
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeBudget6812.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeBudget6812.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeBudget6812.lean
--
--   yukon-proof-operation:foundation-direct-9a218d6f05003e667793393f6daca9f23c3025bc5641f538f9b415f111b1339e
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNjRjNGEzMzBkYTEyMTY0ZWU2NTJkOTE5YjcxNzk0ZTBlNDYyODY5ZDA1ZmJiZWM0YWUxMjc1MGY1ZTZlNDNlOCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTlhMjE4ZDZmMDUwMDNlNjY3NzkzMzkzZjZkYWNhOWYyM2MzMDI1YmM1NjQxZjUzOGY5YjQxNWYxMTFiMTMzOWUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl84OGFjZDY5OWQ3YjI2MTFlZjNiNzFhNTgiLCJ2IjoyfQ]

import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561

import Definitions.Def_Yukon_40ebcc12c6d7b8bd9832993d

import Definitions.Def_Yukon_c5a0e39377dc346e7a8ed2ec

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.KrullDimension.Polynomial
























































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-!
# H-free bridge: the per-slice budget `HFreeSliceBudget`

Assembles the per-place bound on `L0` (HFreePlace6812) into the consumer's statement:
for a slice component `D` (prime of `E[Y,Y',Γ]` with a separable literal coordinate,
containing `F` and the slice equation `ℓ - t`, `H ∉ D`) and every finite set `W` of places,

  `3 Σ pole_ν τ ≤ Σ [(w+1)(4 T_ν + 2 zero_ν H) + 3 flagPole_ν unitAllFlag]`.

Each place `ν` restricts along `ψ : L0 → CoordinateField E D` to a trivial valuation (no
pole) or to `v^e` with `v` normalized; all quantities scale by `e`.  The centre of an affine
place has height `≤ 2` (Nullstellensatz, since `ℓ = t` is transcendental), which gives the two
local generators.  Pieces 3 and 4 (`CrudeBound`, `ResiduallySeparable`) are hypotheses.
-/

namespace ProximityPrize.SubmissionLower.HFree6812

open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204

section Centre

variable {Ω R : Type*} [Field Ω] [IsAlgClosed Ω] [Field R] [Algebra Ω R]

/-- The centre of a valuation on `Ω[Y,Y',Γ]` whose point has a coordinate combination
transcendental over `Ω` has height at most `2`. -/
theorem centre_height_le_two (ν : Valuation R ℤᵐ⁰) (y : Fin 3 → R)
    (𝔮 : Ideal (MvPolynomial (Fin 3) Ω)) [𝔮.IsPrime]
    (h𝔮 : ∀ P, P ∈ 𝔮 ↔ ν (aeval y P) < 1)
    (c : Fin 3 → Ω) (hcω : ∀ a : Ω, a ≠ 0 → ν (algebraMap Ω R a) = 1)
    (hℓ : ∀ a : Fin 3 → Ω, ν (∑ m, algebraMap Ω R (c m) * y m - algebraMap Ω R (∑ m, c m * a m)) = 1) :
    𝔮.height ≤ 2 := by
  classical
  have hnotmax : ¬ 𝔮.IsMaximal := by
    intro hmax
    obtain ⟨a, ha⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton (I := 𝔮)).1 hmax
    have hsmall : ∀ j, ν (y j - algebraMap Ω R (a j)) < 1 := by
      intro j
      have hmem : (MvPolynomial.X j - MvPolynomial.C (a j) : MvPolynomial (Fin 3) Ω) ∈ 𝔮 := by
        rw [ha, MvPolynomial.mem_vanishingIdeal_singleton_iff]
        simp
      have := (h𝔮 _).1 hmem
      simpa using this
    have hsum : ∑ m, algebraMap Ω R (c m) * y m - algebraMap Ω R (∑ m, c m * a m) =
        ∑ m, algebraMap Ω R (c m) * (y m - algebraMap Ω R (a m)) := by
      simp only [map_sum, map_mul, mul_sub, Finset.sum_sub_distrib]
    have hlt : ν (∑ m, algebraMap Ω R (c m) * y m - algebraMap Ω R (∑ m, c m * a m)) < 1 := by
      rw [hsum]
      refine ν.map_sum_lt one_ne_zero fun m _ => ?_
      rw [ν.map_mul]
      refine lt_of_le_of_lt (mul_le_of_le_one_left' ?_) (hsmall m)
      rcases eq_or_ne (c m) 0 with hc | hc
      · rw [hc, map_zero, ν.map_zero]; exact zero_le
      · exact (hcω _ hc).le
    exact absurd (hℓ a) (ne_of_lt hlt)
  obtain ⟨𝔪, h𝔪max, h𝔮𝔪⟩ := Ideal.exists_le_maximal 𝔮 Ideal.IsPrime.ne_top'
  have hlt : 𝔮 < 𝔪 := lt_of_le_of_ne h𝔮𝔪 (fun h => hnotmax (h ▸ h𝔪max))
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : (𝔪.height : WithBot ℕ∞) ≤ 3 := by
    refine (Ideal.height_le_ringKrullDim_of_isPrime (I := 𝔪)).trans (le_of_eq ?_)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h3 : 𝔪.height ≤ 3 := WithBot.coe_le_coe.mp h2
  have h4 : 𝔮.height + 1 ≤ 3 := h1.trans h3
  have hne : 𝔮.height ≠ ⊤ := by
    intro htop; rw [htop] at h4; exact absurd h4 (by decide)
  lift 𝔮.height to ℕ using hne with n hn
  have : n + 1 ≤ 3 := by exact_mod_cast h4
  exact_mod_cast (show n ≤ 2 by omega)

end Centre

section ValCentre

variable {R L : Type*} [CommRing R] [Field L]

/-- The centre `{r | ν (f r) < 1}` of a valuation on an integral ring hom, as a prime ideal. -/
def valCentre (f : R →+* L) (ν : Valuation L ℤᵐ⁰) (hint : ∀ r, ν (f r) ≤ 1) : Ideal R where
  carrier := {r | ν (f r) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact (ν.map_add _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, ν.map_mul] at hx ⊢
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint c)) hx

theorem mem_valCentre (f : R →+* L) (ν : Valuation L ℤᵐ⁰) (hint : ∀ r, ν (f r) ≤ 1) (r : R) :
    r ∈ valCentre f ν hint ↔ ν (f r) < 1 := Iff.rfl

instance valCentre_isPrime (f : R →+* L) (ν : Valuation L ℤᵐ⁰) (hint : ∀ r, ν (f r) ≤ 1) :
    (valCentre f ν hint).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : (1 : R) ∈ valCentre f ν hint := htop ▸ Submodule.mem_top
    rw [mem_valCentre, map_one, ν.map_one] at h1
    exact lt_irrefl _ h1
  · intro a b hab
    rw [mem_valCentre, map_mul, ν.map_mul] at hab
    by_contra h
    rw [not_or] at h
    have ha : ν (f a) = 1 := le_antisymm (hint a) (not_lt.1 fun h' => h.1 h')
    have hb : ν (f b) = 1 := le_antisymm (hint b) (not_lt.1 fun h' => h.2 h')
    rw [ha, hb, one_mul] at hab
    exact lt_irrefl _ hab

theorem zm_pow_le_one {x : ℤᵐ⁰} {e : ℕ} (he : e ≠ 0) : x ^ e ≤ 1 ↔ x ≤ 1 := by
  constructor
  · intro h; by_contra hx; exact absurd h (not_le.2 (one_lt_pow' (not_le.1 hx) he))
  · intro h; exact pow_le_one' h e

theorem zm_pow_lt_one {x : ℤᵐ⁰} {e : ℕ} (he : e ≠ 0) : x ^ e < 1 ↔ x < 1 := by
  constructor
  · intro h; by_contra hx; exact absurd h (not_lt.2 (one_le_pow_of_one_le' (not_lt.1 hx) e))
  · intro h; exact pow_lt_one' h he

end ValCentre

section Budget

variable {K : Type} [Field K] {E : Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

local notation "w" => RCN326.w

/-- The generic slice coefficient map `K[X] → E`. -/
noncomputable abbrev phiE (K E : Type) [Field K] [Field E] [Algebra (GenericField K) E] :
    Polynomial K →+* E :=
  (algebraMap (GenericField K) E).comp (polynomialEmbedding K)

section Images

variable (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (F₀ : MvPolynomial (Fin 4) K)
  [Fact (Irreducible F₀)] (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀})

omit [IsAlgClosed E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_coord (j : Fin 3) :
    sliceEmbedding D F₀ hker (sliceCoord F₀ j) = coordinate E D j := by
  rw [sliceCoord, sliceEmbedding_proj, sliceMap, RingHom.comp_apply, surfaceMap_X_succ]
  rfl

omit [IsAlgClosed E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_const (a : K) :
    sliceEmbedding D F₀ hker (algebraMap K (SliceField F₀) a) =
      algebraMap E (CoordinateField E D) (phiE K E (Polynomial.C a)) := by
  rw [← sliceProj_C, sliceEmbedding_proj, sliceMap, RingHom.comp_apply, surfaceMap_C]
  exact (coordinateEvaluation E D).commutes _

omit [IsAlgClosed E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_X0 :
    sliceEmbedding D F₀ hker (sliceProj F₀ (MvPolynomial.X 0)) =
      algebraMap E (CoordinateField E D) (phiE K E Polynomial.X) := by
  rw [sliceEmbedding_proj, sliceMap, RingHom.comp_apply, surfaceMap_X_zero]
  exact (coordinateEvaluation E D).commutes _

omit [IsAlgClosed E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E] in
theorem psi_sigma (F : MvPolynomial (Fin 4) K) :
    sliceEmbedding D F₀ hker (sliceSigma F F₀) =
      RCN064.movingRatio D (surfaceMap (phiE K E) (polyH K F))
        (surfaceMap (phiE K E) (polyG K F)) := by
  rw [sliceSigma, map_div₀, sliceEmbedding_proj, sliceEmbedding_proj]
  rfl

end Images

theorem scale_target (e : ℤ) (he : 0 ≤ e) (a b c d : ℤ) :
    max (2 * max (e * a) (max (e * b) (e * c))) (max (e * b) (e * c) + e * d) =
      e * max (2 * max a (max b c)) (max b c + d) := by
  rw [mul_max_of_nonneg _ _ he, mul_add, mul_left_comm e 2, mul_max_of_nonneg _ _ he,
    mul_max_of_nonneg _ _ he]

theorem scale_flag (e : ℤ) (he : 0 ≤ e) (a b c : ℤ) :
    max (e * a) (max (e * b) (e * c)) = e * max a (max b c) := by
  rw [mul_max_of_nonneg _ _ he, mul_max_of_nonneg _ _ he]







end Budget

end ProximityPrize.SubmissionLower.HFree6812


