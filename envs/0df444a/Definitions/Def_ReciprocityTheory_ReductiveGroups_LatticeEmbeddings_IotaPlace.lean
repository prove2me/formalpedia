-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlace
-- name    : ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlace
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:36:49.399348+00:00
-- url     : https://prove2.me/theorems/683beb0b-8fa9-451d-beb9-ca976bad6fc2
-- title:
--   Iota Place
-- statement:
--   Definitions and structural lemmas for Iota Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/LatticeEmbeddings/IotaPlace.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlaceB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
namespace ReciprocityTheory.ChartRestriction.B3.IotaPl
theorem norm_le_one_of_isIntegral_int {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨f, hf, hfx⟩ := hx
  set n := f.natDegree with hn
  have hsum := hf.as_sum
  rw [hsum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at hfx
  have key : x ^ n = -∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap ℤ ℂ_[p]) x (Polynomial.C (f.coeff i) * Polynomial.X ^ i) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hfx
  have hx1 : 1 ≤ ‖x‖ := hlt.le
  have bound : ‖∑ i ∈ Finset.range n,
      Polynomial.eval₂ (algebraMap ℤ ℂ_[p]) x (Polynomial.C (f.coeff i) * Polynomial.X ^ i)‖ ≤
        ‖x‖ ^ (n - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
    have hc : ‖(algebraMap ℤ ℂ_[p]) (f.coeff i)‖ ≤ 1 := by
      have h := IsUltrametricDist.norm_intCast_le_one ℂ_[p] (f.coeff i)
      first
        | (simpa using h)
        | (rw [algebraMap_int_eq, eq_intCast]; exact h)
        | (convert h using 2; exact (algebraMap ℤ ℂ_[p]).eq_intCast _)
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖(algebraMap ℤ ℂ_[p]) (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (n - 1) :=
          mul_le_mul hc (pow_le_pow_right₀ hx1 hi') (by positivity) zero_le_one
      _ = ‖x‖ ^ (n - 1) := one_mul _
  have h2 : ‖x‖ ^ n ≤ ‖x‖ ^ (n - 1) := by
    rw [← norm_pow, key, norm_neg]
    exact bound
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at key
    simp at key
  · have h3 : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ hlt (by omega)
    linarith
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
theorem norm_int_le (ι : K →+* ℂ_[p]) (y : 𝓞 K) : ‖ι (y : K)‖ ≤ 1 := by
  obtain ⟨f, hf, hfy⟩ := NumberField.RingOfIntegers.isIntegral_coe y
  refine norm_le_one_of_isIntegral_int ⟨f, hf, ?_⟩
  have e : (algebraMap ℤ ℂ_[p]) = ι.comp (algebraMap ℤ K) := RingHom.ext_int _ _
  rw [e, ← Polynomial.hom_eval₂, hfy, map_zero]
def smallIdeal (ι : K →+* ℂ_[p]) : Ideal (𝓞 K) where
  carrier := {y | ‖ι (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : ι ((a + b : 𝓞 K) : K) = ι (a : K) + ι (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : ι ((c • a : 𝓞 K) : K) = ι (c : K) * ι (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le ι c
    nlinarith [norm_nonneg (ι (c : K)), norm_nonneg (ι (a : K))]
def vAdd (w : HeightOneSpectrum (𝓞 K)) (a : K) : ℤ :=
  FractionalIdeal.count K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a)
end ReciprocityTheory.ChartRestriction.B3.IotaPl
namespace ReciprocityTheory.ChartRestriction.B3
end ReciprocityTheory.ChartRestriction.B3


