-- Prove2me | Definitions.Def_BS2_b3ba934b_EndpointReduction
-- name    : BS2_b3ba934b_EndpointReduction
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:47:04.949071+00:00
-- url     : https://prove2.me/theorems/c73d6577-b37e-4bf4-968c-57662aad6144
-- title:
--   Sensitivity separation: EndpointReduction (complete source module)
-- statement:
--   Complete Lean source module `EndpointReduction` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/EndpointReduction.lean; original SHA-256 de30b8a2edfcd9ff563e9aac46d3fbf7ff892bcc756d3acc8fa042480e7fb56e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Conditional endpoint reductions for the three requested bounds.

This file does NOT prove the recursive seed construction. Its `hseed`
hypotheses are explicit, and none is asserted as an axiom or hidden import.
The logarithmic inequalities and asymptotic conversion are proved here.

The conversion proof adapts the accepted Apache-2.0 proof by @yousofy:
https://prove2.me/submissions/b04cd290-40bc-4809-a2e0-ffb0e70acd04
The shared definitions are the campaign's Definitions.Def_SensitivityCampaign
and Definitions.Def_SensitivitySeparation, with unchanged definition bodies.
-/
import Definitions.Def_SensitivityCampaign
import Definitions.Def_BS2_b3ba934b_IntegerComparisons
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option Elab.async false

namespace ThreeBoundEndpoint
open OAI.Paper320

/-- The campaign predicate is downward closed in its exponent. -/
theorem achieves_mono {a b : ℝ} (hab : a ≤ b)
    (hb : SensitivityCampaign.AchievesExponent b) :
    SensitivityCampaign.AchievesExponent a := by
  intro ε hε S hS
  obtain ⟨n, f, hSf, hf⟩ := hb (ε + (b - a)) (by linarith) S hS
  refine ⟨n, f, hSf, ?_⟩
  convert hf using 1 <;> congr 1 <;> ring

/-- Translate a kernel-verified integer comparison into the logarithmic exponent. -/
theorem exponent_lt_of_power_comparison (g r p q : ℕ) (hr : 1 < r)
    (hq : 0 < q) (hpow : r^p < g^q) :
    (p : ℝ) / q < Real.log (g : ℝ) / Real.log (r : ℝ) := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hrp : (0 : ℝ) < r := by linarith
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hcast : (r : ℝ)^p < (g : ℝ)^q := by exact_mod_cast hpow
  have hlog := Real.log_lt_log (pow_pos hrp p) hcast
  rw [Real.log_pow, Real.log_pow] at hlog
  apply (lt_div_iff₀ (Real.log_pos hr1)).2
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hqp).2
  nlinarith

theorem bound_213303_strict :
    (213303 : ℝ) / 100000 < 4 * Real.log 10007 / Real.log 31739938 := by
  have h := exponent_lt_of_power_comparison (10007^4) 31739938 213303 100000
    (by norm_num) (by norm_num) ThreeBoundArithmetic.comparison_213303
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h

theorem bound_213519_strict :
    (213519 : ℝ) / 100000 < 4 * Real.log 10007 / Real.log 31192129 := by
  have h := exponent_lt_of_power_comparison (10007^4) 31192129 213519 100000
    (by norm_num) (by norm_num) ThreeBoundArithmetic.comparison_213519
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h

theorem bound_213981_strict :
    (213981 : ℝ) / 100000 < 4 * Real.log 5591 / Real.log 10121928 := by
  have h := exponent_lt_of_power_comparison (5591^4) 10121928 213981 100000
    (by norm_num) (by norm_num) ThreeBoundArithmetic.comparison_213981
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h

/-- A concrete Boolean seed family is sufficient for an asymptotic exponent.
    The seed family is a hypothesis, not proved by this lemma. -/
theorem achieves_strict_from_seeds (c r g t : ℕ) (β : ℝ)
    (hc : 1 < c) (hr : 1 < r) (hg : 1 < g) (ht : 1 < t)
    (hβ : 0 ≤ β)
    (hstrict : β < Real.log (g : ℝ) / Real.log (r : ℝ))
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      t^m ≤ sensitivity f ∧ sensitivity f ≤ c*r^m ∧ g^m ≤ blockSensitivity f) :
    SensitivityCampaign.AchievesExponent β := by
  have hcp : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hrp : (0 : ℝ) < r := by linarith
  have hgp : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hlr : 0 < Real.log (r : ℝ) := Real.log_pos hr1
  let δ := Real.log (g : ℝ) - β * Real.log (r : ℝ)
  have hgap : 0 < δ := by
    have hh := (lt_div_iff₀ hlr).mp hstrict
    dsimp only [δ]
    linarith
  intro ε hε S hS
  obtain ⟨m, hm⟩ := exists_nat_gt (max (S : ℝ) (β * Real.log (c : ℝ) / δ))
  have hmS : S < m := by exact_mod_cast ((le_max_left _ _).trans_lt hm)
  have hmul : β * Real.log (c : ℝ) < (m : ℝ) * δ :=
    (div_lt_iff₀ hgap).mp ((le_max_right _ _).trans_lt hm)
  obtain ⟨n, f, hlower, hs, hb⟩ := hseed m
  have hSle : S ≤ sensitivity f :=
    (Nat.le_of_lt hmS).trans ((Nat.le_of_lt (Nat.lt_pow_self ht)).trans hlower)
  refine ⟨n, f, hSle, ?_⟩
  have hbase : (1 : ℝ) ≤ sensitivity f := by
    exact_mod_cast (show 1 ≤ sensitivity f by omega)
  have hApos : (0 : ℝ) < (c*r^m : ℕ) := by
    exact_mod_cast (Nat.mul_pos (by omega : 0 < c) (Nat.pow_pos (by omega : 0 < r)))
  have hBpos : (0 : ℝ) < (g^m : ℕ) := by
    exact_mod_cast (Nat.pow_pos (by omega : 0 < g) : 0 < g^m)
  have hpow : ((c*r^m : ℕ) : ℝ)^β ≤ ((g^m : ℕ) : ℝ) := by
    apply (Real.rpow_le_iff_le_log hApos hBpos).2
    push_cast
    rw [Real.log_mul (ne_of_gt hcp) (ne_of_gt (pow_pos hrp m)),
      Real.log_pow, Real.log_pow]
    dsimp only [δ] at hmul
    nlinarith
  calc
    (sensitivity f : ℝ)^(β-ε) ≤ (sensitivity f : ℝ)^β :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    _ ≤ ((c*r^m : ℕ) : ℝ)^β :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hs) hβ
    _ ≤ ((g^m : ℕ) : ℝ) := hpow
    _ ≤ (blockSensitivity f : ℝ) := by exact_mod_cast hb

theorem reach_213303_of_seeds (c : ℕ) (hc : 1 < c)
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      16^m ≤ sensitivity f ∧ sensitivity f ≤ c*31739938^m ∧
        (10007^4)^m ≤ blockSensitivity f) :
    SensitivityCampaign.AchievesExponent ((213303 : ℝ)/100000) := by
  apply achieves_strict_from_seeds c 31739938 (10007^4) 16
    ((213303 : ℝ)/100000) hc (by norm_num) (by norm_num) (by norm_num)
    (by positivity) ?_ hseed
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using bound_213303_strict

theorem reach_213519_of_seeds (c : ℕ) (hc : 1 < c)
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      16^m ≤ sensitivity f ∧ sensitivity f ≤ c*31192129^m ∧
        (10007^4)^m ≤ blockSensitivity f) :
    SensitivityCampaign.AchievesExponent ((213519 : ℝ)/100000) := by
  apply achieves_strict_from_seeds c 31192129 (10007^4) 16
    ((213519 : ℝ)/100000) hc (by norm_num) (by norm_num) (by norm_num)
    (by positivity) ?_ hseed
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using bound_213519_strict

theorem reach_213981_of_seeds
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      16^m ≤ sensitivity f ∧ sensitivity f ≤ 1531448*10121928^m ∧
        (5591^4)^m ≤ blockSensitivity f) :
    SensitivityCampaign.AchievesExponent ((213981 : ℝ)/100000) := by
  apply achieves_strict_from_seeds 1531448 10121928 (5591^4) 16
    ((213981 : ℝ)/100000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) ?_ hseed
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using bound_213981_strict

/-- Any fixed integer prefactor gives the same asymptotic result.
    In particular one may use the unnormalized integer vector's prefactor. -/
theorem reach_213981_of_seeds_with_prefactor (c : ℕ) (hc : 1 < c)
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      16^m ≤ sensitivity f ∧ sensitivity f ≤ c*10121928^m ∧
        (5591^4)^m ≤ blockSensitivity f) :
    SensitivityCampaign.AchievesExponent ((213981 : ℝ)/100000) := by
  apply achieves_strict_from_seeds c 10121928 (5591^4) 16
    ((213981 : ℝ)/100000) hc (by norm_num) (by norm_num) (by norm_num)
    (by positivity) ?_ hseed
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using bound_213981_strict

end ThreeBoundEndpoint

#print axioms ThreeBoundEndpoint.achieves_mono
#print axioms ThreeBoundEndpoint.bound_213303_strict
#print axioms ThreeBoundEndpoint.bound_213519_strict
#print axioms ThreeBoundEndpoint.bound_213981_strict
#print axioms ThreeBoundEndpoint.reach_213303_of_seeds
#print axioms ThreeBoundEndpoint.reach_213519_of_seeds
#print axioms ThreeBoundEndpoint.reach_213981_of_seeds
#print axioms ThreeBoundEndpoint.reach_213981_of_seeds_with_prefactor


