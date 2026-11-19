-- Prove2me | Definitions.Def_LevyStochCalc_Analysis_GronwallIterate_F000
-- name    : LevyStochCalc_Analysis_GronwallIterate_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:56:25.539421+00:00
-- url     : https://prove2.me/theorems/241a5e22-6b79-4a1f-9b70-ecbf63f6fb44
-- title:
--   Source declarations: LevyStochCalc.Analysis.GronwallIterate
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Analysis.GronwallIterate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Grönwall by iteration

A bounded function on `[0, T]` whose norm is dominated by a constant multiple of the running
integral of its norm vanishes: iterating the bound `n` times gives `C (K t)^n / n!`, which tends
to zero. No continuity, no derivative and no partition of `[0, T]` is needed.
-/

open MeasureTheory intervalIntegral Filter
open scoped Topology

namespace LevyStochCalc.Analysis

variable {F : Type*} [NormedAddCommGroup F]

/-- The `n`-fold iterate of an integral bound on the norm. -/
theorem norm_le_pow_div_factorial_of_norm_le_integral {u : ℝ → F} {T K C : ℝ}
    (hK : 0 ≤ K) (hint : IntegrableOn (fun s => ‖u s‖) (Set.Icc 0 T))
    (hbdd : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u t‖ ≤ C)
    (hle : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u t‖ ≤ K * ∫ s in (0 : ℝ)..t, ‖u s‖) (n : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u t‖ ≤ C * (K * t) ^ n / n.factorial := by
  induction n with
  | zero => intro t ht; simpa using hbdd t ht
  | succ n ih =>
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hII : IntervalIntegrable (fun s => ‖u s‖) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0).mpr
        (hint.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2)))
    have hpoly : IntervalIntegrable (fun s : ℝ => C * (K * s) ^ n / n.factorial) volume 0 t :=
      (by fun_prop : Continuous fun s : ℝ => C * (K * s) ^ n / n.factorial).intervalIntegrable 0 t
    have hmono : ∫ s in (0 : ℝ)..t, ‖u s‖
        ≤ ∫ s in (0 : ℝ)..t, C * (K * s) ^ n / n.factorial :=
      integral_mono_on ht0 hII hpoly fun s hs => ih s ⟨hs.1, hs.2.trans ht.2⟩
    have hval : ∫ s in (0 : ℝ)..t, C * (K * s) ^ n / n.factorial
        = C * K ^ n / n.factorial * (t ^ (n + 1) / (n + 1)) := by
      have hfun : (fun s : ℝ => C * (K * s) ^ n / n.factorial)
          = fun s => (C * K ^ n / n.factorial) * s ^ n := by
        funext s; rw [mul_pow]; ring
      rw [hfun, intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero n),
        sub_zero]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    calc ‖u t‖ ≤ K * ∫ s in (0 : ℝ)..t, ‖u s‖ := hle t ht
      _ ≤ K * (C * K ^ n / n.factorial * (t ^ (n + 1) / (n + 1))) := by
          rw [← hval]; exact mul_le_mul_of_nonneg_left hmono hK
      _ = C * (K * t) ^ (n + 1) / (n + 1).factorial := by
          rw [Nat.factorial_succ, mul_pow]; push_cast; field_simp; ring
/-- **Grönwall by iteration.** A function on `[0, T]` that is bounded, has integrable norm, and
whose norm is dominated by a constant multiple of its own running integral vanishes on `[0, T]`. -/
theorem eq_zero_of_norm_le_integral {u : ℝ → F} {T K C : ℝ}
    (hK : 0 ≤ K) (hint : IntegrableOn (fun s => ‖u s‖) (Set.Icc 0 T))
    (hbdd : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u t‖ ≤ C)
    (hle : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u t‖ ≤ K * ∫ s in (0 : ℝ)..t, ‖u s‖) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, u t = 0 := by
  intro t ht
  have hbound : ∀ n : ℕ, ‖u t‖ ≤ C * ((K * t) ^ n / n.factorial) := fun n => by
    have := norm_le_pow_div_factorial_of_norm_le_integral hK hint hbdd hle n t ht
    rwa [mul_div_assoc] at this
  have hlim : Tendsto (fun n : ℕ => C * ((K * t) ^ n / n.factorial)) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (K * t)).const_mul C
  exact norm_le_zero_iff.mp (ge_of_tendsto' hlim hbound)
end LevyStochCalc.Analysis


