-- Prove2me | Definitions.Def_SourceProof_c5c83cf022c9fd5765bb05bb
-- name    : SourceProof_c5c83cf022c9fd5765bb05bb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T13:13:44.660308+00:00
-- url     : https://prove2.me/theorems/c48d8af9-2fbe-4297-848c-d1de1f97f8d0
-- title:
--   LevyStochCalc source module: SourceProof_c5c83cf022c9fd5765bb05bb
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Continuity.brownian_continuous_modification_kol_aux` comes from the `LevyStochCalc.Brownian.Continuity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F001
import Definitions.Def_SourceProof_30c2a27da1025349f8d2b70b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Kolmogorov-Chentsov continuous modification

Mathlib has only `IsKolmogorovProcess` (the *condition*); the modification
result is missing. We port the classical proof (Karatzas-Shreve §2.2 Thm 2.8 /
Le Gall 2016 Thm 2.9):

  *If `(X_t)_{t ≥ 0}` satisfies `𝔼[ |X_t − X_s|^p ] ≤ M · |t − s|^q` for some
  `p, q > 0` with `q > 1` and constant `M`, then there exists a modification
  `X̃` with continuous paths.*

The sub-lemmas of the proof live in two imported modules of the same namespace:
`LevyStochCalc.Brownian.ContinuityDyadicChaining` (Hölder extension from a dense
set, the dyadic rationals, dyadic truncation and the deterministic chaining
bound) and `LevyStochCalc.Brownian.ContinuityKolmogorovBounds` (the Markov tail
bound, the per-level Borel-Cantelli estimates, almost-sure local Hölder
regularity and the modification identity). This module assembles them into
`kolmogorovChentsov_modification` and applies it to Brownian motion, whose
fourth increment moment is computed here from the Gaussian moment generating
function.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_c5c83cf022c9fd5765bb05bb
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ)
    (h_meas : ∀ s : ℝ, Measurable (X s))
    (h_increment : ∀ {s t : ℝ} (hst : s < t),
       P.map (fun ω => X t ω - X s ω)
         = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩)
    {s t : ℝ} (hst : s < t) :
    ∫⁻ ω, edist (X s ω) (X t ω) ^ 4 ∂P ≤ 3 * edist s t ^ 2 := by
  have h_pow_abs : ∀ x : ℝ, |x|^4 = x^4 := fun x => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have h_edist_pow : ∀ ω, edist (X s ω) (X t ω) ^ 4
      = ENNReal.ofReal ((X s ω - X t ω)^4) := by
    intro ω
    rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _), h_pow_abs]
  have h_meas_diff : Measurable (fun ω => X t ω - X s ω) :=
    (h_meas t).sub (h_meas s)
  have h_neg_pow : ∀ ω, (X s ω - X t ω)^4 = (X t ω - X s ω)^4 := fun ω => by ring
  rw [show (∫⁻ ω, edist (X s ω) (X t ω) ^ 4 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((X t ω - X s ω)^4) ∂P from
      by apply lintegral_congr; intro ω; rw [h_edist_pow ω, h_neg_pow ω]]
  rw [show (∫⁻ ω, ENNReal.ofReal ((X t ω - X s ω)^4) ∂P)
       = ∫⁻ y, ENNReal.ofReal (y^4) ∂(P.map (fun ω => X t ω - X s ω)) from
      by rw [lintegral_map (by fun_prop) h_meas_diff]]
  rw [h_increment hst]
  set v : NNReal := ⟨t - s, by linarith⟩ with hv_def
  have h_v_eq : (v : ℝ) = t - s := rfl
  have h_int : MeasureTheory.Integrable (fun x : ℝ => x^4)
      (ProbabilityTheory.gaussianReal 0 v) := by
    have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 4
        (ProbabilityTheory.gaussianReal 0 v) :=
      ProbabilityTheory.IsGaussian.memLp_id
        (ProbabilityTheory.gaussianReal 0 v) 4 (by simp)
    have h := h_memLp.integrable_norm_pow (p := 4) (by norm_num)
    convert h using 1
    ext x
    change x^4 = ‖x‖^4
    rw [Real.norm_eq_abs, h_pow_abs]
  have h_nn : 0 ≤ᵐ[ProbabilityTheory.gaussianReal 0 v] fun x : ℝ => x^4 := by
    filter_upwards with x
    positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nn]
  rw [_root_.Prove2MeSourceProof.h_30c2a27da1025349f8d2b70b v, h_v_eq]
  have h_edist_st : edist s t = ENNReal.ofReal (t - s) := by
    rw [edist_dist, Real.dist_eq]
    congr 1
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hst)]
  rw [h_edist_st]
  rw [show (3 : ENNReal) = ENNReal.ofReal 3 from by
    rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num : (0 : ℝ) ≤ 3)]
    norm_cast]
  rw [← ENNReal.ofReal_pow (sub_nonneg.mpr (le_of_lt hst))]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
end LevyStochCalc.Brownian.Continuity


