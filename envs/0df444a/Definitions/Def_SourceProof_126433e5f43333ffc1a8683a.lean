-- Prove2me | Definitions.Def_SourceProof_126433e5f43333ffc1a8683a
-- name    : SourceProof_126433e5f43333ffc1a8683a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:00:54.288152+00:00
-- url     : https://prove2.me/theorems/da4dc4cb-66ed-4cb6-b0ba-eb1c1184b4c0
-- title:
--   LevyStochCalc source module: SourceProof_126433e5f43333ffc1a8683a
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral_mul_stepIntegral_mul` comes from the `LevyStochCalc.Poisson.ProfileExpPairingSimple` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairingSimple_F000

open private integral_exp_stepIntegral_mul_compensated_mul sum_sum_pairing from Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairingSimple_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character of a compensated step integral against first- and second-order elements

For a simple mark profile with pairwise disjoint mark sets `B_k` of finite intensity, the
compensated counts `Ñ_k` of the strips `(a, b] × B_k` are independent, so the character
`e^{iuJ_c}` of the compensated step integral `J_c = ∑_k c_k Ñ_k` carried by a coefficient vector
`c` factors over the strips. Each factor pairs with `Ñ_k` and `Ñ_k²` through the identities of
`Poisson/CompensatedCountCharacter.lean`, with `λ_k = (b − a) ν(B_k)`:
`E[e^{isÑ} Ñ] = λ (e^{is} − 1) E[e^{isÑ}]` and
`E[e^{isÑ} Ñ²] = (λ² (e^{is} − 1)² + λ e^{is}) E[e^{isÑ}]`. Summing over the strips gives, for
coefficient vectors `d, d'` on the same mark sets and `γ_k = e^{iuc_k} − 1`,

  `E[e^{iuJ_c} J_d] = (b − a) ∑_k ν(B_k) γ_k d_k · E[e^{iuJ_c}]`,

and the matching second-order identity for `E[e^{iuJ_c} J_d J_{d'}]`. On a common refinement of
finitely many simple profiles these become the pairings of the character of the compensated
integral of one simple profile `G` with the compensated integrals of others, with
`γ = e^{iuG} − 1`:

  `E[e^{iuJ(G)} J(F)] = (b − a) ∫ γ F dν · E[e^{iuJ(G)}]`,
  `E[e^{iuJ(G)} J(F) J(K)]`
  `  = ((b − a)² ∫ γ F dν ∫ γ K dν + (b − a) (∫ γ F K dν + ∫ F K dν)) · E[e^{iuJ(G)}]`.

## Main statements

* `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral_mul_stepIntegral`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral_mul_stepIntegral_mul` —
  the first- and second-order pairings on the mark sets of one simple profile.
* `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_compensatedProfile_mul`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_compensatedProfile_mul_mul` — the
  first- and second-order pairings at simple mark profiles.
* `LevyStochCalc.Poisson.SimpleProfile.abs_toFun_le` — the function of a simple profile is bounded
  by the sum of the absolute values of its coefficients.
-/

open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Strips of a simple profile -/

namespace SimpleProfile

/-! ### Pairings on the mark sets of one simple profile -/


theorem _root_.Prove2MeSourceProof.h_126433e5f43333ffc1a8683a (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c d d' : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
        * (((H.withCoeff d).stepIntegral N a b ω : ℝ) : ℂ)
        * (((H.withCoeff d').stepIntegral N a b ω : ℝ) : ℂ) ∂P
      = (((b - a : ℝ) : ℂ) ^ 2 * (∑ k, ((ν (H.B k)).toReal : ℂ)
            * ((Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ)) - 1) * (d k : ℂ)))
          * (∑ k, ((ν (H.B k)).toReal : ℂ)
            * ((Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ)) - 1) * (d' k : ℂ)))
          + ((b - a : ℝ) : ℂ) * ((∑ k, ((ν (H.B k)).toReal : ℂ)
            * ((Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ)) - 1) * (d k : ℂ) * (d' k : ℂ)))
            + ∑ k, ((ν (H.B k)).toReal : ℂ) * ((d k : ℂ) * (d' k : ℂ))))
        * ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
          ∂P := by
  set χ := ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
    ∂P with hχ
  have hS := ((H.withCoeff c).memLp_stepIntegral N ha b).aestronglyMeasurable
  have hint : ∀ m l, Integrable (fun ω =>
      Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
        * ((N.compensated (Set.Ioc a b ×ˢ H.B m) ω : ℝ) : ℂ)
        * ((N.compensated (Set.Ioc a b ×ˢ H.B l) ω : ℝ) : ℂ)) P := fun m l => by
    simp_rw [mul_assoc]
    exact LevyStochCalc.Probability.integrable_exp_I_mul_mul u hS
      ((H.memLp_compensated_step N ha b m).ofReal.integrable_mul
        (H.memLp_compensated_step N ha b l).ofReal)
  have hpt : ∀ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
      * (((H.withCoeff d).stepIntegral N a b ω : ℝ) : ℂ)
      * (((H.withCoeff d').stepIntegral N a b ω : ℝ) : ℂ)
      = ∑ m, ∑ l, ((d m : ℂ) * (d' l : ℂ)) * (Complex.exp (Complex.I
        * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
          * ((N.compensated (Set.Ioc a b ×ˢ H.B m) ω : ℝ) : ℂ)
          * ((N.compensated (Set.Ioc a b ×ˢ H.B l) ω : ℝ) : ℂ)) := fun ω => by
    rw [LevyStochCalc.Poisson.SimpleProfile.stepIntegral_withCoeff N H d, LevyStochCalc.Poisson.SimpleProfile.stepIntegral_withCoeff N H d']
    push_cast
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun l _ => (hint m l).const_mul _]
  simp_rw [integral_finsetSum _ fun l _ => (hint _ l).const_mul _, integral_const_mul,
    integral_exp_stepIntegral_mul_compensated_mul N H c ha u,
    LevyStochCalc.Poisson.referenceIntensity_strip_toReal ha hab, ← hχ]
  refine (sum_sum_pairing (fun k => (d k : ℂ)) (fun k => (d' k : ℂ))
    (fun k => (((b - a) * (ν (H.B k)).toReal : ℝ) : ℂ)
      * (Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ)) - 1))
    (fun k => (((b - a) * (ν (H.B k)).toReal : ℝ) : ℂ)
      * Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ))) χ).trans ?_
  have h1 : ∀ x : Fin H.K → ℝ, ∑ k, (x k : ℂ) * ((((b - a) * (ν (H.B k)).toReal : ℝ) : ℂ)
      * (Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ)) - 1)) = ((b - a : ℝ) : ℂ) * ∑ k,
      ((ν (H.B k)).toReal : ℂ) * ((Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ)) - 1)
        * (x k : ℂ)) := fun x => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  have h2 : ∑ k, (d k : ℂ) * (d' k : ℂ) * ((((b - a) * (ν (H.B k)).toReal : ℝ) : ℂ)
      * Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ))) = ((b - a : ℝ) : ℂ) * ((∑ k,
      ((ν (H.B k)).toReal : ℂ) * ((Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ)) - 1)
        * (d k : ℂ) * (d' k : ℂ))) + ∑ k, ((ν (H.B k)).toReal : ℂ) * ((d k : ℂ) * (d' k : ℂ))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [h1 d, h1 d', h2]
  ring
/-! ### Simple mark profiles -/

end SimpleProfile

end LevyStochCalc.Poisson


