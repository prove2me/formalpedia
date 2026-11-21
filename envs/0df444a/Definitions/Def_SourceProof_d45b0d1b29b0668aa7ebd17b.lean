-- Prove2me | Definitions.Def_SourceProof_d45b0d1b29b0668aa7ebd17b
-- name    : SourceProof_d45b0d1b29b0668aa7ebd17b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:02:37.204428+00:00
-- url     : https://prove2.me/theorems/5e02a5bf-57ec-41b0-b2ce-37536df2acbc
-- title:
--   LevyStochCalc source module: SourceProof_d45b0d1b29b0668aa7ebd17b
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_compensatedProfile_mul_mul` comes from the `LevyStochCalc.Poisson.ProfileExpPairingSimple` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairingSimple_F000
import Definitions.Def_SourceProof_126433e5f43333ffc1a8683a

open private integral_withCoeff_three from Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairingSimple_F000
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

/-! ### Simple mark profiles -/


theorem _root_.Prove2MeSourceProof.h_d45b0d1b29b0668aa7ebd17b (N : PoissonRandomMeasure P ν)
    (G F K : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N G.toFun a b ω : ℝ) : ℂ))
        * (compensatedProfile N F.toFun a b ω : ℂ) * (compensatedProfile N K.toFun a b ω : ℂ) ∂P
      = (((b - a : ℝ) : ℂ) ^ 2
          * (∫ e, (Complex.exp (Complex.I * ((u * G.toFun e : ℝ) : ℂ)) - 1) * (F.toFun e : ℂ) ∂ν)
          * (∫ e, (Complex.exp (Complex.I * ((u * G.toFun e : ℝ) : ℂ)) - 1) * (K.toFun e : ℂ) ∂ν)
          + ((b - a : ℝ) : ℂ)
            * ((∫ e, (Complex.exp (Complex.I * ((u * G.toFun e : ℝ) : ℂ)) - 1) * (F.toFun e : ℂ)
                * (K.toFun e : ℂ) ∂ν) + ∫ e, (F.toFun e : ℂ) * (K.toFun e : ℂ) ∂ν))
        * ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N G.toFun a b ω : ℝ) : ℂ)) ∂P := by
  obtain ⟨H, dd, hdd⟩ := _root_.Prove2MeSourceProof.h_4bd0a8161788e04ae47801f3 ![G, F, K]
  rw [show G.toFun = (H.withCoeff (dd 0)).toFun from funext fun e => (hdd 0 e).symm,
    show F.toFun = (H.withCoeff (dd 1)).toFun from funext fun e => (hdd 1 e).symm,
    show K.toFun = (H.withCoeff (dd 2)).toFun from funext fun e => (hdd 2 e).symm]
  have h0 := _root_.Prove2MeSourceProof.h_42f85278a4a3a35e73d229e1 N (H.withCoeff (dd 0)) ha hab
  have h1 := _root_.Prove2MeSourceProof.h_42f85278a4a3a35e73d229e1 N (H.withCoeff (dd 1)) ha hab
  have h2 := _root_.Prove2MeSourceProof.h_42f85278a4a3a35e73d229e1 N (H.withCoeff (dd 2)) ha hab
  have hχ : ∫ ω, Complex.exp (Complex.I
      * ((u * LevyStochCalc.Poisson.compensatedProfile N (H.withCoeff (dd 0)).toFun a b ω : ℝ) : ℂ)) ∂P
      = ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff (dd 0)).stepIntegral N a b ω : ℝ) : ℂ))
        ∂P := integral_congr_ae (by filter_upwards [h0] with ω e0; rw [e0])
  rw [hχ, integral_congr_ae (by filter_upwards [h0, h1, h2] with ω e0 e1 e2; rw [e0, e1, e2]),
    _root_.Prove2MeSourceProof.h_126433e5f43333ffc1a8683a N H (dd 0) (dd 1) (dd 2) ha hab u]
  have hν1 := integral_withCoeff_three H (dd 0) (dd 1) (dd 1)
    (fun x y _ => (Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) - 1) * (y : ℂ)) (by simp)
  have hν2 := integral_withCoeff_three H (dd 0) (dd 2) (dd 2)
    (fun x y _ => (Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) - 1) * (y : ℂ)) (by simp)
  have hν3 := integral_withCoeff_three H (dd 0) (dd 1) (dd 2)
    (fun x y w => (Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) - 1) * (y : ℂ) * (w : ℂ))
    (by simp)
  have hν4 := integral_withCoeff_three H (dd 0) (dd 1) (dd 2)
    (fun _ y w => (y : ℂ) * (w : ℂ)) (by simp)
  rw [hν1, hν2, hν3, hν4]
end SimpleProfile

end LevyStochCalc.Poisson


