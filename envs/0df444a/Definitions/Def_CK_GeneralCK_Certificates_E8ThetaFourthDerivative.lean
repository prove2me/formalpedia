-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ThetaFourthDerivative
-- name    : CK_GeneralCK_Certificates_E8ThetaFourthDerivative
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:02:45.605771+00:00
-- url     : https://prove2.me/theorems/d4aceebe-a4bf-407b-b969-6ffdbe7697cd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ThetaFourthDerivative` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ThetaFourthDerivative` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ThetaFourthDerivative` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ThetaFourthDerivative (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ThetaFourthDerivative.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaThirdDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv

-- ===== source module GeneralCK.Certificates.E8ThetaFourthDerivative =====
section

/-! Bootstrap of the radial-contact smoothness needed for the fourth E8
Theta derivative. -/

namespace GeneralCK

open Set Filter

private theorem contDiffAt_succ_of_eventually_hasDerivAt
    {n : ℕ} {f g : ℝ → ℝ} {x : ℝ}
    (hd : ∀ᶠ y in nhds x, HasDerivAt f (g y) y)
    (hg : ContDiffAt ℝ n g x) : ContDiffAt ℝ (n+1) f x := by
  rw [contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨fun y => ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ) (g y), ?_, ?_⟩
  · exact ⟨{y | HasDerivAt f (g y) y}, hd, fun y hy => hy.hasFDerivAt⟩
  · fun_prop

noncomputable def radialRhs (z : ℝ) : ℝ :=
  -H (radialContact z 1) / (z*J (radialContact z 1)+2)

theorem contDiffAt_H {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    ContDiffAt ℝ ⊤ H v := by
  unfold H Real.binEntropy
  fun_prop (disch := positivity)

theorem contDiffAt_J {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    ContDiffAt ℝ ⊤ J v := by
  unfold J
  fun_prop (disch := positivity)

private theorem contDiffAt_radialRhs_of_radial {n : ℕ} {z : ℝ} (hz : 0 < z)
    (hr : ContDiffAt ℝ n (fun r => radialContact r 1) z) :
    ContDiffAt ℝ n radialRhs z := by
  let v := radialContact z 1
  have hv : 0 < v := radialContact_pos hz (by norm_num)
  have hvh : v < 1/2 := radialContact_lt_half hz (by norm_num)
  have hH := (contDiffAt_H hv (by linarith)).of_le (m := n) (by simp)
  have hJ := (contDiffAt_J hv (by linarith)).of_le (m := n) (by simp)
  have hden : z*J v+2 ≠ 0 :=
    by simpa [v] using
      (radialContact_denominator_pos (z := z) (h := 1) hz (by norm_num)).ne'
  unfold radialRhs
  fun_prop (disch := first | assumption | positivity)

private theorem eventually_hasDerivAt_radialRhs {z : ℝ} (hz : 0 < z) :
    ∀ᶠ y in nhds z, HasDerivAt (fun r => radialContact r 1) (radialRhs y) y := by
  filter_upwards [Ioi_mem_nhds hz] with y hy
  simpa [radialRhs] using hasDerivAt_radialContact_radius hy (by norm_num : (0:ℝ)<1)

theorem contDiffAt_radialContact_three {z : ℝ} (hz : 0 < z) :
    ContDiffAt ℝ 3 (fun r => radialContact r 1) z := by
  have h0 : ContDiffAt ℝ 0 (fun r => radialContact r 1) z := by
    rw [contDiffAt_zero]
    exact ⟨Ioi 0, Ioi_mem_nhds hz,
      fun y hy => (continuousAt_radialContact_radius hy (by norm_num)).continuousWithinAt⟩
  have hg0 := contDiffAt_radialRhs_of_radial hz h0
  have h1 := contDiffAt_succ_of_eventually_hasDerivAt
    (eventually_hasDerivAt_radialRhs hz) hg0
  have hg1 := contDiffAt_radialRhs_of_radial hz h1
  have h2 := contDiffAt_succ_of_eventually_hasDerivAt
    (eventually_hasDerivAt_radialRhs hz) hg1
  have hg2 := contDiffAt_radialRhs_of_radial hz h2
  exact contDiffAt_succ_of_eventually_hasDerivAt
    (eventually_hasDerivAt_radialRhs hz) hg2

theorem contDiffAt_thetaSecondFormula_three {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ 3 thetaSecondFormula x := by
  let v := radialContact (2*x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1/2 := radialContact_lt_half (by positivity) (by norm_num)
  have hlin : ContDiffAt ℝ 3 (fun u : ℝ => 2*u) x := by fun_prop
  have hrc : ContDiffAt ℝ 3 (fun u : ℝ => radialContact (2*u) 1) x := by
    simpa [Function.comp_def] using
      (contDiffAt_radialContact_three (z := 2*x) (by positivity)).comp x hlin
  have hpTop := contDiffAt_profile hv hvh
  have hp3 := hpTop.of_le (m := 3) (by simp)
  have hdp3 := hpTop.derivWithin (m := 3) (by simp)
  have hH3 := (contDiffAt_H hv (by linarith)).of_le (m := 3) (by simp)
  have hJ3 := (contDiffAt_J hv (by linarith)).of_le (m := 3) (by simp)
  have hpComp : ContDiffAt ℝ 3
      (fun u : ℝ => Certificates.Mixed.profile (radialContact (2*u) 1)) x := by
    simpa [Function.comp_def] using hp3.comp x hrc
  have hdpComp : ContDiffAt ℝ 3
      (fun u : ℝ => deriv Certificates.Mixed.profile (radialContact (2*u) 1)) x := by
    simpa [Function.comp_def] using hdp3.comp x hrc
  have hHComp : ContDiffAt ℝ 3
      (fun u : ℝ => H (radialContact (2*u) 1)) x := by
    simpa [Function.comp_def] using hH3.comp x hrc
  have hJComp : ContDiffAt ℝ 3
      (fun u : ℝ => J (radialContact (2*u) 1)) x := by
    simpa [Function.comp_def] using hJ3.comp x hrc
  have hden : (2*x)*J v+2 ≠ 0 := by
    simpa [v] using
      (radialContact_denominator_pos (z := 2*x) (h := 1)
        (by positivity) (by norm_num)).ne'
  unfold thetaSecondFormula
  dsimp only
  fun_prop (disch := first | assumption | positivity)

theorem contDiffAt_thetaSecondFormula_two {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ 2 thetaSecondFormula x :=
  (contDiffAt_thetaSecondFormula_three hx).of_le (by norm_num)

theorem differentiableAt_deriv_thetaSecondFormula {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (deriv thetaSecondFormula) x := by
  have h := (contDiffAt_thetaSecondFormula_two hx).derivWithin
    (m := 1) (by norm_num)
  exact h.differentiableAt_one

/-- The d3→d4 link of the canonical `e8Theta` jet is unconditional. -/
theorem differentiableAt_deriv3_e8Theta {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (deriv (deriv (deriv e8Theta))) x := by
  have heq : deriv (deriv e8Theta) =ᶠ[nhds x] thetaSecondFormula := by
    filter_upwards [Ioi_mem_nhds hx] with u hu
    exact deriv2_e8Theta_eq_formula hu
  exact (differentiableAt_deriv_thetaSecondFormula hx).congr_of_eventuallyEq heq.deriv

theorem differentiableAt_deriv2_thetaSecondFormula {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (deriv (deriv thetaSecondFormula)) x := by
  have h1 := (contDiffAt_thetaSecondFormula_three hx).derivWithin
    (m := 2) (by norm_num)
  have h2 := h1.derivWithin (m := 1) (by norm_num)
  exact h2.differentiableAt_one

/-- The final d4→d5 link of the canonical `e8Theta` jet is unconditional. -/
theorem differentiableAt_deriv4_e8Theta {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (deriv (deriv (deriv (deriv e8Theta)))) x := by
  have heq : deriv (deriv e8Theta) =ᶠ[nhds x] thetaSecondFormula := by
    filter_upwards [Ioi_mem_nhds hx] with u hu
    exact deriv2_e8Theta_eq_formula hu
  exact (differentiableAt_deriv2_thetaSecondFormula hx).congr_of_eventuallyEq
    heq.deriv.deriv

end GeneralCK

end


