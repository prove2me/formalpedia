-- Prove2me | Definitions.Def_eulerMascheroni_gompertz
-- name    : eulerMascheroni_gompertz
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-10T06:41:28.056394+00:00
-- url     : https://prove2.me/theorems/b7f6f4d7-9e18-4738-b85c-2581be7e5505
-- title:
--   The Euler–Gompertz constant $\delta$
-- statement:
--   The **Euler--Gompertz constant** is
--
--   $$\delta \;=\; \int_0^{\infty} \frac{e^{-u}}{1+u}\,du \;=\; 0.5963473623\ldots$$
--
--   It arises as the value $\delta = e \cdot E_1(1)$ of the exponential integral, and as the Borel sum of the divergent series $\sum_{n\ge 0} (-1)^n n!$. Its arithmetic nature is unknown in isolation, exactly as for Euler's constant; what is known concerns the pair $(\gamma,\delta)$ jointly, which is why it appears in this mission.
--
--   **Formalization note.** Lean's integral is a total function, returning $0$ when the integrand is not integrable. Two facts are therefore proved alongside the definition: that $e^{-u}/(1+u)$ is integrable on $(0,\infty)$, being dominated by $e^{-u}$; and that $\delta > 0$. Without them, $\delta$ could a priori be the junk value $0$ — which is rational and algebraic — and the disjunctive statements about the pair $(\gamma,\delta)$ would silently degenerate into statements about $\gamma$ alone.

import Mathlib

open MeasureTheory Set

namespace EulerMascheroni

/-- The Euler--Gompertz constant `δ = ∫₀^∞ e^{-u}/(1+u) du`.  It is the constant that the
known unconditional results pair with Euler's constant: the Pade-approximation machinery of
Mahler, Shidlovskii, Aptekarev and Rivoal controls the pair `(γ, δ)` jointly without
separating them. -/
noncomputable def gompertzConstant : ℝ := ∫ u in Ioi (0 : ℝ), Real.exp (-u) / (1 + u)

/-- The defining integrand is integrable on `(0, ∞)`, dominated by `exp (-u)`.

This is recorded because Lean's integral is a total function: for a non-integrable integrand
`∫` returns `0`.  Without this lemma, `gompertzConstant` could a priori be that junk value,
which is rational and algebraic, and every statement below asserting something about `δ`
would silently degenerate. -/
theorem gompertz_integrableOn :
    IntegrableOn (fun u : ℝ => Real.exp (-u) / (1 + u)) (Ioi 0) := by
  have hexp : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi (0:ℝ) (by norm_num : (0:ℝ) < 1)
  refine Integrable.mono' hexp ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
    · exact (continuous_const.add continuous_id).continuousOn
    · intro u hu
      simp only [mem_Ioi] at hu
      exact ne_of_gt (by linarith)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    simp only [mem_Ioi] at hu
    have h1 : (1:ℝ) ≤ 1 + u := by linarith
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact div_le_self (Real.exp_pos _).le h1

/-- `δ` is strictly positive; in particular it is not the junk value `0`. -/
theorem gompertzConstant_pos : 0 < gompertzConstant := by
  rw [gompertzConstant, setIntegral_pos_iff_support_of_nonneg_ae]
  · have : (Function.support fun u : ℝ => Real.exp (-u) / (1 + u)) ∩ Ioi 0 = Ioi 0 := by
      ext u
      simp only [Set.mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
      intro hu
      positivity
    rw [this]
    simp
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    simp only [mem_Ioi] at hu
    positivity
  · exact gompertz_integrableOn

end EulerMascheroni


