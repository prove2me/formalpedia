-- Prove2me | solution 1 for Apery.theta_eventually_close
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T14:34:31.455772+00:00
-- url     : https://prove2.me/submissions/c5602763-449b-4267-bbb3-05226038d591

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The prime number theorem in $\varepsilon$-form from the platform's medium-strength PNT

This file proves the platform theorem `Apery.theta_eventually_close`:

$$\forall \varepsilon > 0,\quad |\theta(y) - y| \le \varepsilon y \quad\text{for all large } y,$$

i.e. $\theta(y) \sim y$. It is reduced to the platform's proved theorem `MediumPNT`
($\psi(x) = x + O(x\exp(-c(\log x)^{1/10}))$) together with Mathlib's elementary comparison
of $\theta$ and $\psi$: `Chebyshev.theta_le_psi` and `Chebyshev.psi_sub_theta_le`
($\psi x - \theta x \le 2\sqrt x \log x$, since $\psi - \theta$ collects the prime powers
$p^k$, $k \ge 2$). Since $\psi - \theta = O(\sqrt x\log x) = o(x)$, the two functions are
asymptotic, and the limit $\psi(x)/x \to 1$ transfers to $\theta$. This is the analytic input
of the small-prime range of the growth estimate for the normaliser; the source project
mo271/Zeta5 imported the prime number theorem from the external package `PrimeNumberTheoremAnd`.
-/

import Mathlib
import Theorems.Thm_MediumPNT

set_option autoImplicit false

section Port0
/-!
# The prime number theorem in `ε`-form from the medium-strength PNT

`Apery.theta_eventually_close`: `|θ(y) - y| ≤ ε y` for all large `y`, i.e. `θ(y) ~ y`.

This is the analytic input of the small-prime range of the growth estimate for the normaliser
of the ζ(5) construction. In the source project `mo271/Zeta5` it is imported from the external
package `PrimeNumberTheoremAnd` (`Apery/PNT.lean`). Here it is derived from the platform's
proved medium-strength prime number theorem `MediumPNT`
(`ψ(x) = x + O(x exp(-c (log x)^{1/10}))`) together with Mathlib's elementary comparison of
`θ` and `ψ` (`Chebyshev.theta_le_psi`, `Chebyshev.psi_sub_theta_le`):
`ψ - θ = O(√x log x) = o(x)`, hence `θ` is asymptotic to `ψ`, hence to the identity.
-/

open Filter Asymptotics

namespace Apery

/-- The prime number theorem in `ε`-form: `|θ(y) - y| ≤ ε y` eventually. -/
lemma theta_eventually_close {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, |Chebyshev.theta y - y| ≤ ε * y := by
  -- Step 1: `ψ x = x + O(x exp(-c (log x)^{1/10}))` gives `|ψ x - x| ≤ ε/2 x` eventually.
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨C, hCb⟩ := isBigO_iff.mp hO
  have hexp : Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
    have h2 : Tendsto (fun x : ℝ => c * (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
      h1.const_mul_atTop hc
    have h3 : Tendsto (fun x : ℝ => -c * (Real.log x) ^ ((1 : ℝ) / 10)) atTop atBot := by
      simpa only [neg_mul] using tendsto_neg_atBot_iff.mpr h2
    exact Real.tendsto_exp_atBot.comp h3
  have hsmall : ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) ≤ ε / (2 * (max C 0 + 1)) :=
    hexp.eventually (eventually_le_nhds (by positivity))
  have hψ : ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ ε / 2 * x := by
    filter_upwards [hCb, hsmall, eventually_gt_atTop (0 : ℝ)] with x hx hxe hx0
    have hE : (0 : ℝ) < Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := Real.exp_pos _
    have hxn : ‖x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))‖ =
        x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
      rw [norm_mul, Real.norm_of_nonneg hx0.le, Real.norm_of_nonneg hE.le]
    have hx' : ‖Chebyshev.psi x - x‖ ≤
        C * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
      simpa only [Pi.sub_apply, id_eq, hxn] using hx
    have h1 : ‖Chebyshev.psi x - x‖ ≤
        max C 0 * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
      have h2 : C * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) ≤
          max C 0 * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)
      linarith
    have h3 : max C 0 * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) ≤
        max C 0 * (x * (ε / (2 * (max C 0 + 1)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxe hx0.le) (le_max_right C 0)
    have h4 : max C 0 * (x * (ε / (2 * (max C 0 + 1)))) =
        (max C 0 / (max C 0 + 1)) * (ε / 2) * x := by
      field_simp
    have h5 : max C 0 / (max C 0 + 1) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]; linarith [le_max_right C 0]
    have h6 : (max C 0 / (max C 0 + 1)) * (ε / 2) * x ≤ ε / 2 * x := by
      have hxε : 0 ≤ ε / 2 * x := by positivity
      have := mul_le_mul_of_nonneg_right h5 hxε
      nlinarith [this]
    have hone : ‖Chebyshev.psi x - x‖ ≤ ε / 2 * x := by linarith [h1, h3, h4, h6]
    rwa [Real.norm_eq_abs] at hone
  -- Step 2: `ψ x - θ x ≤ 2 √x log x = o(x)`.
  have hsqrt : ∀ᶠ x : ℝ in atTop, 2 * Real.sqrt x * Real.log x ≤ ε / 2 * x := by
    have hlo : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x ^ ((1 : ℝ) / 2)) :=
      isLittleO_log_rpow_atTop (by norm_num)
    have hq : Tendsto (fun x : ℝ => Real.log x / x ^ ((1 : ℝ) / 2)) atTop (nhds 0) :=
      hlo.tendsto_div_nhds_zero
    have h2 : Tendsto (fun x : ℝ => 2 * (Real.log x / x ^ ((1 : ℝ) / 2))) atTop (nhds 0) := by
      simpa using hq.const_mul (2 : ℝ)
    have h3 : ∀ᶠ x : ℝ in atTop, 2 * (Real.log x / x ^ ((1 : ℝ) / 2)) ≤ ε / 2 :=
      h2.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < ε / 2))
    have h4 : Tendsto (fun x : ℝ => 2 * Real.sqrt x * Real.log x / x) atTop (nhds 0) := by
      apply h2.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx0
      have hxhalf : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
        rw [← Real.rpow_add hx0]; norm_num
      rw [Real.sqrt_eq_rpow]
      field_simp
      rw [sq, hxhalf]
    have h5 : ∀ᶠ x : ℝ in atTop, 2 * Real.sqrt x * Real.log x / x ≤ ε / 2 :=
      h4.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < ε / 2))
    filter_upwards [h5, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    exact (div_le_iff₀ hx0).mp hx
  -- Step 3: sandwich.
  filter_upwards [hψ, hsqrt, eventually_ge_atTop (1 : ℝ)] with x hψx hsqx hx1
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hupper : Chebyshev.theta x ≤ x + ε * x := by
    have h := (abs_le.mp hψx).2
    have hθψ : Chebyshev.theta x ≤ Chebyshev.psi x := Chebyshev.theta_le_psi x
    have : ε / 2 * x ≤ ε * x := by nlinarith [hε, hx0]
    linarith
  have hlower : x - ε * x ≤ Chebyshev.theta x := by
    have h := (abs_le.mp hψx).1
    have hψθ : Chebyshev.psi x - Chebyshev.theta x ≤ 2 * Real.sqrt x * Real.log x :=
      Chebyshev.psi_sub_theta_le hx1
    linarith
  rw [abs_le]
  constructor <;> linarith

end Apery
end Port0


open Filter in
/-- The platform target `Apery.theta_eventually_close`, restated at top level as `solution`. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, |Chebyshev.theta y - y| ≤ ε * y :=
  Apery.theta_eventually_close hε
