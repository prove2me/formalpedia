-- Prove2me | Definitions.Def_RHT1000_Support_20261118_B006
-- name    : RHT1000_Support_20261118_B006
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-18T16:46:39.293669+00:00
-- url     : https://prove2.me/theorems/d8154e03-41bd-4104-a71e-e7cb1be8fc5e
-- title:
--   Suporte completo para T1000 — bloco 6 de 10
-- statement:
--   Definições e lemas auxiliares completos para a prova finita T1000. Este bloco não afirma sozinho a conclusão T1000 nem RH. A divisão reduz o tempo de compilação sem substituir demonstrações por hipóteses.
-- source:
--   Código adaptado de Salvatore Mercuri e Bhavik Mehta, smmercuri/zeta, tag v1-1e8 (3dab648), com dependências e avisos de autoria preservados. Fonte histórica integral T1000: https://axle.axiommath.ai/check#r=d2dcb520-c50a-44dc-a527-de0f7a51b892 . Reorganização em módulos ordinários para compatibilidade com Prove2Me; atribuição da adaptação: projeto Desenvolvimento RH, Ricardo Marangoni Brandão Bueno.

import Definitions.Def_RHT1000_Support_20261118_B005
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
section CertificatePort88
section
open MeasureTheory Real
open scoped Nat
namespace Real
theorem exp_neg_pi_mul_sq_add_mul_abs_le (b w : ℝ) :
    exp (-(π * w ^ 2) + b * |w|)
      ≤ exp (b ^ 2 / (4 * π)) *
        (exp (-π * (w - b / (2 * π)) ^ 2) + exp (-π * (w + b / (2 * π)) ^ 2)) := by
  have hpi : (π : ℝ) ≠ 0 := pi_ne_zero
  rcases abs_cases w with ⟨hw, -⟩ | ⟨hw, -⟩
  · have key : -(π * w ^ 2) + b * |w| = b ^ 2 / (4 * π) + -π * (w - b / (2 * π)) ^ 2 := by
      rw [hw]; field_simp; ring
    rw [key, exp_add]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (exp_pos _).le) (exp_pos _).le
  · have key : -(π * w ^ 2) + b * |w| = b ^ 2 / (4 * π) + -π * (w + b / (2 * π)) ^ 2 := by
      rw [hw]; field_simp; ring
    rw [key, exp_add]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (exp_pos _).le) (exp_pos _).le
end Real
private theorem integrable_exp_neg_pi_mul_sub_sq (c : ℝ) :
    Integrable fun w : ℝ ↦ exp (-π * (w - c) ^ 2) :=
  (integrable_exp_neg_mul_sq pi_pos).comp_sub_right c
private theorem integrable_exp_neg_pi_mul_add_sq (c : ℝ) :
    Integrable fun w : ℝ ↦ exp (-π * (w + c) ^ 2) := by
  simpa [sub_neg_eq_add] using integrable_exp_neg_pi_mul_sub_sq (-c)
private theorem integrable_majorant (b : ℝ) :
    Integrable fun w : ℝ ↦ exp (b ^ 2 / (4 * π)) *
      (exp (-π * (w - b / (2 * π)) ^ 2) + exp (-π * (w + b / (2 * π)) ^ 2)) :=
  ((integrable_exp_neg_pi_mul_sub_sq _).add (integrable_exp_neg_pi_mul_add_sq _)).const_mul _
theorem integrable_exp_neg_pi_mul_sq_add_mul_abs (b : ℝ) :
    Integrable fun w : ℝ ↦ exp (-(π * w ^ 2) + b * |w|) := by
  refine (integrable_majorant b).mono' (by fun_prop) (Filter.Eventually.of_forall fun w ↦ ?_)
  rw [norm_of_nonneg (exp_pos _).le]
  exact exp_neg_pi_mul_sq_add_mul_abs_le b w
theorem integrable_rpow_abs_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {q : ℝ} (hq : -1 < q) :
    Integrable fun w : ℝ ↦ |w| ^ q * exp (-b * w ^ 2) := by
  have hIoi : IntegrableOn (fun w : ℝ ↦ |w| ^ q * exp (-b * w ^ 2)) (Set.Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq hb hq).congr_fun
      (fun x hx ↦ by rw [abs_of_pos hx]) measurableSet_Ioi
  have hIio : IntegrableOn (fun w : ℝ ↦ |w| ^ q * exp (-b * w ^ 2)) (Set.Iio 0) := by
    simpa using hIoi.comp_neg
  rw [← integrableOn_univ, ← Set.Iio_union_Ici (a := (0 : ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hIio, hIoi⟩
theorem integrable_rpow_abs_mul_exp_neg_pi_mul_sq_add_mul_abs {q : ℝ} (hq : -1 < q) (b : ℝ) :
    Integrable fun w : ℝ ↦ |w| ^ q * exp (-(π * w ^ 2) + b * |w|) := by
  have hmaj : Integrable fun w : ℝ ↦ exp (b ^ 2 / (2 * π)) * (|w| ^ q * exp (-(π / 2) * w ^ 2)) :=
    (integrable_rpow_abs_mul_exp_neg_mul_sq (by positivity) hq).const_mul _
  have hmeas : AEStronglyMeasurable
      (fun w : ℝ ↦ |w| ^ q * exp (-(π * w ^ 2) + b * |w|)) volume := by
    have h1 := (integrable_rpow_abs_mul_exp_neg_mul_sq pi_pos hq).aestronglyMeasurable
    have h2 : Continuous fun w : ℝ ↦ exp (b * |w|) := by fun_prop
    refine (h1.mul h2.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [Pi.mul_apply]
    rw [mul_assoc, ← exp_add, show -π * w ^ 2 + b * |w| = -(π * w ^ 2) + b * |w| by ring]
  refine hmaj.mono' hmeas (Filter.Eventually.of_forall fun w ↦ ?_)
  have hkey : -(π * w ^ 2) + b * |w| ≤ b ^ 2 / (2 * π) + -(π / 2) * w ^ 2 := by
    rw [← sub_nonneg, ← sq_abs w,
      show b ^ 2 / (2 * π) + -(π / 2) * |w| ^ 2 - (-(π * |w| ^ 2) + b * |w|)
        = (π * |w| - b) ^ 2 / (2 * π) by field_simp; ring]
    positivity
  rw [norm_of_nonneg (by positivity)]
  calc |w| ^ q * exp (-(π * w ^ 2) + b * |w|)
      ≤ |w| ^ q * exp (b ^ 2 / (2 * π) + -(π / 2) * w ^ 2) := by gcongr
    _ = exp (b ^ 2 / (2 * π)) * (|w| ^ q * exp (-(π / 2) * w ^ 2)) := by
        rw [exp_add]; ring
section Moments
variable {b : ℝ}
theorem integrableOn_pow_mul_exp_neg_mul_sq (hb : 0 < b) (n : ℕ) :
    IntegrableOn (fun w : ℝ ↦ w ^ n * exp (-b * w ^ 2)) (Set.Ioi 0) := by
  simpa using integrableOn_rpow_mul_exp_neg_mul_sq hb
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
theorem integrable_abs_pow_mul_exp_neg_mul_sq (hb : 0 < b) (n : ℕ) :
    Integrable fun w : ℝ ↦ |w| ^ n * exp (-b * w ^ 2) := by
  simpa using integrable_rpow_abs_mul_exp_neg_mul_sq hb
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
theorem integrable_abs_pow_mul_exp_neg_mul_sq_add_mul_abs (hb : 0 < b) (c : ℝ) (n : ℕ) :
    Integrable fun w : ℝ ↦ |w| ^ n * exp (-b * w ^ 2 + c * |w|) := by
  have hmaj : Integrable fun w : ℝ ↦ exp (c ^ 2 / (2 * b)) * (|w| ^ n * exp (-(b / 2) * w ^ 2)) :=
    (integrable_abs_pow_mul_exp_neg_mul_sq (by positivity) n).const_mul _
  refine hmaj.mono' (by fun_prop) (.of_forall fun w ↦ ?_)
  have hkey : -b * w ^ 2 + c * |w| ≤ c ^ 2 / (2 * b) + -(b / 2) * w ^ 2 := by
    rw [← sub_nonneg, ← sq_abs w,
      show c ^ 2 / (2 * b) + -(b / 2) * |w| ^ 2 - (-b * |w| ^ 2 + c * |w|)
        = (b * |w| - c) ^ 2 / (2 * b) by field_simp; ring]
    positivity
  rw [norm_of_nonneg (by positivity)]
  calc |w| ^ n * exp (-b * w ^ 2 + c * |w|)
      ≤ |w| ^ n * exp (c ^ 2 / (2 * b) + -(b / 2) * w ^ 2) := by gcongr
    _ = exp (c ^ 2 / (2 * b)) * (|w| ^ n * exp (-(b / 2) * w ^ 2)) := by rw [exp_add]; ring
theorem integrable_pow_add_mul_abs_mul_exp_neg_mul_sq_add_mul_abs (hb : 0 < b) {A β : ℝ}
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (c : ℝ) (n : ℕ) :
    Integrable fun w : ℝ ↦ (A + β * |w|) ^ n * exp (-b * w ^ 2 + c * |w|) := by
  have h0 : Integrable fun w : ℝ ↦ exp (-b * w ^ 2 + c * |w|) := by
    simpa using integrable_abs_pow_mul_exp_neg_mul_sq_add_mul_abs hb c 0
  have hn : Integrable fun w : ℝ ↦ |w| ^ n * exp (-b * w ^ 2 + c * |w|) :=
    integrable_abs_pow_mul_exp_neg_mul_sq_add_mul_abs hb c n
  have hmaj : Integrable fun w : ℝ ↦ 2 ^ (n - 1) * (A ^ n * exp (-b * w ^ 2 + c * |w|)
      + β ^ n * (|w| ^ n * exp (-b * w ^ 2 + c * |w|))) :=
    ((h0.const_mul (A ^ n)).add (hn.const_mul (β ^ n))).const_mul _
  refine hmaj.mono' (by fun_prop) (.of_forall fun w ↦ ?_)
  rw [norm_of_nonneg (by positivity)]
  calc (A + β * |w|) ^ n * exp (-b * w ^ 2 + c * |w|)
      ≤ 2 ^ (n - 1) * (A ^ n + (β * |w|) ^ n) * exp (-b * w ^ 2 + c * |w|) := by
        gcongr
        exact add_pow_le hA (by positivity) n
    _ = 2 ^ (n - 1) * (A ^ n * exp (-b * w ^ 2 + c * |w|)
          + β ^ n * (|w| ^ n * exp (-b * w ^ 2 + c * |w|))) := by rw [mul_pow]; ring
private theorem tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero (hb : 0 < b) (n : ℕ) :
    Filter.Tendsto (fun w : ℝ ↦ w ^ n * exp (-b * w ^ 2)) Filter.atTop (nhds 0) := by
  have hexp : Filter.Tendsto (fun x : ℝ ↦ exp (-(1 / 2) * x)) Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun x : ℝ ↦ -(1 / 2) * x) Filter.atTop Filter.atBot :=
      Filter.tendsto_id.const_mul_atTop_of_neg (by norm_num)
    exact tendsto_exp_atBot.comp h
  refine ((rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb
    ((n : ℝ))).isBigO.trans_tendsto hexp).congr fun x ↦ ?_
  rw [rpow_natCast]
theorem integral_Ioi_mul_exp_neg_mul_sq (hb : 0 < b) (c : ℝ) :
    ∫ w in Set.Ioi c, w * exp (-b * w ^ 2) = exp (-b * c ^ 2) / (2 * b) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hderiv : ∀ w : ℝ, HasDerivAt (fun w : ℝ ↦ -exp (-b * w ^ 2))
      (2 * b * (w * exp (-b * w ^ 2))) w := by
    intro w
    have h2 : HasDerivAt (fun w : ℝ ↦ exp (-b * w ^ 2))
        (exp (-b * w ^ 2) * (-b * (2 * w))) w := by
      simpa using ((hasDerivAt_pow 2 w).const_mul (-b)).exp
    rw [show 2 * b * (w * exp (-b * w ^ 2)) = -(exp (-b * w ^ 2) * (-b * (2 * w))) by ring]
    exact h2.neg
  have hlim : Filter.Tendsto (fun w : ℝ ↦ -exp (-b * w ^ 2)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero hb 0).neg
  have key := integral_Ioi_of_hasDerivAt_of_tendsto (a := c)
    (Continuous.continuousWithinAt (by fun_prop)) (fun x _ ↦ hderiv x)
    ((integrable_mul_exp_neg_mul_sq hb).const_mul (2 * b)).integrableOn hlim
  rw [integral_const_mul, zero_sub, neg_neg] at key
  rw [eq_div_iff (by positivity : (2 : ℝ) * b ≠ 0)]
  linear_combination key
theorem integral_Ioi_pow_add_two_mul_exp_neg_mul_sq (hb : 0 < b) (n : ℕ) :
    ∫ w in Set.Ioi (0 : ℝ), w ^ (n + 2) * exp (-b * w ^ 2)
      = ((n : ℝ) + 1) / (2 * b) * ∫ w in Set.Ioi (0 : ℝ), w ^ n * exp (-b * w ^ 2) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hderiv : ∀ w : ℝ, HasDerivAt (fun w : ℝ ↦ -(w ^ (n + 1) * exp (-b * w ^ 2)))
      (2 * b * (w ^ (n + 2) * exp (-b * w ^ 2))
        - ((n : ℝ) + 1) * (w ^ n * exp (-b * w ^ 2))) w := by
    intro w
    have h1 : HasDerivAt (fun w : ℝ ↦ w ^ (n + 1)) (((n : ℝ) + 1) * w ^ n) w := by
      simpa using hasDerivAt_pow (n + 1) w
    have h2 : HasDerivAt (fun w : ℝ ↦ exp (-b * w ^ 2))
        (exp (-b * w ^ 2) * (-b * (2 * w))) w := by
      simpa using ((hasDerivAt_pow 2 w).const_mul (-b)).exp
    rw [show 2 * b * (w ^ (n + 2) * exp (-b * w ^ 2))
        - ((n : ℝ) + 1) * (w ^ n * exp (-b * w ^ 2))
        = -(((n : ℝ) + 1) * w ^ n * exp (-b * w ^ 2)
          + w ^ (n + 1) * (exp (-b * w ^ 2) * (-b * (2 * w)))) by ring]
    exact (h1.mul h2).neg
  have hint : IntegrableOn (fun w : ℝ ↦ 2 * b * (w ^ (n + 2) * exp (-b * w ^ 2))
      - ((n : ℝ) + 1) * (w ^ n * exp (-b * w ^ 2))) (Set.Ioi 0) :=
    ((integrableOn_pow_mul_exp_neg_mul_sq hb (n + 2)).const_mul _).sub
      ((integrableOn_pow_mul_exp_neg_mul_sq hb n).const_mul _)
  have hlim : Filter.Tendsto (fun w : ℝ ↦ -(w ^ (n + 1) * exp (-b * w ^ 2)))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero hb (n + 1)).neg
  have key := integral_Ioi_of_hasDerivAt_of_tendsto
    (Continuous.continuousWithinAt (by fun_prop)) (fun x _ ↦ hderiv x) hint hlim
  rw [integral_sub ((integrableOn_pow_mul_exp_neg_mul_sq hb (n + 2)).const_mul _)
    ((integrableOn_pow_mul_exp_neg_mul_sq hb n).const_mul _), integral_const_mul,
    integral_const_mul] at key
  rw [show -((0 : ℝ) ^ (n + 1) * exp (-b * (0 : ℝ) ^ 2)) = 0 by simp, sub_zero] at key
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity : (2 : ℝ) * b ≠ 0)]
  linear_combination key
private theorem integral_abs_pow_mul_exp_neg_mul_sq_eq_two_mul (n : ℕ) :
    ∫ w : ℝ, |w| ^ n * exp (-b * w ^ 2)
      = 2 * ∫ w in Set.Ioi (0 : ℝ), w ^ n * exp (-b * w ^ 2) := by
  have h := integral_comp_abs (f := fun u : ℝ ↦ u ^ n * exp (-b * u ^ 2))
  simp only [sq_abs] at h
  exact h
theorem integral_abs_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, |w| * exp (-b * w ^ 2) = 1 / b := by
  have h := integral_abs_pow_mul_exp_neg_mul_sq_eq_two_mul (b := b) 1
  simp only [pow_one] at h
  rw [h, integral_Ioi_mul_exp_neg_mul_sq hb 0, show -b * (0 : ℝ) ^ 2 = 0 by ring, Real.exp_zero]
  field_simp
theorem integral_abs_pow_add_two_mul_exp_neg_mul_sq (hb : 0 < b) (n : ℕ) :
    ∫ w : ℝ, |w| ^ (n + 2) * exp (-b * w ^ 2)
      = ((n : ℝ) + 1) / (2 * b) * ∫ w : ℝ, |w| ^ n * exp (-b * w ^ 2) := by
  rw [integral_abs_pow_mul_exp_neg_mul_sq_eq_two_mul,
    integral_abs_pow_mul_exp_neg_mul_sq_eq_two_mul,
    integral_Ioi_pow_add_two_mul_exp_neg_mul_sq hb n]
  ring
theorem integral_abs_pow_even_mul_exp_neg_mul_sq (hb : 0 < b) (m : ℕ) :
    ∫ w : ℝ, |w| ^ (2 * m) * exp (-b * w ^ 2)
      = (2 * m)! / (4 ^ m * m !) * (√(π / b) / b ^ m) := by
  induction m with
  | zero => simpa using integral_gaussian b
  | succ m ih =>
      have hb0 : b ≠ 0 := hb.ne'
      have hm : (m ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
      have hfac : ((2 * m + 2)! : ℝ) = ((2 : ℝ) * m + 2) * (2 * m + 1) * (2 * m)! := by
        rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, integral_abs_pow_add_two_mul_exp_neg_mul_sq hb,
        ih, hfac, Nat.factorial_succ]
      push_cast
      field_simp
      ring
theorem integral_abs_pow_odd_mul_exp_neg_mul_sq (hb : 0 < b) (m : ℕ) :
    ∫ w : ℝ, |w| ^ (2 * m + 1) * exp (-b * w ^ 2) = m ! / b ^ (m + 1) := by
  induction m with
  | zero => simpa using integral_abs_mul_exp_neg_mul_sq hb
  | succ m ih =>
      have hb0 : b ≠ 0 := hb.ne'
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring,
        integral_abs_pow_add_two_mul_exp_neg_mul_sq hb, ih, Nat.factorial_succ]
      push_cast
      field_simp
      ring
theorem integral_sq_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, w ^ 2 * exp (-b * w ^ 2) = √(π / b) / (2 * b) := by
  have h := integral_abs_pow_even_mul_exp_neg_mul_sq hb 1
  simp only [show 2 * 1 = 2 from rfl, sq_abs, pow_one, Nat.factorial] at h
  rw [h]
  push_cast
  field_simp
  ring
private theorem even_four : Even 4 := ⟨2, rfl⟩
private theorem even_six : Even 6 := ⟨3, rfl⟩
theorem integral_pow_four_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, w ^ 4 * exp (-b * w ^ 2) = 3 * √(π / b) / (4 * b ^ 2) := by
  have h := integral_abs_pow_even_mul_exp_neg_mul_sq hb 2
  simp only [show 2 * 2 = 4 from rfl, even_four.pow_abs] at h
  rw [h, show ((4 : ℕ)! : ℝ) = 24 by norm_num [Nat.factorial],
    show ((2 : ℕ)! : ℝ) = 2 by norm_num [Nat.factorial]]
  field_simp
  ring
theorem integral_pow_six_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, w ^ 6 * exp (-b * w ^ 2) = 15 * √(π / b) / (8 * b ^ 3) := by
  have h := integral_abs_pow_even_mul_exp_neg_mul_sq hb 3
  simp only [show 2 * 3 = 6 from rfl, even_six.pow_abs] at h
  rw [h, show ((6 : ℕ)! : ℝ) = 720 by norm_num [Nat.factorial],
    show ((3 : ℕ)! : ℝ) = 6 by norm_num [Nat.factorial]]
  field_simp
  ring
theorem integral_abs_pow_three_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, |w| ^ 3 * exp (-b * w ^ 2) = 1 / b ^ 2 := by
  simpa using integral_abs_pow_odd_mul_exp_neg_mul_sq hb 1
theorem integral_Ioi_exp_neg_mul_sq_le (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    ∫ w in Set.Ioi c, exp (-b * w ^ 2) ≤ exp (-b * c ^ 2) / (2 * b * c) := by
  have h1 : IntegrableOn (fun w : ℝ ↦ exp (-b * w ^ 2)) (Set.Ioi c) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  have h2 : IntegrableOn (fun w : ℝ ↦ c⁻¹ * (w * exp (-b * w ^ 2))) (Set.Ioi c) :=
    ((integrable_mul_exp_neg_mul_sq hb).const_mul c⁻¹).integrableOn
  calc ∫ w in Set.Ioi c, exp (-b * w ^ 2)
      ≤ ∫ w in Set.Ioi c, c⁻¹ * (w * exp (-b * w ^ 2)) := by
        refine setIntegral_mono_on h1 h2 measurableSet_Ioi fun w hw ↦ ?_
        have hcw : (1 : ℝ) ≤ c⁻¹ * w := by
          rw [← div_eq_inv_mul]
          exact (one_le_div hc).2 (le_of_lt hw)
        calc exp (-b * w ^ 2) = 1 * exp (-b * w ^ 2) := (one_mul _).symm
          _ ≤ c⁻¹ * w * exp (-b * w ^ 2) :=
              mul_le_mul_of_nonneg_right hcw (exp_pos _).le
          _ = c⁻¹ * (w * exp (-b * w ^ 2)) := by ring
    _ = exp (-b * c ^ 2) / (2 * b * c) := by
        rw [integral_const_mul, integral_Ioi_mul_exp_neg_mul_sq hb c]
        field_simp
theorem integral_Ioi_pow_three_mul_exp_neg_mul_sq (hb : 0 < b) (c : ℝ) :
    ∫ w in Set.Ioi c, w ^ 3 * exp (-b * w ^ 2)
      = exp (-b * c ^ 2) * (c ^ 2 / (2 * b) + 1 / (2 * b ^ 2)) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hderiv : ∀ w : ℝ, HasDerivAt
      (fun w : ℝ ↦ -((w ^ 2 / (2 * b) + 1 / (2 * b ^ 2)) * exp (-b * w ^ 2)))
      (w ^ 3 * exp (-b * w ^ 2)) w := by
    intro w
    have h1 : HasDerivAt (fun w : ℝ ↦ w ^ 2 / (2 * b) + 1 / (2 * b ^ 2)) (2 * w / (2 * b)) w := by
      simpa using ((hasDerivAt_pow 2 w).div_const (2 * b)).add_const (1 / (2 * b ^ 2))
    have h2 : HasDerivAt (fun w : ℝ ↦ exp (-b * w ^ 2)) (exp (-b * w ^ 2) * (-b * (2 * w))) w := by
      simpa using ((hasDerivAt_pow 2 w).const_mul (-b)).exp
    refine (h1.mul h2).neg.congr_deriv ?_
    field_simp
    ring
  have hint : Integrable fun w : ℝ ↦ w ^ 3 * exp (-b * w ^ 2) := by
    refine (integrable_abs_pow_mul_exp_neg_mul_sq hb 3).mono' (by fun_prop)
      (.of_forall fun w ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (exp_pos _).le]
  have hlim : Filter.Tendsto
      (fun w : ℝ ↦ -((w ^ 2 / (2 * b) + 1 / (2 * b ^ 2)) * exp (-b * w ^ 2)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun w : ℝ ↦ exp (-b * w ^ 2)) Filter.atTop (nhds 0) := by
      simpa using tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero hb 0
    have h := ((tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero hb 2).const_mul
      (-(1 / (2 * b)))).add (h0.const_mul (-(1 / (2 * b ^ 2))))
    rw [show -(1 / (2 * b)) * (0 : ℝ) + -(1 / (2 * b ^ 2)) * 0 = 0 by ring] at h
    exact h.congr fun w ↦ by ring
  have key := integral_Ioi_of_hasDerivAt_of_tendsto (a := c)
    (Continuous.continuousWithinAt (by fun_prop)) (fun x _ ↦ hderiv x) hint.integrableOn hlim
  rw [key, zero_sub, neg_neg]
  ring
private theorem lt_abs_of_mem_compl_Icc {c w : ℝ} (hw : w ∈ (Set.Icc (-c) c)ᶜ) : c < |w| := by
  rwa [Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le] at hw
theorem integral_compl_Icc_eq_two_mul_integral_Ioi {f : ℝ → ℝ} (hf : Integrable f)
    (hfe : ∀ w : ℝ, f (-w) = f w) {c : ℝ} (hc : 0 ≤ c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, f w = 2 * ∫ w in Set.Ioi c, f w := by
  have hcompl : (Set.Icc (-c) c)ᶜ = Set.Iio (-c) ∪ Set.Ioi c := by
    ext w
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
      not_and_or, not_le]
  have hdisj : Disjoint (Set.Iio (-c)) (Set.Ioi c) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    have h1 : w < -c := hw
    have h2 : c < w := hw'
    linarith
  have hIio : ∫ w in Set.Iio (-c), f w = ∫ w in Set.Ioi c, f w := by
    have h := integral_comp_neg_Iic (-c) f
    rw [neg_neg] at h
    rw [← integral_Iic_eq_integral_Iio, ← h]
    exact setIntegral_congr_fun measurableSet_Iic fun w _ ↦ (hfe w).symm
  rw [hcompl, setIntegral_union hdisj measurableSet_Ioi hf.integrableOn hf.integrableOn, hIio]
  ring
theorem integral_compl_Icc_exp_neg_mul_sq_le (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, exp (-b * w ^ 2) ≤ exp (-b * c ^ 2) / (b * c) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hc0 : c ≠ 0 := hc.ne'
  rw [integral_compl_Icc_eq_two_mul_integral_Ioi (integrable_exp_neg_mul_sq hb)
    (fun w ↦ by rw [neg_sq]) hc.le]
  have heq : 2 * (exp (-b * c ^ 2) / (2 * b * c)) = exp (-b * c ^ 2) / (b * c) := by
    field_simp
  linarith [integral_Ioi_exp_neg_mul_sq_le hb hc]
theorem integral_compl_Icc_abs_mul_exp_neg_mul_sq (hb : 0 < b) {c : ℝ} (hc : 0 ≤ c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, |w| * exp (-b * w ^ 2) = exp (-b * c ^ 2) / b := by
  have hb0 : b ≠ 0 := hb.ne'
  have hint : Integrable fun w : ℝ ↦ |w| * exp (-b * w ^ 2) := by
    simpa using integrable_abs_pow_mul_exp_neg_mul_sq hb 1
  have hIoi : ∫ w in Set.Ioi c, |w| * exp (-b * w ^ 2) = ∫ w in Set.Ioi c, w * exp (-b * w ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ by
      rw [abs_of_pos (lt_of_le_of_lt hc hw)]
  rw [integral_compl_Icc_eq_two_mul_integral_Ioi hint (fun w ↦ by rw [abs_neg, neg_sq]) hc, hIoi,
    integral_Ioi_mul_exp_neg_mul_sq hb c]
  field_simp
theorem integral_compl_Icc_abs_pow_three_mul_exp_neg_mul_sq (hb : 0 < b) {c : ℝ} (hc : 0 ≤ c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, |w| ^ 3 * exp (-b * w ^ 2)
      = exp (-b * c ^ 2) * (c ^ 2 / b + 1 / b ^ 2) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hint : Integrable fun w : ℝ ↦ |w| ^ 3 * exp (-b * w ^ 2) :=
    integrable_abs_pow_mul_exp_neg_mul_sq hb 3
  have hIoi : ∫ w in Set.Ioi c, |w| ^ 3 * exp (-b * w ^ 2)
      = ∫ w in Set.Ioi c, w ^ 3 * exp (-b * w ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ by
      rw [abs_of_pos (lt_of_le_of_lt hc hw)]
  rw [integral_compl_Icc_eq_two_mul_integral_Ioi hint (fun w ↦ by rw [abs_neg, neg_sq]) hc, hIoi,
    integral_Ioi_pow_three_mul_exp_neg_mul_sq hb c]
  ring
theorem integral_compl_Icc_sq_mul_exp_neg_mul_sq_le (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, w ^ 2 * exp (-b * w ^ 2)
      ≤ exp (-b * c ^ 2) * (c / b + 1 / (b ^ 2 * c)) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have h2 : IntegrableOn (fun w : ℝ ↦ w ^ 2 * exp (-b * w ^ 2)) (Set.Icc (-c) c)ᶜ := by
    simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).integrableOn
  have h3 : IntegrableOn (fun w : ℝ ↦ c⁻¹ * (|w| ^ 3 * exp (-b * w ^ 2))) (Set.Icc (-c) c)ᶜ :=
    ((integrable_abs_pow_mul_exp_neg_mul_sq hb 3).const_mul c⁻¹).integrableOn
  calc ∫ w in (Set.Icc (-c) c)ᶜ, w ^ 2 * exp (-b * w ^ 2)
      ≤ ∫ w in (Set.Icc (-c) c)ᶜ, c⁻¹ * (|w| ^ 3 * exp (-b * w ^ 2)) := by
        refine setIntegral_mono_on h2 h3 measurableSet_Icc.compl fun w hw ↦ ?_
        have hwc : c ≤ |w| := (lt_abs_of_mem_compl_Icc hw).le
        have hpow : w ^ 2 ≤ c⁻¹ * |w| ^ 3 := by
          rw [← sq_abs w, inv_mul_eq_div, le_div_iff₀ hc]
          nlinarith [abs_nonneg w]
        calc w ^ 2 * exp (-b * w ^ 2) ≤ c⁻¹ * |w| ^ 3 * exp (-b * w ^ 2) :=
              mul_le_mul_of_nonneg_right hpow (exp_pos _).le
          _ = c⁻¹ * (|w| ^ 3 * exp (-b * w ^ 2)) := by ring
    _ = c⁻¹ * (exp (-b * c ^ 2) * (c ^ 2 / b + 1 / b ^ 2)) := by
        rw [integral_const_mul, integral_compl_Icc_abs_pow_three_mul_exp_neg_mul_sq hb hc.le]
    _ = exp (-b * c ^ 2) * (c / b + 1 / (b ^ 2 * c)) := by
        field_simp
private theorem exp_neg_mul_sq_mul_poly_eq (b c₀ c₁ c₂ c₃ : ℝ) :
    (fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₁ * |w| + c₂ * w ^ 2 + c₃ * |w| ^ 3))
      = fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2))
          + c₂ * (w ^ 2 * exp (-b * w ^ 2)) + c₃ * (|w| ^ 3 * exp (-b * w ^ 2)) := by
  funext w
  ring
theorem integrable_exp_neg_mul_sq_mul_poly (hb : 0 < b) (c₀ c₁ c₂ c₃ : ℝ) :
    Integrable fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₁ * |w| + c₂ * w ^ 2 + c₃ * |w| ^ 3) := by
  rw [exp_neg_mul_sq_mul_poly_eq]
  refine (((((integrable_exp_neg_mul_sq hb).const_mul c₀).add ?_).add ?_).add ?_)
  · simpa using (integrable_abs_pow_mul_exp_neg_mul_sq hb 1).const_mul c₁
  · simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂
  · exact (integrable_abs_pow_mul_exp_neg_mul_sq hb 3).const_mul c₃
theorem integral_exp_neg_mul_sq_mul_poly (hb : 0 < b) (c₀ c₁ c₂ c₃ : ℝ) :
    ∫ w : ℝ, exp (-b * w ^ 2) * (c₀ + c₁ * |w| + c₂ * w ^ 2 + c₃ * |w| ^ 3)
      = c₀ * √(π / b) + c₁ / b + c₂ * (√(π / b) / (2 * b)) + c₃ / b ^ 2 := by
  have e0 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) :=
    (integrable_exp_neg_mul_sq hb).const_mul c₀
  have e1 : Integrable fun w : ℝ ↦ c₁ * (|w| * exp (-b * w ^ 2)) := by
    simpa using (integrable_abs_pow_mul_exp_neg_mul_sq hb 1).const_mul c₁
  have e2 : Integrable fun w : ℝ ↦ c₂ * (w ^ 2 * exp (-b * w ^ 2)) := by
    simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂
  have e3 : Integrable fun w : ℝ ↦ c₃ * (|w| ^ 3 * exp (-b * w ^ 2)) :=
    (integrable_abs_pow_mul_exp_neg_mul_sq hb 3).const_mul c₃
  have e01 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2)) :=
    e0.add e1
  have e012 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2))
      + c₂ * (w ^ 2 * exp (-b * w ^ 2)) := e01.add e2
  rw [exp_neg_mul_sq_mul_poly_eq, integral_add e012 e3, integral_add e01 e2, integral_add e0 e1,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_gaussian, integral_abs_mul_exp_neg_mul_sq hb, integral_sq_mul_exp_neg_mul_sq hb,
    integral_abs_pow_three_mul_exp_neg_mul_sq hb]
  ring
theorem integral_compl_Icc_exp_neg_mul_sq_mul_poly_le (hb : 0 < b) {A : ℝ} (hA : 0 < A)
    (hbA : 1 ≤ b * A ^ 2) {c₀ c₁ c₂ c₃ : ℝ} (h₀ : 0 ≤ c₀) (h₂ : 0 ≤ c₂) (h₃ : 0 ≤ c₃) :
    ∫ w in (Set.Icc (-A) A)ᶜ, exp (-b * w ^ 2) * (c₀ + c₁ * |w| + c₂ * w ^ 2 + c₃ * |w| ^ 3)
      ≤ exp (-b * A ^ 2) / b * (c₀ / A + c₁ + 2 * c₂ * A + 2 * c₃ * A ^ 2) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hA0 : A ≠ 0 := hA.ne'
  have hE : (0 : ℝ) < exp (-b * A ^ 2) := exp_pos _
  set s : Set ℝ := (Set.Icc (-A) A)ᶜ with hs
  have e0 : IntegrableOn (fun w : ℝ ↦ c₀ * exp (-b * w ^ 2)) s :=
    ((integrable_exp_neg_mul_sq hb).const_mul c₀).integrableOn
  have e1 : IntegrableOn (fun w : ℝ ↦ c₁ * (|w| * exp (-b * w ^ 2))) s := by
    simpa using ((integrable_abs_pow_mul_exp_neg_mul_sq hb 1).const_mul c₁).integrableOn
  have e2 : IntegrableOn (fun w : ℝ ↦ c₂ * (w ^ 2 * exp (-b * w ^ 2))) s := by
    simpa [sq_abs] using ((integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂).integrableOn
  have e3 : IntegrableOn (fun w : ℝ ↦ c₃ * (|w| ^ 3 * exp (-b * w ^ 2))) s :=
    ((integrable_abs_pow_mul_exp_neg_mul_sq hb 3).const_mul c₃).integrableOn
  have e01 : IntegrableOn (fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2))) s :=
    e0.add e1
  have e012 : IntegrableOn (fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2))
      + c₂ * (w ^ 2 * exp (-b * w ^ 2))) s := e01.add e2
  have b0 : ∫ w in s, c₀ * exp (-b * w ^ 2) ≤ c₀ * (exp (-b * A ^ 2) / (b * A)) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_compl_Icc_exp_neg_mul_sq_le hb hA) h₀
  have b1 : ∫ w in s, c₁ * (|w| * exp (-b * w ^ 2)) = c₁ * (exp (-b * A ^ 2) / b) := by
    rw [integral_const_mul, integral_compl_Icc_abs_mul_exp_neg_mul_sq hb hA.le]
  have b2 : ∫ w in s, c₂ * (w ^ 2 * exp (-b * w ^ 2))
      ≤ c₂ * (exp (-b * A ^ 2) * (A / b + 1 / (b ^ 2 * A))) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_compl_Icc_sq_mul_exp_neg_mul_sq_le hb hA) h₂
  have b3 : ∫ w in s, c₃ * (|w| ^ 3 * exp (-b * w ^ 2))
      = c₃ * (exp (-b * A ^ 2) * (A ^ 2 / b + 1 / b ^ 2)) := by
    rw [integral_const_mul, integral_compl_Icc_abs_pow_three_mul_exp_neg_mul_sq hb hA.le]
  have hd2 : 1 / (b ^ 2 * A) ≤ A / b := by
    rw [div_le_div_iff₀ (by positivity) hb]
    nlinarith
  have hd3 : 1 / b ^ 2 ≤ A ^ 2 / b := by
    rw [div_le_div_iff₀ (by positivity) hb]
    nlinarith
  have g2 : c₂ * (exp (-b * A ^ 2) * (A / b + 1 / (b ^ 2 * A)))
      ≤ c₂ * (exp (-b * A ^ 2) * (2 * A / b)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hE.le) h₂
    rw [show 2 * A / b = A / b + A / b by ring]
    linarith
  have g3 : c₃ * (exp (-b * A ^ 2) * (A ^ 2 / b + 1 / b ^ 2))
      ≤ c₃ * (exp (-b * A ^ 2) * (2 * A ^ 2 / b)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hE.le) h₃
    rw [show 2 * A ^ 2 / b = A ^ 2 / b + A ^ 2 / b by ring]
    linarith
  have hsum : c₀ * (exp (-b * A ^ 2) / (b * A)) + c₁ * (exp (-b * A ^ 2) / b)
      + c₂ * (exp (-b * A ^ 2) * (2 * A / b)) + c₃ * (exp (-b * A ^ 2) * (2 * A ^ 2 / b))
      = exp (-b * A ^ 2) / b * (c₀ / A + c₁ + 2 * c₂ * A + 2 * c₃ * A ^ 2) := by
    field_simp
  rw [exp_neg_mul_sq_mul_poly_eq, integral_add e012 e3, integral_add e01 e2, integral_add e0 e1]
  linarith
private theorem setIntegral_comp_add_right_le_of_nonneg {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ u : ℝ, 0 ≤ f u) {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) (d : ℝ)
    (hst : ∀ w ∈ s, w + d ∈ t) :
    ∫ w in s, f (w + d) ≤ ∫ u in t, f u := by
  have hR : ∫ w : ℝ, t.indicator f (w + d) = ∫ u : ℝ, t.indicator f u :=
    integral_add_right_eq_self (t.indicator f) d
  rw [← integral_indicator hs, ← integral_indicator ht, ← hR]
  refine integral_mono ((hf.comp_add_right d).indicator hs)
    ((hf.indicator ht).comp_add_right d) fun w ↦ ?_
  by_cases hw : w ∈ s
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (hst w hw)]
  · rw [Set.indicator_of_notMem hw]
    exact Set.indicator_nonneg (fun u _ ↦ hf0 u) _
theorem integral_compl_Icc_exp_neg_mul_sq_mul_poly_comp_add_right_le (hb : 0 < b) {W d A : ℝ}
    (hA : 0 < A) (hAW : A + |d| ≤ W) (hbA : 1 ≤ b * A ^ 2) {c₀ c₁ c₂ c₃ : ℝ} (h₀ : 0 ≤ c₀)
    (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (h₃ : 0 ≤ c₃) :
    ∫ w in (Set.Icc (-W) W)ᶜ, exp (-b * (w + d) ^ 2) *
        (c₀ + c₁ * |w + d| + c₂ * (w + d) ^ 2 + c₃ * |w + d| ^ 3)
      ≤ exp (-b * A ^ 2) / b * (c₀ / A + c₁ + 2 * c₂ * A + 2 * c₃ * A ^ 2) := by
  refine le_trans (setIntegral_comp_add_right_le_of_nonneg
    (integrable_exp_neg_mul_sq_mul_poly hb c₀ c₁ c₂ c₃)
    (fun u ↦ by positivity) measurableSet_Icc.compl measurableSet_Icc.compl d fun w hw ↦ ?_)
    (integral_compl_Icc_exp_neg_mul_sq_mul_poly_le hb hA hbA h₀ h₂ h₃)
  have hwW : W < |w| := lt_abs_of_mem_compl_Icc hw
  have hshift : A < |w + d| := by
    have h := abs_sub_abs_le_abs_sub w (-d)
    rw [abs_neg, sub_neg_eq_add] at h
    linarith
  rw [Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le]
  exact hshift
theorem integral_compl_Icc_exp_neg_mul_sq_comp_add_right_le (hb : 0 < b) {W d A : ℝ} (hA : 0 < A)
    (hAW : A + |d| ≤ W) (hbA : 1 ≤ b * A ^ 2) :
    ∫ w in (Set.Icc (-W) W)ᶜ, exp (-b * (w + d) ^ 2) ≤ exp (-b * A ^ 2) / (b * A) := by
  have h := integral_compl_Icc_exp_neg_mul_sq_mul_poly_comp_add_right_le hb hA hAW hbA
    (c₀ := 1) (c₁ := 0) (c₂ := 0) (c₃ := 0) zero_le_one le_rfl le_rfl le_rfl
  simp only [mul_zero, zero_mul, add_zero, mul_one] at h
  calc ∫ w in (Set.Icc (-W) W)ᶜ, exp (-b * (w + d) ^ 2)
      ≤ exp (-b * A ^ 2) / b * (1 / A) := h
    _ = exp (-b * A ^ 2) / (b * A) := by ring
private theorem exp_neg_mul_sq_mul_even_poly_eq (b c₀ c₂ c₄ c₆ : ℝ) :
    (fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₂ * w ^ 2 + c₄ * w ^ 4 + c₆ * w ^ 6))
      = fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₂ * (w ^ 2 * exp (-b * w ^ 2))
          + c₄ * (w ^ 4 * exp (-b * w ^ 2)) + c₆ * (w ^ 6 * exp (-b * w ^ 2)) := by
  funext w
  ring
theorem integrable_exp_neg_mul_sq_mul_even_poly (hb : 0 < b) (c₀ c₂ c₄ c₆ : ℝ) :
    Integrable fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₂ * w ^ 2 + c₄ * w ^ 4 + c₆ * w ^ 6) := by
  rw [exp_neg_mul_sq_mul_even_poly_eq]
  refine ((((integrable_exp_neg_mul_sq hb).const_mul c₀).add ?_).add ?_).add ?_
  · simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂
  · simpa [even_four.pow_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 4).const_mul c₄
  · simpa [even_six.pow_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 6).const_mul c₆
theorem integral_exp_neg_mul_sq_mul_even_poly (hb : 0 < b) (c₀ c₂ c₄ c₆ : ℝ) :
    ∫ w : ℝ, exp (-b * w ^ 2) * (c₀ + c₂ * w ^ 2 + c₄ * w ^ 4 + c₆ * w ^ 6)
      = (c₀ + c₂ / (2 * b) + 3 * c₄ / (4 * b ^ 2) + 15 * c₆ / (8 * b ^ 3)) * √(π / b) := by
  have hb0 : b ≠ 0 := hb.ne'
  have e0 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) :=
    (integrable_exp_neg_mul_sq hb).const_mul c₀
  have e2 : Integrable fun w : ℝ ↦ c₂ * (w ^ 2 * exp (-b * w ^ 2)) := by
    simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂
  have e4 : Integrable fun w : ℝ ↦ c₄ * (w ^ 4 * exp (-b * w ^ 2)) := by
    simpa [even_four.pow_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 4).const_mul c₄
  have e6 : Integrable fun w : ℝ ↦ c₆ * (w ^ 6 * exp (-b * w ^ 2)) := by
    simpa [even_six.pow_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 6).const_mul c₆
  have e02 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₂ * (w ^ 2 * exp (-b * w ^ 2)) :=
    e0.add e2
  have e024 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₂ * (w ^ 2 * exp (-b * w ^ 2))
      + c₄ * (w ^ 4 * exp (-b * w ^ 2)) := e02.add e4
  rw [exp_neg_mul_sq_mul_even_poly_eq, integral_add e024 e6, integral_add e02 e4,
    integral_add e0 e2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_gaussian, integral_sq_mul_exp_neg_mul_sq hb,
    integral_pow_four_mul_exp_neg_mul_sq hb, integral_pow_six_mul_exp_neg_mul_sq hb]
  field_simp
theorem integral_exp_neg_mul_sq_mul_even_poly_comp_add_right (hb : 0 < b) (c₀ c₂ c₄ c₆ d : ℝ) :
    ∫ w : ℝ, exp (-b * (w + d) ^ 2) *
        (c₀ + c₂ * (w + d) ^ 2 + c₄ * (w + d) ^ 4 + c₆ * (w + d) ^ 6)
      = (c₀ + c₂ / (2 * b) + 3 * c₄ / (4 * b ^ 2) + 15 * c₆ / (8 * b ^ 3)) * √(π / b) := by
  rw [show (∫ w : ℝ, exp (-b * (w + d) ^ 2) *
        (c₀ + c₂ * (w + d) ^ 2 + c₄ * (w + d) ^ 4 + c₆ * (w + d) ^ 6))
      = ∫ w : ℝ, (fun u : ℝ ↦ exp (-b * u ^ 2) *
        (c₀ + c₂ * u ^ 2 + c₄ * u ^ 4 + c₆ * u ^ 6)) (w + d) from rfl,
    integral_add_right_eq_self (fun u : ℝ ↦ exp (-b * u ^ 2) *
      (c₀ + c₂ * u ^ 2 + c₄ * u ^ 4 + c₆ * u ^ 6)) d,
    integral_exp_neg_mul_sq_mul_even_poly hb]
theorem integrable_exp_neg_mul_sq_mul_even_quartic (hb : 0 < b) (c₀ c₂ c₄ : ℝ) :
    Integrable fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₂ * w ^ 2 + c₄ * w ^ 4) := by
  simpa using integrable_exp_neg_mul_sq_mul_even_poly hb c₀ c₂ c₄ 0
theorem integral_exp_neg_mul_sq_mul_even_quartic_comp_add_right (hb : 0 < b) (c₀ c₂ c₄ d : ℝ) :
    ∫ w : ℝ, exp (-b * (w + d) ^ 2) * (c₀ + c₂ * (w + d) ^ 2 + c₄ * (w + d) ^ 4)
      = (c₀ + c₂ / (2 * b) + 3 * c₄ / (4 * b ^ 2)) * √(π / b) := by
  simpa using integral_exp_neg_mul_sq_mul_even_poly_comp_add_right hb c₀ c₂ c₄ 0 d
end Moments
end
end CertificatePort88

section CertificatePort89
section
open scoped Real
namespace Complex
theorem exp_mul_I_sub_exp_neg_mul_I (z : ℂ) : exp (z * I) - exp (-(z * I)) = 2 * I * sin z := by
  rw [show (-(z * I)) = (-z) * I by ring, exp_mul_I, exp_mul_I, cos_neg, sin_neg]
  ring
theorem exp_neg_two_pi_mul_I_div_sub_eq {z : ℂ} (hz : exp (π * I * z) ≠ exp (-(π * I * z))) :
    exp (-(2 * π * I * z)) / (exp (π * I * z) - exp (-(π * I * z)))
      = 1 / (exp (π * I * z) - exp (-(π * I * z))) - exp (-(π * I * z)) := by
  have hden : exp ((π : ℂ) * I * z) - exp (-(π * I * z)) ≠ 0 := sub_ne_zero_of_ne hz
  have key : exp (-(2 * (π : ℂ) * I * z))
      = 1 - exp (-((π : ℂ) * I * z)) * (exp ((π : ℂ) * I * z) - exp (-((π : ℂ) * I * z))) := by
    rw [mul_sub, ← exp_add, ← exp_add,
      show -((π : ℂ) * I * z) + (π : ℂ) * I * z = 0 by ring, exp_zero,
      show -((π : ℂ) * I * z) + -((π : ℂ) * I * z) = -(2 * (π : ℂ) * I * z) by ring]
    ring
  rw [key, sub_div, mul_div_assoc, div_self hden, mul_one]
theorem exp_pi_div_four_mul_I :
    exp ((π / 4 : ℝ) * I) = (Real.sqrt 2 / 2 : ℝ) + (Real.sqrt 2 / 2 : ℝ) * I := by
  rw [exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
theorem exp_neg_pi_div_four_mul_I :
    exp (-((π / 4 : ℝ) * I)) = (Real.sqrt 2 / 2 : ℝ) - (Real.sqrt 2 / 2 : ℝ) * I := by
  rw [show -(((π / 4 : ℝ) : ℂ) * I) = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  push_cast
  ring
theorem exp_neg_pi_div_four_mul_I_mul_exp :
    exp (-((π / 4 : ℝ) * I)) * exp ((π / 4 : ℝ) * I) = 1 := by
  rw [← exp_add, neg_add_cancel, exp_zero]
theorem exp_pi_div_four_mul_I_mul_exp_neg :
    exp ((π / 4 : ℝ) * I) * exp (-((π / 4 : ℝ) * I)) = 1 := by
  rw [mul_comm]
  exact exp_neg_pi_div_four_mul_I_mul_exp
theorem exp_pi_div_four_mul_I_mul_self :
    exp ((π / 4 : ℝ) * I) * exp ((π / 4 : ℝ) * I) = I := by
  rw [← exp_add, show ((π / 4 : ℝ) : ℂ) * I + ((π / 4 : ℝ) : ℂ) * I = (π : ℂ) / 2 * I by
    push_cast; ring, exp_pi_div_two_mul_I]
theorem I_mul_exp_neg_pi_div_four_mul_I :
    I * exp (-((π / 4 : ℝ) * I)) = exp ((π / 4 : ℝ) * I) := by
  linear_combination (-exp (-((π / 4 : ℝ) * I))) * exp_pi_div_four_mul_I_mul_self +
    exp ((π / 4 : ℝ) * I) * exp_pi_div_four_mul_I_mul_exp_neg
theorem exp_neg_pi_div_four_mul_I_mul_self :
    exp (-((π / 4 : ℝ) * I)) * exp (-((π / 4 : ℝ) * I)) = -I := by
  rw [← exp_add, show -(((π / 4 : ℝ) : ℂ) * I) + -(((π / 4 : ℝ) : ℂ) * I) = -((π : ℂ) / 2 * I) by
    push_cast; ring, exp_neg, exp_pi_div_two_mul_I, inv_I]
theorem norm_one_add_I : ‖(1 + I : ℂ)‖ = Real.sqrt 2 := by
  rw [← Real.sqrt_sq (norm_nonneg ((1 : ℂ) + I)), Complex.sq_norm, Complex.normSq_apply]
  norm_num
theorem exp_neg_pi_div_four_mul_I_mul_re (z : ℂ) :
    (exp (-((π / 4 : ℝ) * I)) * z).re = Real.sqrt 2 / 2 * (z.re + z.im) := by
  rw [exp_neg_pi_div_four_mul_I]; simp [Complex.mul_re]; ring
theorem exp_neg_pi_div_four_mul_I_mul_im (z : ℂ) :
    (exp (-((π / 4 : ℝ) * I)) * z).im = Real.sqrt 2 / 2 * (z.im - z.re) := by
  rw [exp_neg_pi_div_four_mul_I]; simp [Complex.mul_im]; ring
theorem exp_pi_div_four_mul_I_div_sqrt_two :
    exp ((π / 4 : ℝ) * I) / (Real.sqrt 2 : ℂ) = (1 + I) / 2 := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.2 (by positivity)
  rw [exp_pi_div_four_mul_I, div_eq_div_iff h2 two_ne_zero]
  push_cast
  ring
theorem sin_pi_mul_ne_zero {z : ℂ} (hz : ∀ n : ℤ, z ≠ n) : sin (π * z) ≠ 0 := by
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  exact sin_ne_zero_iff.2 fun k h ↦ hz k (mul_left_cancel₀ hpi (by rw [h]; ring))
theorem norm_sin_sq (z : ℂ) : ‖sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  have h : sin z = ((Real.sin z.re * Real.cosh z.im : ℝ) : ℂ)
      + ((Real.cos z.re * Real.sinh z.im : ℝ) : ℂ) * I := by
    rw [sin_eq]; push_cast; ring
  rw [h, Complex.sq_norm, normSq_add_mul_I, mul_pow, mul_pow, Real.cosh_sq]
  nlinarith [Real.sin_sq_add_cos_sq z.re]
theorem sinh_abs_im_le_norm_sin (z : ℂ) : Real.sinh |z.im| ≤ ‖sin z‖ := by
  have h0 : (0 : ℝ) ≤ Real.sinh |z.im| := by
    rw [Real.sinh_eq]
    have := Real.exp_le_exp.2 (neg_le_self (abs_nonneg z.im))
    linarith
  have hsq : Real.sinh |z.im| ^ 2 = Real.sinh z.im ^ 2 := by
    rcases abs_choice z.im with h | h
    · rw [h]
    · rw [h, Real.sinh_neg, neg_sq]
  nlinarith [norm_sin_sq z, sq_nonneg (Real.sin z.re), norm_nonneg (sin z)]
theorem one_le_norm_sin_pi_mul {z : ℂ} (hz : Real.sqrt 2 / 2 ≤ |z.im|) : 1 ≤ ‖sin (π * z)‖ := by
  have hpi := Real.pi_gt_three
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have him : |((π : ℂ) * z).im| = π * |z.im| := by
    rw [show ((π : ℂ) * z).im = π * z.im by simp [Complex.mul_im], abs_mul,
      abs_of_pos Real.pi_pos]
  have h1 : (1 : ℝ) ≤ |((π : ℂ) * z).im| := by
    rw [him]
    nlinarith [mul_le_mul_of_nonneg_left hz Real.pi_pos.le]
  exact (h1.trans (Real.self_le_sinh_iff.2 (abs_nonneg _))).trans (sinh_abs_im_le_norm_sin _)
theorem norm_exp_pi_mul_I_mul_sq (z : ℂ) :
    ‖exp (π * I * z ^ 2)‖ = Real.exp (-(2 * π * z.re * z.im)) := by
  rw [norm_exp]
  congr 1
  simp only [sq, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  ring
theorem norm_exp_two_pi_mul_I_mul_sq (z : ℂ) :
    ‖exp (2 * π * I * z ^ 2)‖ = Real.exp (-(4 * π * z.re * z.im)) := by
  rw [norm_exp]
  congr 1
  simp only [sq, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
  ring
end Complex
end
end CertificatePort89

section CertificatePort90
section
open Complex
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def line (a w : ℝ) : ℂ := (a + w : ℝ) + (w : ℝ) * I
@[simp]
theorem line_re (a w : ℝ) : (line a w).re = a + w := by simp [line]
@[simp]
theorem line_im (a w : ℝ) : (line a w).im = w := by simp [line]
theorem line_ne_zero {a : ℝ} (ha : a ≠ 0) (w : ℝ) : line a w ≠ 0 := by
  simp only [ne_eq, Complex.ext_iff, line_re, line_im, Complex.zero_re, Complex.zero_im, not_and]
  exact fun h hw ↦ ha (by rw [hw] at h; linarith)
theorem line_add_one (a w : ℝ) : line (a + 1) w = line a w + 1 := by
  rw [line, line]; push_cast; ring
@[fun_prop]
theorem continuous_line (a : ℝ) : Continuous (line a) := by
  unfold line; fun_prop
theorem exp_pi_div_four_mul_I_mul_line (a w : ℝ) :
    exp ((π / 4 : ℝ) * I) * line a w
      = (Real.sqrt 2 / 2 : ℝ) * ((a : ℂ) + ((a : ℂ) + 2 * w) * I) := by
  rw [exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four, line]
  push_cast
  linear_combination (Real.sqrt 2 : ℂ) * (w : ℂ) * (1 / 2) * Complex.I_sq
theorem line_zero (w : ℝ) : line 0 w = ((Real.sqrt 2 * w : ℝ) : ℂ) * exp ((π / 4 : ℝ) * I) := by
  refine mul_left_cancel₀ (exp_ne_zero (((π / 4 : ℝ) : ℂ) * I)) ?_
  rw [exp_pi_div_four_mul_I_mul_line, ← mul_assoc,
    mul_comm (exp (((π / 4 : ℝ) : ℂ) * I)) (((Real.sqrt 2 * w : ℝ) : ℂ)), mul_assoc,
    Complex.exp_pi_div_four_mul_I_mul_self]
  push_cast; ring
theorem re_exp_pi_div_four_mul_I_mul_line (a w : ℝ) :
    (exp ((π / 4 : ℝ) * I) * line a w).re = a / Real.sqrt 2 := by
  rw [exp_pi_div_four_mul_I_mul_line, Complex.re_ofReal_mul,
    show ((a : ℂ) + ((a : ℂ) + 2 * w) * I).re = a by simp,
    eq_div_iff (by positivity : Real.sqrt 2 ≠ 0)]
  linear_combination (a / 2) * Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
theorem re_exp_pi_div_four_mul_I_mul_ofReal (r : ℝ) :
    (exp ((π / 4 : ℝ) * I) * (r : ℂ)).re = r / Real.sqrt 2 := by
  simpa [line] using re_exp_pi_div_four_mul_I_mul_line r 0
theorem norm_line_sq (a w : ℝ) : ‖line a w‖ ^ 2 = (a ^ 2 + (a + 2 * w) ^ 2) / 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, line_re, line_im]
  ring
theorem norm_line_ge (a w : ℝ) : a / Real.sqrt 2 ≤ ‖line a w‖ :=
  le_of_sq_le_sq (by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), norm_line_sq]
    nlinarith [sq_nonneg (a + 2 * w)]) (norm_nonneg _)
theorem norm_line_le {a : ℝ} (ha0 : 0 ≤ a) (w : ℝ) : ‖line a w‖ ≤ a + 2 * |w| := by
  nlinarith [norm_line_sq a w, norm_nonneg (line a w), sq_abs w, le_abs_self w, abs_nonneg w,
    mul_nonneg ha0 (abs_nonneg w)]
theorem abs_log_norm_line_le {a : ℝ} (ha0 : 0 < a) (w : ℝ) :
    |Real.log ‖line a w‖| ≤ |Real.log (a / Real.sqrt 2)| + a + 2 * |w| := by
  have hup : Real.log ‖line a w‖ ≤ a + 2 * |w| :=
    (Real.log_le_sub_one_of_pos (norm_pos_iff.2 (line_ne_zero ha0.ne' w))).trans
      (by linarith [norm_line_le ha0.le w])
  have hlow : Real.log (a / Real.sqrt 2) ≤ Real.log ‖line a w‖ :=
    Real.log_le_log (by positivity) (norm_line_ge a w)
  exact abs_le.2 ⟨by linarith [abs_nonneg w, neg_abs_le (Real.log (a / Real.sqrt 2))],
    by linarith [abs_nonneg (Real.log (a / Real.sqrt 2))]⟩
theorem norm_line_sub_ofReal_le (a w p : ℝ) :
    ‖line a w - (p : ℂ)‖ ≤ |a - p| + Real.sqrt 2 * |w| := by
  rw [show line a w - (p : ℂ) = ((a - p : ℝ) : ℂ) + (w : ℂ) * (1 + I) by
    rw [line]; push_cast; ring]
  refine (norm_add_le _ _).trans_eq ?_
  rw [Complex.norm_real, norm_mul, Complex.norm_real, norm_one_add_I, Real.norm_eq_abs,
    Real.norm_eq_abs, mul_comm]
theorem norm_line_sub_ofReal_sq (a w p : ℝ) :
    ‖line a w - (p : ℂ)‖ ^ 2 = 2 * (w + (a - p) / 2) ^ 2 + (a - p) ^ 2 / 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, line_re, line_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring
theorem norm_line_sub_ofReal_le' (a w p : ℝ) :
    ‖line a w - (p : ℂ)‖ ≤ Real.sqrt 2 * (|w + (a - p) / 2| + |a - p| / 2) := by
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [norm_line_sub_ofReal_sq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [sq_abs (w + (a - p) / 2), sq_abs (a - p), abs_nonneg (w + (a - p) / 2),
    abs_nonneg (a - p)]
theorem sinh_le_norm_sin_pi_mul_line (a w : ℝ) :
    Real.sinh (π * |w|) ≤ ‖sin (π * line a w)‖ := by
  simpa [Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos] using
    Complex.sinh_abs_im_le_norm_sin ((π : ℂ) * line a w)
theorem abs_sin_le_norm_sin_pi_mul_line (a w : ℝ) :
    |Real.sin (π * (a + w))| ≤ ‖sin (π * line a w)‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [sq_abs, Complex.norm_sin_sq,
    show ((π : ℂ) * line a w).re = π * (a + w) by simp [Complex.mul_re]]
  linarith [sq_nonneg (Real.sinh ((π : ℂ) * line a w).im)]
theorem norm_sin_pi_mul_line_ge {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) (w : ℝ) :
    Real.sqrt 2 / 2 ≤ ‖sin (π * line a w)‖ := by
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  rcases le_or_gt (1 / 4 : ℝ) |w| with hw | hw
  ·
    refine le_trans ?_ ((Real.self_le_sinh_iff.2 (by positivity)).trans
      (sinh_le_norm_sin_pi_mul_line a w))
    nlinarith [Real.pi_gt_three]
  refine le_trans ?_ (abs_sin_le_norm_sin_pi_mul_line a w)
  have hsin : Real.sin (π * (a + w)) = (-1 : ℝ) ^ n * Real.cos (π * w) := by
    rw [ha, show π * ((n : ℝ) + 1 / 2 + w) = π * w + π / 2 + n * π by ring,
      Real.sin_add_int_mul_pi, Real.sin_add_pi_div_two]
  have hcos : Real.sqrt 2 / 2 ≤ Real.cos (π * w) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (π * w))
      (by linarith [Real.pi_pos] : π / 4 ≤ π)
      (by rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [Real.pi_pos])
    rwa [Real.cos_pi_div_four, Real.cos_abs] at h
  rw [hsin, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  exact hcos.trans (le_abs_self _)
theorem sin_pi_mul_line_ne_zero {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) (w : ℝ) :
    sin (π * line a w) ≠ 0 :=
  norm_pos_iff.1 <| lt_of_lt_of_le (by positivity) (norm_sin_pi_mul_line_ge ha w)
theorem norm_sin_pi_mul_line_ge_min {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (w : ℝ) :
    min (1 / 2) ‖line a w‖ ≤ ‖sin (π * line a w)‖ := by
  have hpi3 := Real.pi_gt_three
  have hsin := abs_sin_le_norm_sin_pi_mul_line a w
  have hsinh : π * |w| ≤ ‖sin (π * line a w)‖ :=
    (Real.self_le_sinh_iff.2 (by positivity)).trans (sinh_le_norm_sin_pi_mul_line a w)
  rcases le_or_gt (1 / 4 : ℝ) |w| with hw | hw
  ·
    exact (min_le_left _ _).trans (by nlinarith)
  obtain ⟨hw1, hw2⟩ := abs_lt.1 hw
  rcases le_or_gt |a + w| (1 / 2 : ℝ) with hu | hu
  ·
    have hj : 2 * |a + w| ≤ ‖sin (π * line a w)‖ := by
      have h := Real.mul_abs_le_abs_sin (x := π * (a + w))
        (by rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith)
      rw [abs_mul, abs_of_pos Real.pi_pos, ← mul_assoc, div_mul_cancel₀ _ Real.pi_ne_zero] at h
      exact h.trans hsin
    refine (min_le_right _ _).trans ((Complex.norm_le_abs_re_add_abs_im _).trans ?_)
    rw [line_re, line_im]
    nlinarith [abs_nonneg w, norm_nonneg (sin (π * line a w))]
  ·
    refine (min_le_left _ _).trans (le_trans ?_ ((le_abs_self _).trans hsin))
    have hu' : 1 / 2 < a + w := by rcases abs_cases (a + w) with h | h <;> linarith [h.1]
    have ht : π * (a + w) - π / 2 < 1 := by
      nlinarith [Real.pi_lt_four, mul_lt_mul_of_pos_left
        (show a + w - 1 / 2 < 1 / 4 by linarith) Real.pi_pos]
    rw [← Real.cos_sub_pi_div_two]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := π * (a + w) - π / 2),
      mul_pos Real.pi_pos (show (0 : ℝ) < a + w - 1 / 2 by linarith)]
theorem le_exp_of_le_pow {n : ℕ} {c x : ℝ} (hc : c ≤ 2.718 ^ n) (hx : (n : ℝ) ≤ x) :
    c ≤ Real.exp x :=
  hc.trans (((pow_le_pow_left₀ (by norm_num)
    (by linarith [Real.exp_one_gt_d9] : (2.718 : ℝ) ≤ Real.exp 1) n).trans_eq
      (Real.exp_one_pow n)).trans (Real.exp_le_exp.2 hx))
theorem exp_neg_mul_le_one {n : ℕ} {c x : ℝ} (hc : c ≤ 2.718 ^ n) (hx : (n : ℝ) ≤ x) :
    Real.exp (-x) * c ≤ 1 := by
  rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
  linarith [le_exp_of_le_pow hc hx]
theorem mul_exp_le_norm_sin_pi_mul_line (a : ℝ) {w : ℝ} (hw : 1 ≤ |w|) :
    99 / 200 * Real.exp (π * |w|) ≤ ‖sin (π * line a w)‖ := by
  refine le_trans ?_ (sinh_le_norm_sin_pi_mul_line a w)
  have h100 : (100 : ℝ) ≤ Real.exp (π * |w|) * Real.exp (π * |w|) := by
    rw [← Real.exp_add]
    exact le_exp_of_le_pow (n := 6) (by norm_num) (by push_cast; nlinarith [Real.pi_gt_three])
  rw [Real.sinh_eq, Real.exp_neg]
  nlinarith [Real.exp_pos (π * |w|), mul_inv_cancel₀ (Real.exp_ne_zero (π * |w|))]
end Zeta.RiemannSiegel
end
end CertificatePort90

section CertificatePort91
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
theorem mul_pi_mul_I_mul_line_sub_sq (k : ℂ) (a : ℝ) (c : ℂ) (w : ℝ) :
    k * π * I * (line a w - c) ^ 2
      = -2 * k * π * (w : ℂ) ^ 2 + 2 * k * π * I * ((a : ℂ) - c) * (1 + I) * (w : ℂ)
        + k * π * I * ((a : ℂ) - c) ^ 2 := by
  simp only [line, Complex.ofReal_add]
  linear_combination (k * (π : ℂ) * (w : ℂ) ^ 2 * (I + 2)) * Complex.I_sq
theorem integrable_exp_mul_pi_mul_I_mul_line_sub_sq {k : ℝ} (hk : 0 < k) (a : ℝ) (c : ℂ) :
    Integrable fun w : ℝ ↦ exp ((k : ℂ) * π * I * (line a w - c) ^ 2) := by
  have hb : (-2 * (k : ℂ) * π).re < 0 := by simpa using mul_pos (mul_pos two_pos hk) Real.pi_pos
  exact (integrable_cexp_quadratic' hb _ _).congr
    (.of_forall fun w ↦ (congrArg exp (mul_pi_mul_I_mul_line_sub_sq k a c w)).symm)
theorem integral_exp_mul_pi_mul_I_mul_line_sub_sq {k : ℝ} (hk : 0 < k) (a : ℝ) (c : ℂ) :
    (1 + I) * ∫ w : ℝ, exp ((k : ℂ) * π * I * (line a w - c) ^ 2)
      = exp ((π / 4 : ℝ) * I) / (Real.sqrt k : ℂ) := by
  have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk.ne'
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hb : (-2 * (k : ℂ) * π).re < 0 := by simpa using mul_pos (mul_pos two_pos hk) Real.pi_pos
  have hval : (k : ℂ) * π * I * ((a : ℂ) - c) ^ 2
      - (2 * k * π * I * ((a : ℂ) - c) * (1 + I)) ^ 2 / (4 * (-2 * (k : ℂ) * π)) = 0 := by
    rw [show (2 * (k : ℂ) * π * I * ((a : ℂ) - c) * (1 + I)) ^ 2
        = -8 * (k : ℂ) ^ 2 * π ^ 2 * I * ((a : ℂ) - c) ^ 2 by
      linear_combination (4 * (k : ℂ) ^ 2 * (π : ℂ) ^ 2 * ((a : ℂ) - c) ^ 2 * (I ^ 2 + 2 * I)) *
        Complex.I_sq]
    field_simp
    ring
  have hhalf : ((π : ℂ) / -(-2 * (k : ℂ) * π)) ^ (1 / 2 : ℂ)
      = ((Real.sqrt 2 / 2 : ℝ) : ℂ) / (Real.sqrt k : ℂ) := by
    rw [show (π : ℂ) / -(-2 * (k : ℂ) * π) = ((1 / (2 * k) : ℝ) : ℂ) by push_cast; field_simp,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, show Real.sqrt (1 / (2 * k)) = Real.sqrt 2 / 2 / Real.sqrt k by
        rw [show (1 : ℝ) / (2 * k) = (Real.sqrt 2 / 2 / Real.sqrt k) ^ 2 by
          rw [div_pow, div_pow, Real.sq_sqrt hk.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          field_simp, Real.sqrt_sq (by positivity)]]
    push_cast
    ring
  simp only [mul_pi_mul_I_mul_line_sub_sq]
  rw [integral_cexp_quadratic hb, hhalf, hval, exp_zero, mul_one, exp_pi_div_four_mul_I]
  push_cast
  ring
theorem integral_exp_pi_mul_I_mul_line_sub_sq (a : ℝ) (c : ℂ) :
    (1 + I) * ∫ w : ℝ, exp (π * I * (line a w - c) ^ 2) = exp ((π / 4 : ℝ) * I) := by
  simpa using integral_exp_mul_pi_mul_I_mul_line_sub_sq one_pos a c
theorem integrable_exp_two_pi_mul_I_mul_line_sub_sq (a : ℝ) (c : ℂ) :
    Integrable fun w : ℝ ↦ exp (2 * π * I * (line a w - c) ^ 2) := by
  simpa using integrable_exp_mul_pi_mul_I_mul_line_sub_sq two_pos a c
theorem integral_exp_two_pi_mul_I_mul_line_sub_sq (a : ℝ) (c : ℂ) :
    (1 + I) * ∫ w : ℝ, exp (2 * π * I * (line a w - c) ^ 2) = (1 + I) / 2 := by
  rw [← exp_pi_div_four_mul_I_div_sqrt_two]
  simpa using integral_exp_mul_pi_mul_I_mul_line_sub_sq two_pos a c
end Zeta.RiemannSiegel
end
end CertificatePort91

section CertificatePort92
section
open Complex Filter Topology
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def kernel (x : ℂ) : ℂ :=
  exp (π * I * x ^ 2) / (exp (π * I * x) - exp (-(π * I * x)))
theorem kernel_eq_div_two_mul_I_mul_sin (x : ℂ) :
    kernel x = exp (π * I * x ^ 2) / (2 * I * sin (π * x)) := by
  rw [kernel, show ((π : ℂ) * I * x) = (π * x) * I by ring, exp_mul_I_sub_exp_neg_mul_I]
theorem differentiableAt_kernel {x : ℂ} (hx : ∀ n : ℤ, x ≠ n) : DifferentiableAt ℂ kernel x := by
  rw [funext kernel_eq_div_two_mul_I_mul_sin]
  exact DifferentiableAt.div (by fun_prop) (by fun_prop)
    (by simpa [I_ne_zero] using sin_pi_mul_ne_zero hx)
theorem kernel_add_one (x : ℂ) : kernel (x + 1) = exp (2 * π * I * x) * kernel x := by
  rw [kernel_eq_div_two_mul_I_mul_sin, kernel_eq_div_two_mul_I_mul_sin,
    show ((π : ℂ) * (x + 1)) = π * x + π by ring, sin_add_pi,
    show ((π : ℂ) * I * (x + 1) ^ 2) = 2 * π * I * x + π * I * x ^ 2 + π * I by ring,
    exp_add, exp_add, exp_pi_mul_I]
  ring
theorem kernel_neg (x : ℂ) : kernel (-x) = -kernel x := by
  rw [kernel, kernel, neg_sq, show (π : ℂ) * I * -x = -((π : ℂ) * I * x) by ring, neg_neg,
    ← neg_sub, div_neg]
theorem tendsto_sub_mul_kernel (n : ℤ) :
    Tendsto (fun x ↦ (x - n) * kernel x) (𝓝[≠] (n : ℂ)) (𝓝 (1 / (2 * π * I))) := by
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hsin : sin ((π : ℂ) * n) = 0 := sin_eq_zero_iff.2 ⟨n, by ring⟩
  have hgauss : exp ((π : ℂ) * I * (n : ℂ) ^ 2) = cos ((π : ℂ) * n) := by
    obtain ⟨m, hm⟩ : Even (n ^ 2 - n) :=
      (by ring : n * (n - 1) = n ^ 2 - n) ▸ Int.even_mul_pred_self n
    have hm' : ((n : ℂ)) ^ 2 - (n : ℂ) = (m : ℂ) + (m : ℂ) := by exact_mod_cast hm
    rw [show ((π : ℂ) * I * (n : ℂ) ^ 2) = ((π : ℂ) * n) * I + (m : ℂ) * (2 * π * I) from by
      linear_combination ((π : ℂ) * I) * hm', exp_add, exp_int_mul_two_pi_mul_I m, exp_mul_I, hsin]
    ring
  have hcos : cos ((π : ℂ) * n) ≠ 0 := hgauss ▸ exp_ne_zero ((π : ℂ) * I * (n : ℂ) ^ 2)
  have hinv : Tendsto (fun x : ℂ ↦ (x - n) / sin (π * x)) (𝓝[≠] (n : ℂ))
      (𝓝 (cos ((π : ℂ) * n) * π)⁻¹) := by
    have hderiv : HasDerivAt (fun z : ℂ ↦ sin (π * z)) (cos ((π : ℂ) * n) * π) (n : ℂ) := by
      simpa using (HasDerivAt.const_mul (π : ℂ) (hasDerivAt_id (n : ℂ))).csin
    refine ((hasDerivAt_iff_tendsto_slope.1 hderiv).inv₀ (mul_ne_zero hcos hpi)).congr fun x ↦ ?_
    simp only [slope_def_field, hsin, sub_zero, inv_div]
  rw [show (1 : ℂ) / (2 * π * I)
      = exp ((π : ℂ) * I * (n : ℂ) ^ 2) / (2 * I) * (cos ((π : ℂ) * n) * π)⁻¹ from by
    rw [hgauss]; field_simp]
  exact ((((by fun_prop : Continuous fun x : ℂ ↦ exp ((π : ℂ) * I * x ^ 2) / (2 * I)).tendsto
    (n : ℂ)).mono_left nhdsWithin_le_nhds).mul hinv).congr fun x ↦ by
      rw [kernel_eq_div_two_mul_I_mul_sin]; ring
end Zeta.RiemannSiegel
end
end CertificatePort92

section CertificatePort93
section
open scoped Real
namespace Complex
theorem arg_eq_arctan {z : ℂ} (hz : 0 < z.re) : arg z = Real.arctan (z.im / z.re) := by
  obtain ⟨h₁, h₂⟩ := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hz))
  rw [← tan_arg z, Real.arctan_tan h₁ h₂]
theorem arg_exp_ofReal_mul_I_mul {θ : ℝ} {x : ℂ} (hx : x ≠ 0)
    (hθ : arg x + θ ∈ Set.Ioc (-π) π) : arg (exp ((θ : ℂ) * I) * x) = arg x + θ := by
  have hrot : exp ((θ : ℂ) * I) * x
      = (‖x‖ : ℂ) * (cos ((arg x + θ : ℝ) : ℂ) + sin ((arg x + θ : ℝ) : ℂ) * I) := by
    rw [← exp_mul_I]
    push_cast
    rw [show ((arg x : ℂ) + (θ : ℂ)) * I = (arg x : ℂ) * I + (θ : ℂ) * I by ring, exp_add,
      ← mul_assoc, norm_mul_exp_arg_mul_I, mul_comm]
  rw [hrot, arg_mul_cos_add_sin_mul_I (norm_pos_iff.2 hx) hθ]
end Complex
end
end CertificatePort93

section CertificatePort94
section
open scoped Real
namespace Complex
theorem ofReal_mul_exp_mul_I_cpow {r θ : ℝ} (hr : 0 < r) (hθ₁ : -π < θ) (hθ₂ : θ ≤ π) (u : ℂ) :
    ((r : ℂ) * exp ((θ : ℝ) * I)) ^ u = (r : ℂ) ^ u * exp ((θ : ℝ) * I * u) := by
  have hx : (r : ℂ) * exp ((θ : ℝ) * I) = exp ((Real.log r : ℂ) + (θ : ℝ) * I) := by
    rw [exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
  have him : ((Real.log r : ℂ) + ((θ : ℝ) : ℂ) * I).im = θ := by simp
  have h₁ : -π < ((Real.log r : ℂ) + ((θ : ℝ) : ℂ) * I).im := by rw [him]; exact hθ₁
  have h₂ : ((Real.log r : ℂ) + ((θ : ℝ) : ℂ) * I).im ≤ π := by rw [him]; exact hθ₂
  rw [hx, cpow_def_of_ne_zero (exp_ne_zero _), log_exp h₁ h₂,
    cpow_def_of_ne_zero (by exact_mod_cast hr.ne' : (r : ℂ) ≠ 0),
    ← Complex.ofReal_log hr.le, ← exp_add]
  congr 1
  ring
theorem ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (u : ℂ) :
    ((r : ℂ) * z) ^ u = (r : ℂ) ^ u * z ^ u := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hr0 hz), cpow_def_of_ne_zero hr0, cpow_def_of_ne_zero hz,
    ← exp_add, log_ofReal_mul hr hz, ofReal_log hr.le]
  ring_nf
theorem re_exp_mul_I_mul_cpow_neg {x : ℝ} (hx : 0 < x) (t θ : ℝ) :
    (exp (I * θ) * (x : ℂ) ^ (-(1 / 2 + t * I))).re
      = Real.cos (θ - t * Real.log x) / Real.sqrt x := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hsqrt : Real.exp (-Real.log x / 2) = (Real.sqrt x)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, ← Real.exp_neg]
    congr 1
    ring
  have hz : exp (I * θ) * (x : ℂ) ^ (-(1 / 2 + t * I))
      = exp (((-Real.log x / 2 : ℝ) : ℂ) + ((θ - t * Real.log x : ℝ) : ℂ) * I) := by
    rw [cpow_def_of_ne_zero hx0, ← ofReal_log hx.le, ← exp_add]
    congr 1
    push_cast
    ring
  rw [hz, exp_re, add_re, add_im, ofReal_re, ofReal_im, re_ofReal_mul, im_ofReal_mul, I_re, I_im,
    mul_zero, mul_one, add_zero, zero_add, hsqrt]
  ring
end Complex
end
end CertificatePort94


