-- Prove2me | Definitions.Def_PPSLattice_gaussW
-- name    : PPSLattice_gaussW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:08.834982+00:00
-- url     : https://prove2.me/theorems/302c08fb-1830-42a2-a648-5a0c6016dbb0
-- title:
--   Gaussian weight $\rho_\sigma(x)=e^{-x^2/(2\sigma^2)}$
-- statement:
--   For $\sigma\in\mathbb R$ and $x\in\mathbb Z$, $\rho_\sigma(x)=\exp(-x^2/(2\sigma^2))$. For $\sigma>0$ the weights are summable over $\mathbb Z$ (proved in the module).
--
--   **Formalization Note** The paper gives no formula for $D_{\mathbb Z,\sigma}$; this is the convention of [Lyu12], under which Lemma 3.2 is stated.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Discrete Gaussian, p.16

import Mathlib
set_option autoImplicit false

namespace PPSLattice

/-- The **Gaussian weight** `ρ_σ(x) = exp(−x²/(2σ²))` of an integer `x`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Discrete Gaussian, p.16 ("D_{Z,σ} ... with width parameter σ > 0"), with the
convention of [Lyu12] under which Lemma 3.2 is stated. -/
noncomputable def gaussW (σ : ℝ) (x : ℤ) : ℝ := Real.exp (-((x : ℝ) ^ 2) / (2 * σ ^ 2))

/-- The Gaussian weights are summable over `ℤ` for `σ > 0`. -/
theorem gaussW_summable (σ : ℝ) (hσ : 0 < σ) : Summable (gaussW σ) := by
  have hc : 0 < 1 / (2 * σ ^ 2) := by positivity
  have hr1 : Real.exp (-(1 / (2 * σ ^ 2))) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnat : Summable fun n : ℕ => gaussW σ n := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
      (summable_geometric_of_lt_one (Real.exp_pos _).le hr1)
    rw [gaussW, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    have : ((n : ℤ) : ℝ) = (n : ℝ) := by norm_cast
    rw [this, div_eq_mul_one_div, mul_neg, ← neg_mul]
    nlinarith
  refine Summable.of_nat_of_neg hnat ?_
  simpa [gaussW] using hnat

end PPSLattice


