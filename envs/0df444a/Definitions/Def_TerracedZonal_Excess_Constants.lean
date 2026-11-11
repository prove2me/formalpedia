-- Prove2me | Definitions.Def_TerracedZonal_Excess_Constants
-- name    : TerracedZonal_Excess_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:39.736893+00:00
-- url     : https://prove2.me/theorems/5319316a-6a28-462b-a27c-6c22f2342957
-- title:
--   The constants $c_{\mathrm{stretch}}$, $c_{\mathrm{step}}$, $c_{\mathrm{seam}}$, $C_0$, $C(\lambda)$ and $C_1$
-- statement:
--   The constants of TerracedZonal and of Theorem 4.3:
--
--   1. the stretching stiffness $c_{\mathrm{stretch}}=\tfrac14$;
--   2. the nearest-neighbour seam price $c_{\mathrm{step}}=\log\big(1+e^{-\pi\sqrt3}\big)\approx0.0043241$;
--   3. the all-pairs seam cost $c_{\mathrm{seam}}=\sum_{d\ge1}d\log\big(1-(-1)^d e^{-\pi\sqrt3\,d}\big)\approx0.0042867$;
--   4. $C_0=\sqrt{2\pi\sqrt3}$ and $B(\tfrac23,\tfrac56)=\Gamma(\tfrac23)\Gamma(\tfrac56)/\Gamma(\tfrac32)\approx1.724739$;
--   5. for real $\lambda$,
--
--   $$C(\lambda)=\frac{3}{C_0}\Big(\frac{c_{\mathrm{stretch}}\lambda^2C_0^5}{384}\Big)^{1/3}B\big(\tfrac23,\tfrac56\big),\qquad C_1=\frac13\Big(1+\frac{2c_{\mathrm{seam}}}{c_{\mathrm{step}}}\Big)C(c_{\mathrm{step}})\approx0.026225.$$
--
--   $C(\lambda)N^{2/3}$ is the asymptotic minimum of the terrace cost $G_\lambda$ (Lemma E.5), and $C_1$ is the constant of the energy excess in Theorem 4.3.
--
--   **Formalization Note** The series for $c_{\mathrm{seam}}$ is written with $d=n+1$, $n\in\mathbb N$, as a `tsum`; it converges absolutely (its terms are $O(d\,e^{-\pi\sqrt3 d})$), so `tsum` is its sum. The cube root is the real power $x^{1/3}$ of a nonnegative base.
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), eqs. (5)–(6) pp. 6–7 (PDF 7–8), c_seam p. 10 (PDF 11), eq. (29) p. 29 (PDF 30)

import Mathlib

namespace TerracedZonal.Excess

open Real

/-- Stretching stiffness `c_stretch = 1/4`, eq. (5), p. 6 (PDF 7). -/
noncomputable def cStretch : ℝ := 1 / 4

/-- Nearest-neighbour seam price `c_step = log (1 + e^{-π√3})`, eq. (6), p. 7 (PDF 8). -/
noncomputable def cStep : ℝ := Real.log (1 + Real.exp (-(π * Real.sqrt 3)))

/-- All-pairs seam cost `c_seam = ∑_{d ≥ 1} d · log (1 - (-1)^d e^{-π√3 d})`, p. 10 (PDF 11).
The index is shifted, `d = n + 1` for `n : ℕ`. The series is absolutely summable
(its terms are `O(d e^{-π√3 d})`), so `tsum` is its sum. -/
noncomputable def cSeam : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) *
    Real.log (1 - (-1 : ℝ) ^ (n + 1) * Real.exp (-(π * Real.sqrt 3 * ((n : ℝ) + 1))))

/-- `C₀ = √(2π√3)`, below (29), p. 29 (PDF 30). -/
noncomputable def C0 : ℝ := Real.sqrt (2 * π * Real.sqrt 3)

/-- `B(2/3, 5/6) = Γ(2/3) Γ(5/6) / Γ(3/2)`, below (29), p. 29 (PDF 30). -/
noncomputable def betaB : ℝ := Real.Gamma (2 / 3) * Real.Gamma (5 / 6) / Real.Gamma (3 / 2)

/-- `C(λ) = (3/C₀) (c_stretch λ² C₀⁵ / 384)^{1/3} B(2/3, 5/6)`, eq. (29), p. 29 (PDF 30).
The base of the real power is `≥ 0` for every real `λ`. -/
noncomputable def Cfun (lam : ℝ) : ℝ :=
  (3 / C0) * (cStretch * lam ^ 2 * C0 ^ 5 / 384) ^ (1 / 3 : ℝ) * betaB

/-- `C₁ = ⅓ (1 + 2 c_seam / c_step) C(c_step)`, eq. (29), p. 29 (PDF 30). -/
noncomputable def C1 : ℝ := (1 / 3) * (1 + 2 * cSeam / cStep) * Cfun cStep

end TerracedZonal.Excess


