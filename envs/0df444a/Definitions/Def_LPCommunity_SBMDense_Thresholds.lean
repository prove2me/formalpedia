-- Prove2me | Definitions.Def_LPCommunity_SBMDense_Thresholds
-- name    : LPCommunity_SBMDense_Thresholds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T12:37:18.643363+00:00
-- url     : https://prove2.me/theorems/b5658604-33d6-43b9-9ec8-beb6ece2c346
-- title:
--   Theorem 7, pp. 15–16, and Proposition 14, p. 29 — the threshold conditions (22)–(25) and Shimizu's constant $\mu(\omega,\alpha)$
-- statement:
--   Let $\alpha,\beta>0$ and $\omega\in[0,1)$, and write $\lceil x\rceil$ for the least integer $\ge x$. The four non-recovery conditions of Theorem 7 are:
--
--   1. **(22)** $\omega=0$ and $\displaystyle\beta>\max\Big\{\frac{3-\alpha-\sqrt{(3-\alpha)^2-4\alpha}}{2},\ 2\alpha-1\Big\}$;
--   2. **(23)** $\omega\in(0,1)$ with $\frac1{1-\omega}\notin\mathbb N$ and $\displaystyle\beta>\frac{1}{2\lceil\frac1{1-\omega}\rceil-1}\cdot\alpha$;
--   3. **(24)** $\omega=\frac12$ and $\displaystyle\beta>\max\Big\{\frac{1-2e^{-\alpha^2}}{2-e^{-\alpha^2}},\ \frac{1}{3+2e^{-\alpha^2}}\Big\}\cdot\alpha$;
--   4. **(25)** $\omega\in(0,1)$ with $\frac1{1-\omega}\in\mathbb N\setminus\{2\}$ and $\displaystyle\beta>\frac{1}{2\cdot\frac1{1-\omega}-1+2\exp\big(-\alpha^{\frac1{1-\omega}}\big)}\cdot\alpha$.
--
--   For $\omega\in(0,1)$ and $\alpha>0$, Shimizu's constant (Proposition 14) is
--
--   $$
--   \mu(\omega,\alpha)=\Big\lceil\frac1{1-\omega}\Big\rceil+\mathbf 1\Big\{\frac1{1-\omega}\in\mathbb N\Big\}\exp\big(-\alpha^{\frac1{1-\omega}}\big),
--   $$
--
--   the limiting average distance of $\mathcal G_{n,\alpha n^{-\omega}}$.
--
--   **Formalization Note** Each condition carries its own clause on $\omega$, exactly as printed; "$\frac1{1-\omega}\in\mathbb N$" is "there is a natural number $k$ with $\frac1{1-\omega}=k$". The ceiling is `Nat.ceil`, which agrees with the integer ceiling since $\frac1{1-\omega}>0$. The powers $\alpha^{1/(1-\omega)}$ are real powers; $\alpha^2$ is the ordinary square. In (25), $2\cdot\frac1{1-\omega}$ is kept as the real expression printed.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, pp. 15–16, Theorem 7, (22)–(25); p. 29, Proposition 14 (µ)

import Mathlib

namespace LPCommunity.SBMDense

open scoped Classical

/-- Condition 1 of Theorem 7, (22): `ω = 0` and
`β > max{(3 − α − √((3 − α)² − 4α))/2, 2α − 1}`. -/
def Cond22 (α β ω : ℝ) : Prop :=
  ω = 0 ∧ β > max ((3 - α - Real.sqrt ((3 - α) ^ 2 - 4 * α)) / 2) (2 * α - 1)

/-- Condition 2 of Theorem 7, (23): `ω ∈ (0, 1)`, `1/(1−ω) ∉ ℕ`, and
`β > α / (2⌈1/(1−ω)⌉ − 1)`. -/
def Cond23 (α β ω : ℝ) : Prop :=
  0 < ω ∧ ω < 1 ∧ (¬ ∃ k : ℕ, 1 / (1 - ω) = k) ∧
    β > 1 / (2 * (⌈1 / (1 - ω)⌉₊ : ℝ) - 1) * α

/-- Condition 3 of Theorem 7, (24): `ω = 1/2` and
`β > max{(1 − 2e^{−α²})/(2 − e^{−α²}), 1/(3 + 2e^{−α²})} · α`. -/
def Cond24 (α β ω : ℝ) : Prop :=
  ω = 1 / 2 ∧
    β > max ((1 - 2 * Real.exp (-(α ^ 2))) / (2 - Real.exp (-(α ^ 2))))
          (1 / (3 + 2 * Real.exp (-(α ^ 2)))) * α

/-- Condition 4 of Theorem 7, (25): `ω ∈ (0, 1)`, `1/(1−ω) ∈ ℕ ∖ {2}`, and
`β > α / (2 · 1/(1−ω) − 1 + 2 exp(−α^{1/(1−ω)}))`. -/
def Cond25 (α β ω : ℝ) : Prop :=
  0 < ω ∧ ω < 1 ∧ (∃ k : ℕ, k ≠ 2 ∧ 1 / (1 - ω) = k) ∧
    β > 1 / (2 * (1 / (1 - ω)) - 1 + 2 * Real.exp (-(α ^ (1 / (1 - ω))))) * α

/-- Shimizu's limit of the average distance in `G_{n,p}`, `p = α n^{-ω}` (Proposition 14):
`µ(ω, α) = ⌈1/(1−ω)⌉ + 1{1/(1−ω) ∈ ℕ} exp(−α^{1/(1−ω)})`. -/
noncomputable def mu (ω α : ℝ) : ℝ :=
  (⌈1 / (1 - ω)⌉₊ : ℝ) +
    (if ∃ k : ℕ, 1 / (1 - ω) = k then Real.exp (-(α ^ (1 / (1 - ω)))) else 0)

end LPCommunity.SBMDense


