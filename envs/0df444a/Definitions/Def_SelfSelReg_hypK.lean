-- Prove2me | Definitions.Def_SelfSelReg_hypK
-- name    : SelfSelReg_hypK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:27.979855+00:00
-- url     : https://prove2.me/theorems/b3c9ab28-1245-4a0e-92a6-15fc48102bde
-- title:
--   Hyperparameters 4.1: $K$, $s$, $T$, $\varepsilon_{\mathrm{int}}$, $\Gamma$
-- statement:
--   Given the constants $B\ge1$, $\Delta\in(0,1]$ of Assumption 1.2, the dimension $n$ and the target error $\varepsilon$, the paper fixes
--   $$K=\frac{16(1+B^2)^3}{\Delta^4},\qquad s=\lceil K^4\log n\rceil,\qquad T=2K^2\sqrt s,\qquad \varepsilon_{\mathrm{int}}=\min\{\varepsilon,e^{-K^6s}\},\qquad \Gamma=2K\sqrt{\log(n/\varepsilon_{\mathrm{int}})} .$$
--   $s$ is the tensor order at which the lifted regressors become nearly orthogonal, $T$ the tail threshold of the slices, $\varepsilon_{\mathrm{int}}$ the internal accuracy and $\Gamma$ the refinement threshold. All logarithms are natural.
--
--   **Formalization Note** (9) prints $s:=K^4\log n$, which is not an integer, while $s$ is used as a tensor order, and (182) states $s\le 2K^4\log n$, which presupposes rounding up; $s$ is read as the ceiling.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Hyperparameters 4.1, (8)–(12), p.15 (PDF p.18); (182), p.94 (PDF p.97)

import Mathlib

namespace SelfSelReg

/-- **Hyperparameters 4.1**.

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Hyperparameters 4.1, p.15 (PDF p.18): "K := 16(1 + B²)³/∆⁴ (8),
s := K⁴ log n (9), T := 2K²√s (10), ε_int := min{ε, e^{−K⁶s}} (11), Γ := 2K √(log(n/ε_int)) (12)."

`hypK B ∆ = 16(1 + B²)³/∆⁴`. -/
noncomputable def hypK (B Δ : ℝ) : ℝ := 16 * (1 + B ^ 2) ^ 3 / Δ ^ 4

/-- `s = ⌈K⁴ log n⌉`, the tensor order (9), natural logarithm.

**Formalization Note.** (9) prints `s := K⁴ log n`, which is not an integer, while `s` is used as a
tensor order ("let s ≥ 1 be an integer", Lemmas 5.7, 5.8) and (182), p.94, states
`s ≤ 2K⁴ log n`, which presupposes rounding up. We read `s` as the ceiling. -/
noncomputable def hypS (B Δ : ℝ) (n : ℕ) : ℕ := ⌈hypK B Δ ^ 4 * Real.log n⌉₊

/-- `T = 2K²√s`, the tail threshold (10). -/
noncomputable def hypT (B Δ : ℝ) (n : ℕ) : ℝ := 2 * hypK B Δ ^ 2 * Real.sqrt (hypS B Δ n)

/-- `ε_int = min{ε, e^{−K⁶s}}`, the internal accuracy (11). -/
noncomputable def hypEpsInt (B Δ ε : ℝ) (n : ℕ) : ℝ :=
  min ε (Real.exp (-(hypK B Δ ^ 6 * hypS B Δ n)))

/-- `Γ = 2K√(log(n/ε_int))`, the refinement threshold (12). -/
noncomputable def hypGamma (B Δ ε : ℝ) (n : ℕ) : ℝ :=
  2 * hypK B Δ * Real.sqrt (Real.log (n / hypEpsInt B Δ ε n))

end SelfSelReg


