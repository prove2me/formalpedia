-- Prove2me | Definitions.Def_LowDimMeanEst_Parameters
-- name    : LowDimMeanEst_Parameters
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:47:57.922337+00:00
-- url     : https://prove2.me/theorems/28fad519-22cc-4f9a-b6be-a8e0bddd02de
-- title:
--   The error terms $\eta$ of Theorem 6, Corollary 7 and Lemma 9, and the parameters $R=25000000\,d\log(1/\delta)/n$, $\tau=\sqrt{nd}$
-- statement:
--   With $L=\log\frac1\delta$ and $LL=\log\log\frac1\delta$, the error terms of the paper are, for a constant $C>0$:
--
--   $$\eta_{\rm main}=C\Big(\sqrt[4]{\tfrac Ln}+\tfrac1{LL}+\tfrac{d^2(\log d+LL)}{L}\Big(1+\sqrt{\tfrac dL}\Big)\Big)\qquad\text{(Theorem 6)},$$
--
--   $$\eta_{\rm cor}=C\Big(\sqrt{\|\mu\|^2+\tfrac dL}+\tfrac1{LL}+\tfrac{d^2(\log d+LL)}{L}\sqrt{1+\tfrac dL}\Big)\qquad\text{(Corollary 7, Theorem 26)},$$
--
--   $$\eta_{\rm fixed}=C\Big(\sqrt{\gamma+\tfrac dL}+\tfrac1{LL}+\tfrac{d^2(\log d+LL)}{L}\sqrt{1+\gamma+\tfrac dL}\Big)\qquad\text{(Lemma 9)}.$$
--
--   The paper writes each as $O(\cdot)$ (and $O_\xi(\cdot)$ in Lemma 9); in the statements of the mission $C$ is existentially quantified before every other parameter (after $\xi$ in Lemma 9). Table 1 sets
--
--   $$R=\frac{25000000\,d\log(1/\delta)}{n},\qquad \tau=\sqrt{nd}.$$
--
--   **Formalization Note** $\log d=0$ at $d=1$, as in the paper; $\sqrt[4]{\cdot}$ is a real power of a nonnegative number.
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Theorem 6, p.13; Corollary 7, p.13; Theorem 26, p.31; Lemma 9, p.16; Table 1, p.24

import Mathlib
import Definitions.Def_LowDimMeanEst_Basic

namespace LowDimMeanEst

/-!
# The error terms η and the parameters of Table 1

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…): η of Theorem 6 (p.13), of Corollary 7 and Theorem 26
(pp.13, 31) and of Lemma 9 (p.16); Table 1 (p.24).

**Formalization Note.**
* Each `η = O(…)` of the paper is `C · (…)` with an explicit constant `C`, existentially quantified
  in the statements before every other parameter (a universal constant), or after `ξ` in Lemma 9
  (`O_ξ`). With `L = log(1/δ)` and `LL = log log(1/δ)`:
  - `etaMain C d n δ = C (⁴√(L/n) + 1/LL + (d²(log d + LL)/L)(1 + √(d/L)))` (Theorem 6);
  - `etaCor C d m₂ δ = C (√(m₂ + d/L) + 1/LL + (d²(log d + LL)/L) √(1 + d/L))`, used with
    `m₂ = ‖µ‖²` (Corollary 7, Theorem 26);
  - `etaFixed C d γ δ = C (√(γ + d/L) + 1/LL + (d²(log d + LL)/L) √(1 + γ + d/L))` (Lemma 9).
* `log d` at `d = 1` is `0`, as in the paper. `⁴√` is `Real.rpow · (1/4)` of a nonnegative number.
* Table 1: `R = 25000000 d log(1/δ)/n`, `τ = √(nd)`.
-/

/-- `η` of Theorem 6 with `O(·)` constant `C`. -/
noncomputable def etaMain (C : ℝ) (d n : ℕ) (δ : ℝ) : ℝ :=
  C * ((logInv δ / n) ^ (1 / 4 : ℝ) + 1 / loglogInv δ +
    ((d : ℝ) ^ 2 * (Real.log d + loglogInv δ) / logInv δ) * (1 + Real.sqrt (d / logInv δ)))

/-- `η` of Corollary 7 and Theorem 26 with `O(·)` constant `C`; `m2` stands for `‖µ‖²`. -/
noncomputable def etaCor (C : ℝ) (d : ℕ) (m2 δ : ℝ) : ℝ :=
  C * (Real.sqrt (m2 + d / logInv δ) + 1 / loglogInv δ +
    ((d : ℝ) ^ 2 * (Real.log d + loglogInv δ) / logInv δ) * Real.sqrt (1 + d / logInv δ))

/-- `η` of Lemma 9 with `O_ξ(·)` constant `C`. -/
noncomputable def etaFixed (C : ℝ) (d : ℕ) (γ δ : ℝ) : ℝ :=
  C * (Real.sqrt (γ + d / logInv δ) + 1 / loglogInv δ +
    ((d : ℝ) ^ 2 * (Real.log d + loglogInv δ) / logInv δ) * Real.sqrt (1 + γ + d / logInv δ))

/-- Table 1: `R = 25000000 d log(1/δ) / n`. -/
noncomputable def paramR (d n : ℕ) (δ : ℝ) : ℝ := 25000000 * d * logInv δ / n

/-- Table 1: `τ = √(nd)`. -/
noncomputable def paramTau (d n : ℕ) : ℝ := Real.sqrt (n * d)

end LowDimMeanEst


