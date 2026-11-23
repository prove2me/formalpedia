-- Prove2me | Definitions.Def_SPPRevenue_SingleUnit_Supplement_EspProgram
-- name    : SPPRevenue_SingleUnit_Supplement_EspProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:11:44.621414+00:00
-- url     : https://prove2.me/theorems/ba0c1428-2d0b-43be-bad1-26baaae0d4ca
-- title:
--   Lemma 2 and Theorems 5–6, pp. 15, 27–29 — r_n, T_x and the programs (FR-ESP), (FR-ESP-d), (FR-ESP-n), (FR-ESP-n-d)
-- statement:
--   Objects of the eager second-price bounds.
--
--   1. **$r_n$ and the limits.** $r_n(y)=2(1-y/n)^n+y(1-y/n)^{n-1}$ (Lemma 2); the limits of $q_n(y)$ and $r_n(y)$ are $e^{-y}$ and $(2+y)e^{-y}$.
--   2. **$T_x$.** For a tail $s$ and $x\in[0,1]$, $T_x=\inf\{\tau\ge0: s(\tau)\le x\}\in[0,\infty]$, with $T_x=\infty$ when the set is empty.
--   3. **Generic ESP program.** For a pair $(q,r)$, a function $s$ on $[0,\infty)$ is feasible when it is weakly decreasing with values in $[0,1]$, for every $x\in[0,1]$
--   $$\int_{T_x}^\infty\big(2-r(s(\tau))\big)\,d\tau+\int_0^{T_x}\big(x+1-q(s(\tau))\big)\,d\tau\le2,$$
--   and $\int_0^\infty(1-q(s(\tau)))\,d\tau\le1$. The value is the supremum of $\int_0^\infty s$.
--   4. **Generic discretized program.** With $s_i=i/k$: $w_i\ge0$; for every $j\in[k]$,
--   $$\sum_{i=1}^{j}w_i\frac{2-r(s_i)}{s_i}+\sum_{i=j+1}^{k}w_i\frac{s_j+1-q(s_i)}{s_i}\le2;$$
--   and $\sum_i w_i(1-q(s_i))/s_i\le1$. The value is the supremum of $\sum_i w_i$.
--   5. **Instances.** $\mathrm{FR\text{-}ESP}$ and $\mathrm{FR\text{-}ESP\text{-}d}(k)$ take $q(y)=e^{-y}$ and $r(y)=(2+y)e^{-y}$, so that $2-r(y)=2-2e^{-y}-ye^{-y}$ and $1-q=f$ as on p. 27; $\mathrm{FR\text{-}ESP}(n)$ and $\mathrm{FR\text{-}ESP\text{-}d}(n,k)$ take $q=q_n$ and $r=r_n$ (p. 29).
--
--   **Formalization Note** The paper defines $T_x$ with $s^\star$ inside the program; here it is computed from the program's variable $s$, as the proof on pp. 42–43 uses it. The displayed program leaves its tail range implicit. Here $0\le s\le1$ explicitly records the domain of $f$ on p. 27 and the range of the probability tail and grid $s_i$. The n-dependent program uses the same tail range under the substitution on p. 29. The proposed unrestricted counterexample $s>1$ does not respect this domain and is not a refutation of that source reading. The integration domains $\{\tau\ge0:T_x\le\tau\}$ and $\{\tau\ge0:\tau<T_x\}$ differ from the closed intervals only at the point $T_x$.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, pp. 15 (Lemma 2), 27 (Theorem 5, (FR-ESP), (FR-ESP-d)), 28–29 (Theorem 6, (FR-ESP-n), (FR-ESP-n-d)), 42–43 (§8.7)

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Programs

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

/-- `r_n(y) = 2(1 − y/n)^n + y(1 − y/n)^{n−1}` (Lemma 2, p. 15). -/
noncomputable def rn (n : ℕ) (y : ℝ) : ℝ := 2 * (1 - y / n) ^ n + y * (1 - y / n) ^ (n - 1)

/-- The limits `e^{−y}` of `q_n(y)` and `(2 + y) e^{−y}` of `r_n(y)` (Lemma 2, p. 15). -/
noncomputable def qLim (y : ℝ) : ℝ := Real.exp (-y)
noncomputable def rLim (y : ℝ) : ℝ := (2 + y) * Real.exp (-y)

/-- `T_x = inf{τ ≥ 0 : s(τ) ≤ x}` in `[0, ∞]`, equal to `∞` when no such `τ` exists
(Theorems 5–6, pp. 27, 29), computed from the candidate tail `s` of the program. -/
noncomputable def levelTime (s : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨅ τ ∈ {τ : ℝ | 0 ≤ τ ∧ s τ ≤ x}, ENNReal.ofReal τ

/-- Feasibility for the ESP factor-revealing programs, with `q, r` the zero- and
two-events bounds: (FR-ESP) uses `q = e^{−y}`, `r = (2+y)e^{−y}` (p. 27); (FR-ESP-n) uses
`q = q_n`, `r = r_n` (p. 29). The tail `s` is weakly decreasing on `τ ≥ 0` with values in `[0, 1]`;
for every `x ∈ [0, 1]`,
`∫_{T_x}^∞ (2 − r(s(τ))) dτ + ∫_0^{T_x} (x + 1 − q(s(τ))) dτ ≤ 2`; and `∫_0^∞ (1 − q(s(τ))) dτ ≤ 1`. -/
def EspFeasible (q r : ℝ → ℝ) (s : ℝ → ℝ) : Prop :=
  AntitoneOn s (Set.Ici 0) ∧
    (∀ τ, 0 ≤ τ → 0 ≤ s τ ∧ s τ ≤ 1) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      (∫⁻ τ in {τ : ℝ | 0 ≤ τ ∧ levelTime s x ≤ ENNReal.ofReal τ},
          ENNReal.ofReal (2 - r (s τ))) +
        (∫⁻ τ in {τ : ℝ | 0 ≤ τ ∧ ENNReal.ofReal τ < levelTime s x},
          ENNReal.ofReal (x + (1 - q (s τ)))) ≤ 2) ∧
    ∫⁻ τ in Set.Ici 0, ENNReal.ofReal (1 - q (s τ)) ≤ 1

/-- Feasibility for the discretized ESP programs (FR-ESP-d) (p. 27) and (FR-ESP-n-d) (p. 29), with
`s_i = i/k`: `w_i ≥ 0`; for every `j ∈ [k]`,
`Σ_{i=1}^{j} w_i (2 − r(s_i))/s_i + Σ_{i=j+1}^{k} w_i (s_j + 1 − q(s_i))/s_i ≤ 2`; and
`Σ_{i ∈ [k]} w_i (1 − q(s_i))/s_i ≤ 1`. Indices are 0-based. -/
def EspDFeasible (q r : ℝ → ℝ) (k : ℕ) (w : Fin k → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧
    (∀ j : Fin k,
      ∑ i ∈ Finset.univ.filter (fun i => i ≤ j), w i * ((2 - r (gridPt k i)) / gridPt k i) +
        ∑ i ∈ Finset.univ.filter (fun i => j < i),
          w i * ((gridPt k j + (1 - q (gridPt k i))) / gridPt k i) ≤ 2) ∧
    ∑ i, w i * ((1 - q (gridPt k i)) / gridPt k i) ≤ 1

/-- Objective values of (FR-ESP) / (FR-ESP-n), and of their discretizations. -/
def espValues (q r : ℝ → ℝ) : Set ℝ≥0∞ := frObj '' {s | EspFeasible q r s}

def espDValues (q r : ℝ → ℝ) (k : ℕ) : Set ℝ≥0∞ :=
  (fun w : Fin k → ℝ => ENNReal.ofReal (∑ i, w i)) '' {w | EspDFeasible q r k w}

/-- `FR-ESP` and `FR-ESP-d(k)` (Theorem 5, p. 27). -/
noncomputable def frEsp : ℝ≥0∞ := sSup (espValues qLim rLim)
noncomputable def frEspD (k : ℕ) : ℝ≥0∞ := sSup (espDValues qLim rLim k)

/-- `FR-ESP(n)` and `FR-ESP-d(n, k)` (Theorem 6, pp. 28–29). -/
noncomputable def frEspN (n : ℕ) : ℝ≥0∞ := sSup (espValues (qn n) (rn n))
noncomputable def frEspND (n k : ℕ) : ℝ≥0∞ := sSup (espDValues (qn n) (rn n) k)

end SPPRevenue.SingleUnit.Supplement


