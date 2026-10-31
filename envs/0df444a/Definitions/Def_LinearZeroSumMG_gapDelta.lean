-- Prove2me | Definitions.Def_LinearZeroSumMG_gapDelta
-- name    : LinearZeroSumMG_gapDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:53:49.124555+00:00
-- url     : https://prove2.me/theorems/d846ceca-155a-4727-ac9b-5c95a8263deb
-- title:
--   The quantities $\delta^k_h$, $\zeta^k_h$, $\overline\gamma^k_h$, $\underline\gamma^k_h$ of Lemma 6
-- statement:
--   Along a data sequence (including episode $k$'s own states and actions), define
--   $$
--   \delta^k_h=\overline V^k_h(x^k_h)-\underline V^k_h(x^k_h),\qquad
--   \zeta^k_h=\big[\mathbb P_h(\overline V^k_{h+1}-\underline V^k_{h+1})\big](x^k_h,a^k_h,b^k_h)-\delta^k_{h+1},
--   $$
--   $$
--   \overline\gamma^k_h=\mathbb E_{(a,b)\sim\sigma^k_h(x^k_h)}\big[\overline Q^k_h(x^k_h,a,b)\big]-\overline Q^k_h(x^k_h,a^k_h,b^k_h),\qquad
--   \underline\gamma^k_h=\mathbb E_{(a,b)\sim\sigma^k_h(x^k_h)}\big[\underline Q^k_h(x^k_h,a,b)\big]-\underline Q^k_h(x^k_h,a^k_h,b^k_h),
--   $$
--   with $\delta^k_{H+1}=0$.
--
--   $\delta^k_h$ is the width of the confidence interval at the visited state; $\zeta,\overline\gamma,\underline\gamma$ are the martingale-difference terms of the recursive decomposition in Lemma 6.
--
--   **Formalization Note** The conditional expectation $\mathbb E[\delta^k_{h+1}\mid x^k_h,a^k_h,b^k_h]$ is written as the kernel integral, the identity the proof uses (p.23). The printed definitions of $\overline\gamma,\underline\gamma$ (p.22) place $a^k_h$, resp. $b^k_h$, inside the expectation over $(a,b)$; the definitions here follow the proof on p.23, which is also what makes $\zeta+\overline\gamma-\underline\gamma$ a martingale difference sequence (§5.5, p.24).
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Lemma 6, p.22; proof, p.23

import Mathlib
import Definitions.Def_LinearZeroSumMG_omni
import Definitions.Def_LinearZeroSumMG_Vval

namespace LinearZeroSumMG

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] {d : ℕ}

/-- **The quantities `δ^k_h`, `ζ^k_h`, `γ̄^k_h`, `γ̲^k_h` of Lemma 6.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Lemma 6, p.22: "Define the random
variables `δ^k_h := V̄^k_h(x^k_h) − V̲^k_h(x^k_h)`, `ζ^k_h := 𝔼[δ^k_{h+1} | x^k_h, a^k_h, b^k_h] − δ^k_{h+1}`,
`γ̄^k_h := 𝔼_{(a,b)∼σ^k_h(x^k_h)}[Q̄^k_h(x^k_h, a^k_h, b)] − Q̄^k_h(x^k_h, a^k_h, b^k_h)`,
`γ̲^k_h := 𝔼_{(a,b)∼σ^k_h(x^k_h)}[Q̲^k_h(x^k_h, a, b^k_h)] − Q̲^k_h(x^k_h, a^k_h, b^k_h)`."

Along the data `xs`, `as`, `bs` (episode `k`'s own states and actions included):
- `gapDelta … k h = δ^k_h = V̄^k_h(x^k_h) − V̲^k_h(x^k_h)` (so `δ^k_{H+1} = 0`);
- `gapZeta … k h = ζ^k_h = (ℙ_h(V̄^k_{h+1} − V̲^k_{h+1}))(x^k_h, a^k_h, b^k_h) − δ^k_{h+1}`;
- `gapGammaUp … k h = γ̄^k_h = 𝔼_{(a,b)∼σ^k_h(x^k_h)}[Q̄^k_h(x^k_h, a, b)] − Q̄^k_h(x^k_h, a^k_h, b^k_h)`;
- `gapGammaLo … k h = γ̲^k_h = 𝔼_{(a,b)∼σ^k_h(x^k_h)}[Q̲^k_h(x^k_h, a, b)] − Q̲^k_h(x^k_h, a^k_h, b^k_h)`.

**Formalization Note**
- `ζ`: the conditional expectation `𝔼[δ^k_{h+1} | x^k_h, a^k_h, b^k_h]` is the kernel integral
  `ℙ_h(V̄^k_{h+1} − V̲^k_{h+1})(x^k_h, a^k_h, b^k_h)`, the identity used in the proof on p.23 (a version of a
  conditional expectation chosen per sample point would make the pathwise statement meaningless).
- `γ̄`, `γ̲`: the printed definitions put `a^k_h` (resp. `b^k_h`) inside the expectation over
  `(a, b) ∼ σ^k_h(x^k_h)`. The proof on p.23 uses `𝔼_{(a,b)∼σ}[Q̄^k_h(x^k_h, a, b)]` and
  `𝔼_{(a,b)∼σ}[Q̲^k_h(x^k_h, a, b)]` (the decomposition of `δ^k_h` there), and §5.5 (p.24) needs
  `ζ + γ̄ − γ̲` to be a martingale difference sequence, which fails for the printed versions when `σ`
  is correlated. These definitions follow the proof. -/
noncomputable def gapDelta (G : MarkovGame S A) (P : OmniParams S A d) (xs : ℕ → ℕ → S)
    (as bs : ℕ → ℕ → A) (k h : ℕ) : ℝ :=
  VUp G P xs as bs k h (xs k h) - VLo G P xs as bs k h (xs k h)

/-- `ζ^k_h = (ℙ_h(V̄^k_{h+1} − V̲^k_{h+1}))(x^k_h, a^k_h, b^k_h) − δ^k_{h+1}` (Lemma 6, p.22). -/
noncomputable def gapZeta (G : MarkovGame S A) (P : OmniParams S A d) (xs : ℕ → ℕ → S)
    (as bs : ℕ → ℕ → A) (k h : ℕ) : ℝ :=
  transOp G h (fun y => VUp G P xs as bs k (h + 1) y - VLo G P xs as bs k (h + 1) y)
      (xs k h) (as k h) (bs k h) - gapDelta G P xs as bs k (h + 1)

/-- `γ̄^k_h = 𝔼_{(a,b)∼σ^k_h(x^k_h)}[Q̄^k_h(x^k_h, a, b)] − Q̄^k_h(x^k_h, a^k_h, b^k_h)` (Lemma 6, p.22, as used
on p.23). -/
noncomputable def gapGammaUp (G : MarkovGame S A) (P : OmniParams S A d) (xs : ℕ → ℕ → S)
    (as bs : ℕ → ℕ → A) (k h : ℕ) : ℝ :=
  (∑ ab : A × A, (omni G P xs as bs k h).sigma (xs k h) ab *
      (omni G P xs as bs k h).QUp (xs k h) ab.1 ab.2) -
    (omni G P xs as bs k h).QUp (xs k h) (as k h) (bs k h)

/-- `γ̲^k_h = 𝔼_{(a,b)∼σ^k_h(x^k_h)}[Q̲^k_h(x^k_h, a, b)] − Q̲^k_h(x^k_h, a^k_h, b^k_h)` (Lemma 6, p.22, as used
on p.23). -/
noncomputable def gapGammaLo (G : MarkovGame S A) (P : OmniParams S A d) (xs : ℕ → ℕ → S)
    (as bs : ℕ → ℕ → A) (k h : ℕ) : ℝ :=
  (∑ ab : A × A, (omni G P xs as bs k h).sigma (xs k h) ab *
      (omni G P xs as bs k h).QLo (xs k h) ab.1 ab.2) -
    (omni G P xs as bs k h).QLo (xs k h) (as k h) (bs k h)

end LinearZeroSumMG


