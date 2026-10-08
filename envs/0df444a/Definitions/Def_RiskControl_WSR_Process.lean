-- Prove2me | Definitions.Def_RiskControl_WSR_Process
-- name    : RiskControl_WSR_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:35:13.663842+00:00
-- url     : https://prove2.me/theorems/00392000-4a92-44e4-8ef3-34f96f887f51
-- title:
--   Proposition 5, p. 7 — the WSR quantities μ̂ᵢ, σ̂²ᵢ, νᵢ, the capital process 𝒦ᵢ(R), the bound R̂⁺_WSR, and the loss filtration
-- statement:
--   These are the objects of Proposition 5 (the Waudby-Smith–Ramdas bound) of Bates, Angelopoulos, Lei, Malik and Jordan, for one fixed value of the parameter $\lambda$, which is dropped from the notation.
--
--   Let $n$ be the calibration sample size, $\delta$ the confidence level, and let $L_1, \dots, L_n$ be the losses $L_j = L(Y_j, \mathcal T_\lambda(X_j))$ of the calibration points, collected in a sample $\omega = (L_1, \dots, L_n) \in \mathbb R^n$. Indices are 1-based as in the paper.
--
--   1. **Running mean and variance.** For $i \ge 0$,
--   $$\hat\mu_i = \frac{1/2 + \sum_{j=1}^{i} L_j}{1+i}, \qquad \hat\sigma^2_i = \frac{1/4 + \sum_{j=1}^{i} (L_j - \hat\mu_j)^2}{1+i}.$$
--   In particular $\hat\sigma^2_0 = 1/4$.
--   2. **Betting fractions.** For $i \ge 1$,
--   $$\nu_i = \min\left\{1, \sqrt{\frac{2\log(1/\delta)}{n\,\hat\sigma^2_{i-1}}}\right\}.$$
--   3. **Capital process.** For $R \in \mathbb R$ and $i \ge 0$,
--   $$\mathcal K_i(R) = \prod_{j=1}^{i} \bigl\{1 - \nu_j (L_j - R)\bigr\}, \qquad \mathcal K_0(R) = 1.$$
--   4. **Upper confidence bound.**
--   $$\widehat R^+_{\mathrm{WSR}} = \inf\Bigl\{R \ge 0 : \max_{i=1,\dots,n} \mathcal K_i(R) > \frac1\delta\Bigr\},$$
--   an infimum in the extended reals, so that it equals $+\infty$ when no $R \ge 0$ qualifies.
--   5. **Filtration.** $\mathcal F_i = \sigma(L_1, \dots, L_i)$ on the sample space $\mathbb R^n$ with its product $\sigma$-field, with $\mathcal F_0$ trivial and $\mathcal F_i = \mathcal F_n$ for $i \ge n$.
--
--   These quantities are the hedged-capital construction the paper borrows from Waudby-Smith and Ramdas: $\nu_i$ depends only on $L_1, \dots, L_{i-1}$, and $\widehat R^+_{\mathrm{WSR}}$ is the smallest candidate mean at which a gambler betting against it would have multiplied their capital by more than $1/\delta$.
--
--   **Formalization Note** The sample is a function $\omega : \{0,\dots,n-1\} \to \mathbb R$ and $L_j = \omega(j-1)$ for $1 \le j \le n$; $L_j$ is set to $0$ outside $\{1, \dots, n\}$, which only matters through $\mathcal F_0$ being trivial. In $\nu_i$ the index $i-1$ is natural-number subtraction, used only for $i \ge 1$, where it is the page's $i-1$. The value $\hat\sigma^2_0 = 1/4$ is the page's formula with the empty sum; $\hat\sigma^2_i \ge 1/(4(1+i)) > 0$, so $\nu_i$ never divides by zero for $n \ge 1$. "$\max_{i=1,\dots,n} \mathcal K_i > 1/\delta$" is written as "there is $i \in \{1,\dots,n\}$ with $\mathcal K_i > 1/\delta$", the same condition when $n \ge 1$. The infimum is an `EReal` infimum of the image of a real set, never a real `sInf` (which would be $0$ on the empty set). The filtration is Mathlib's natural filtration of the process $i \mapsto L_i$; the file also contains the routine lemma that each $L_j$ is a measurable function of the sample, which that construction needs.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proposition 5, p. 7; filtration from the Proof of Proposition 5, p. 26

import Mathlib

open MeasureTheory

namespace RiskControl.WSR

/-- The `j`-th loss `L_j(λ)` of the calibration sample, 1-based as on the page
(Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proposition 5, p. 7). The sample
of the `n` loss values at the fixed `λ` is `ω : Fin n → ℝ`, and `obs ω j = ω (j - 1)` for
`1 ≤ j ≤ n`. Outside `{1, …, n}` (in particular at `j = 0`) it is `0`; this value is never used
by the quantities below except through the trivial σ-field `ℱ₀` of `filt`. -/
noncomputable def obs {n : ℕ} (ω : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ n then ω ⟨j - 1, by omega⟩ else 0

/-- The running mean `μ̂_i(λ) = (1/2 + ∑_{j=1}^i L_j(λ)) / (1 + i)` (arXiv:2101.02703v3,
Proposition 5, p. 7). -/
noncomputable def muHat {n : ℕ} (ω : Fin n → ℝ) (i : ℕ) : ℝ :=
  (1 / 2 + ∑ j ∈ Finset.Icc 1 i, obs ω j) / (1 + (i : ℝ))

/-- The running variance `σ̂²_i(λ) = (1/4 + ∑_{j=1}^i (L_j(λ) − μ̂_j(λ))²) / (1 + i)`
(arXiv:2101.02703v3, Proposition 5, p. 7). At `i = 0` the sum is empty and `σ̂²_0 = 1/4`, the
page's formula with the empty sum; this is the value `ν₁` uses. It is always positive
(at least `1 / (4 (1 + i))`). -/
noncomputable def sigmaSqHat {n : ℕ} (ω : Fin n → ℝ) (i : ℕ) : ℝ :=
  (1 / 4 + ∑ j ∈ Finset.Icc 1 i, (obs ω j - muHat ω j) ^ 2) / (1 + (i : ℝ))

/-- The betting fraction `ν_i(λ) = min{1, √(2 log(1/δ) / (n σ̂²_{i−1}(λ)))}`
(arXiv:2101.02703v3, Proposition 5, p. 7), for the sample size `n` and the level `δ`. It is used
only for `i ≥ 1` (in `K`), where the natural-number subtraction `i - 1` is the page's `i − 1`. -/
noncomputable def nu (n : ℕ) (δ : ℝ) (ω : Fin n → ℝ) (i : ℕ) : ℝ :=
  min 1 (Real.sqrt (2 * Real.log (1 / δ) / ((n : ℝ) * sigmaSqHat ω (i - 1))))

/-- The capital process `𝒦_i(R; λ) = ∏_{j=1}^i {1 − ν_j(λ)(L_j(λ) − R)}` (arXiv:2101.02703v3,
Proposition 5, p. 7). The empty product gives `𝒦_0(R; λ) = 1`. -/
noncomputable def K (n : ℕ) (δ : ℝ) (ω : Fin n → ℝ) (i : ℕ) (R : ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 i, (1 - nu n δ ω j * (obs ω j - R))

/-- The Waudby-Smith–Ramdas upper confidence bound
`R̂⁺_WSR(λ) = inf {R ≥ 0 : max_{i=1,…,n} 𝒦_i(R; λ) > 1/δ}` (arXiv:2101.02703v3,
Proposition 5, p. 7). The condition `max_{i=1,…,n} 𝒦_i > 1/δ` is written as
`∃ i ∈ {1, …, n}, 𝒦_i > 1/δ` (the same for `n ≥ 1`). The infimum is taken in `EReal`, so an
empty defining set gives `R̂⁺_WSR = +∞` (`sInf ∅ = ⊤`), never the junk value `0` of a real
`sInf`. -/
noncomputable def wsrUCB (n : ℕ) (δ : ℝ) (ω : Fin n → ℝ) : EReal :=
  sInf ((fun R : ℝ => (R : EReal)) ''
    {R : ℝ | 0 ≤ R ∧ ∃ i ∈ Finset.Icc 1 n, 1 / δ < K n δ ω i R})

/-- Each loss `ω ↦ L_j(λ)` is a measurable (hence strongly measurable) function of the sample. -/
theorem stronglyMeasurable_obs (n j : ℕ) :
    StronglyMeasurable (fun ω : Fin n → ℝ => obs ω j) := by
  unfold obs
  split_ifs with h
  · exact (measurable_pi_apply _).stronglyMeasurable
  · exact stronglyMeasurable_const

/-- The natural filtration of the losses: `ℱ_i = σ(L_1(λ), …, L_i(λ))` for `i ≤ n`, with `ℱ_0`
the trivial σ-field (because `obs ω 0 = 0`) and `ℱ_i = ℱ_n` for `i ≥ n` (arXiv:2101.02703v3,
Proof of Proposition 5, p. 26), on the sample space `Fin n → ℝ` with its product σ-field. -/
noncomputable def filt (n : ℕ) : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (Fin n → ℝ)) :=
  Filtration.natural (fun i (ω : Fin n → ℝ) => obs ω i) (fun i => stronglyMeasurable_obs n i)

end RiskControl.WSR


