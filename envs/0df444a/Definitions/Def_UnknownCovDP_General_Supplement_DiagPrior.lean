-- Prove2me | Definitions.Def_UnknownCovDP_General_Supplement_DiagPrior
-- name    : UnknownCovDP_General_Supplement_DiagPrior
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:45:52.086183+00:00
-- url     : https://prove2.me/theorems/7c336eb5-8399-4bd3-adf3-758a27c93e18
-- title:
--   Definitions 3.1, 3.3 and eq. (9) — the prior $\mathcal P_{\mathrm{diag}}(d)$ and $(k,\ell)$-selection mechanisms
-- statement:
--   Fix a dimension $d$ and a sample size $n$. This module sets up the diagonal-covariance experiment of §3.
--
--   1. **The law $\mathrm{inv}\chi^2(1,1)$** (Definition 3.1 with $\nu=\tau=1$). A random variable $\sigma^2$ has this law when $1/\sigma^2\sim\chi^2_1$; equivalently $\sigma^2=1/g^2$ with $g\sim N(0,1)$. Its density on $x>0$ is proportional to $e^{-1/(2x)}x^{-3/2}$.
--   2. **The prior $\mathcal P_{\mathrm{diag}}(d)$** (eq. (9)). The mean and the covariance are independent, with
--   $$\mu\sim N(0,d^2 I_d),\qquad \Sigma=\mathrm{Diag}(\sigma_1^2,\dots,\sigma_d^2),\quad (\sigma_i^2)_{i\in[d]}\sim \mathrm{inv}\chi^2(1,1)^{\otimes d}.$$
--   3. **The $k$ largest variances.** Let $\pi$ be the permutation with $\sigma^2_{\pi(1)}\ge\dots\ge\sigma^2_{\pi(d)}$, and write $T_k(\Sigma)=\{\pi(1),\dots,\pi(k)\}$.
--   4. **Selection mechanisms** (Definition 3.3). A randomized algorithm $\mathcal M$ maps a dataset $X$ of $n$ points of $\mathbb R^d$ to $s=\mathcal M(X)\in\{0,1\}^d$. It is a **$(k,\ell)$-selection mechanism for $\mathcal P_{\mathrm{diag}}$ with sample complexity $n$** if
--      - (Boundedness) $\sum_{j=1}^d s_j\le \ell$ for every output, and
--      - (Accuracy) with $\Sigma$ drawn from the covariance marginal of $\mathcal P_{\mathrm{diag}}$, centered data $X\sim N(0,\Sigma)^{\otimes n}$ and the coins of $\mathcal M$,
--   $$\Pr\Bigl[\sum_{j=1}^k s_{\pi(j)}\ge \tfrac k4\Bigr]\ge\tfrac13 .$$
--
--   These objects are used by Theorems 3.2 and 3.4. The mean-estimation experiment and the Bayes risk $\mathfrak R_{\varepsilon,\delta}(\mathcal P,n)$ come from the mission's published model and apply to $\mathcal P_{\mathrm{diag}}$ unchanged.
--
--   **Formalization Note** $\mathrm{inv}\chi^2(1,1)$ is the pushforward of $N(0,1)$ under $g\mapsto 1/g^2$; at the null point $g=0$ Lean returns $0$. The defining maps are proved measurable, so the laws are probability measures. An output $s$ is a function $\mathrm{Fin}\,d\to\mathrm{Bool}$. Ties among the variances have probability zero; $T_k$ breaks them by index (the smaller index first), and when $k\ge d$ every index is in $T_k$. Boundedness is stated as: for every dataset, the output law gives probability $0$ to $\{s:\sum_j s_j>\ell\}$.
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Definition 3.1 and eq. (9), printed p. 16 (PDF p. 17); Definition 3.3, printed p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_UnknownCovDP_General_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General.Supplement

/-!
# The diagonal inverse-χ² prior `P_diag` and `(k, ℓ)`-selection mechanisms

Gaucher, Linder, Smith, Ullman, Zakynthinou, *Dimension-Free Private Mean Estimation is Impossible
Without the Covariance*, STOC 2027 submission #573 (October 2026), Definition 3.1 and eq. (9)
(printed p. 16, PDF p. 17), Definition 3.3 (printed p. 17, PDF p. 18).

**Formalization Note.**
* Only `invχ²(1, 1)` is used. By Definition 3.1, `σ² ∼ invχ²(1, 1)` iff `1/σ² ∼ χ²₁`, i.e. `σ²` has
  the law of `1/g²` with `g ∼ N(0, 1)`. It is realized as that pushforward; at `g = 0` (a null event)
  Lean's `(0 ^ 2)⁻¹ = 0`. The defining maps are proved measurable, so no law is the junk zero
  measure.
* `P_diag(d)` is a measure on `Vec d × Mat d` (the base mission's types), so the base
  `experimentProb` and `bayesRisk` apply to it unchanged.
* A selection mechanism outputs `s ∈ {0,1}^d`, encoded as `Fin d → Bool` (finite, discrete σ-algebra).
* "The `k` indices with the largest variances" (`π(1), …, π(k)` with `σ²_{π(1)} ≥ … ≥ σ²_{π(d)}`) is
  encoded by `topK`: index `i` is selected iff fewer than `k` indices precede it in the strict order
  "larger variance, ties broken by smaller index". Ties have probability zero under `P_diag`. If
  `k ≥ d`, every index is selected.
-/

/-- The law `invχ²(1, 1)` of Definition 3.1 (`ν = τ = 1`): the law of `1/g²` with `g ∼ N(0,1)`,
equivalently `1/σ² ∼ χ²₁`; density `∝ exp(−1/(2x)) x^{−3/2}` on `x > 0`. -/
noncomputable def invChiSq11 : Measure ℝ :=
  (gaussianReal 0 1).map fun g : ℝ => (g ^ 2)⁻¹

lemma measurable_invSq : Measurable fun g : ℝ => (g ^ 2)⁻¹ :=
  (measurable_id.pow_const 2).inv

instance invChiSq11_prob : IsProbabilityMeasure invChiSq11 :=
  Measure.isProbabilityMeasure_map measurable_invSq.aemeasurable

/-- `σ ↦ Diag(σ₁, …, σ_d)` is measurable. -/
lemma measurable_diagonal (d : ℕ) :
    Measurable (fun σ : Fin d → ℝ => (Matrix.diagonal σ : Mat d)) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  by_cases h : i = j
  · subst h
    simp only [Matrix.diagonal_apply_eq]
    exact measurable_pi_apply i
  · simp only [Matrix.diagonal_apply_ne _ h]
    exact measurable_const

/-- The `Σ`-marginal of `P_diag(d)` (eq. (9)): `Σ = Diag(σ₁², …, σ_d²)` with `σᵢ²` i.i.d.
`invχ²(1, 1)`. -/
noncomputable def diagCovPrior (d : ℕ) : Measure (Mat d) :=
  (Measure.pi fun _ : Fin d => invChiSq11).map fun σ => (Matrix.diagonal σ : Mat d)

instance diagCovPrior_prob (d : ℕ) : IsProbabilityMeasure (diagCovPrior d) :=
  Measure.isProbabilityMeasure_map (measurable_diagonal d).aemeasurable

/-- The prior `P_diag(d)` of eq. (9): `μ ∼ N(0, d² I_d)` and, independently,
`Σ = Diag(σ₁², …, σ_d²)` with `σᵢ²` i.i.d. `invχ²(1, 1)`. -/
noncomputable def Pdiag (d : ℕ) : Measure (Vec d × Mat d) :=
  (multivariateGaussian (0 : Vec d) (((d : ℝ) ^ 2) • (1 : Mat d))).prod (diagCovPrior d)

/-- The indices of the `k` largest diagonal entries of `S` (Definition 3.3, `{π(1), …, π(k)}`):
`i` is selected iff fewer than `k` indices `j` have `S j j > S i i`, or `S j j = S i i` and `j < i`.
-/
noncomputable def topK {d : ℕ} (k : ℕ) (S : Mat d) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter fun i =>
    (Finset.univ.filter fun j => S i i < S j j ∨ (S j j = S i i ∧ j < i)).card < k

/-- The number of selected indices of `s ∈ {0,1}^d` among the indices in `J`, as a natural number. -/
def countSel {d : ℕ} (J : Finset (Fin d)) (s : Fin d → Bool) : ℕ :=
  (J.filter fun j => s j = true).card

/-- A selection mechanism with sample complexity `n`: a randomized map (Markov kernel, its coins
being the kernel's randomness) from `n`-point datasets in `ℝ^d` to `s ∈ {0,1}^d`. -/
abbrev SelMech (d n : ℕ) := Kernel (Fin n → Vec d) (Fin d → Bool)

/-- `Pr_{Σ ∼ P_diag, X ∼ N(0,Σ)^{⊗n}, coins of M}[Σ_{j ≤ k} s_{π(j)} ≥ k/4]` (Definition 3.3,
Accuracy): the data are centered, the inequality is between real numbers. -/
noncomputable def selAccuracy {d n : ℕ} (k : ℕ) (M : SelMech d n) : ℝ≥0∞ :=
  ∫⁻ S, ∫⁻ X, M X {s | (k : ℝ) / 4 ≤ (countSel (topK k S) s : ℝ)} ∂(dataLaw n (0 : Vec d) S)
    ∂(diagCovPrior d)

/-- Definition 3.3: `M` is a `(k, ℓ)`-selection mechanism for `P_diag` with sample complexity `n`:
1. Boundedness: `Σ_j s_j ≤ ℓ` for every output, i.e. for every dataset the output law puts no mass on
   `{s | ℓ < Σ_j s_j}`;
2. Accuracy: `Pr[Σ_{j=1}^k s_{π(j)} ≥ k/4] ≥ 1/3`. -/
def IsSelectionMechanism {d n : ℕ} (k ℓ : ℕ) (M : SelMech d n) : Prop :=
  (∀ X, M X {s | ℓ < countSel Finset.univ s} = 0) ∧ 1 / 3 ≤ selAccuracy k M

end UnknownCovDP.General.Supplement


