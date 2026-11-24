-- Prove2me | Definitions.Def_LearnThenTest_Basic
-- name    : LearnThenTest_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T00:07:45.571942+00:00
-- url     : https://prove2.me/theorems/5a15c0db-1080-4815-91d2-be399d42dc35
-- title:
--   Learn then Test: risk-controlling predictions, valid p-values and FWER-controlling algorithms
-- statement:
--   Objects of Sections 1.1, 2 and Appendix B of Angelopoulos, Bates, Candès, Jordan and Lei (2022).
--
--   1. **Risk-controlling prediction (Definition 1).** Let $\Lambda$ be a set of parameters, let $R(\lambda)=R(\mathcal T_\lambda)$ be the risk of the predictor $\mathcal T_\lambda$, and let $\hat\lambda$ be a random element of $\Lambda$ defined on a probability space $(\Omega,\mathcal F,\mathbb P)$. Then $\mathcal T_{\hat\lambda}$ is an $(\alpha,\delta)$-risk-controlling prediction (RCP) if $\mathbb P\big(R(\hat\lambda)\le\alpha\big)\ge1-\delta$.
--   2. **Valid p-value (Section 2.2).** A real statistic $p$ is a valid p-value if $\mathbb P(p\le u)\le u$ for every $u\in[0,1]$, that is, its law stochastically dominates the uniform law on $[0,1]$.
--   3. **FWER-controlling algorithm (Definition 2).** An algorithm $\mathcal A$ maps p-values $(p_1,\dots,p_N)\in[0,1]^N$ to a set of rejected indices $\mathcal A(p_1,\dots,p_N)\subseteq\{1,\dots,N\}$. It is FWER-controlling at level $\delta$ if, for every joint law of $(p_1,\dots,p_N)$ on $[0,1]^N$ (with arbitrary dependence) and every set $J_0$ of true nulls whose p-values are valid, $\mathbb P\big(\mathcal A(p_1,\dots,p_N)\subseteq J_1\big)\ge1-\delta$, where $J_1=\{1,\dots,N\}\setminus J_0$. For a given family of p-values on $\Omega$ and a given $J_0$, the family-wise error rate is $\mathrm{FWER}=\mathbb P\big(\mathcal A(p_1,\dots,p_N)\cap J_0\ne\emptyset\big)$.
--   4. **Bonferroni (Proposition 2).** $\mathcal A^{(\mathrm{Bf})}(p_1,\dots,p_N)=\{j:p_j\le\delta/N\}$, where $N=|\Lambda|$.
--   5. **Fixed sequence testing (Algorithm 1).** Given initializations $\mathcal J\subseteq\{1,\dots,N\}$, for each $j\in\mathcal J$ that is not yet rejected, reject $j,j+1,\dots$ as long as $p\le\delta/|\mathcal J|$, stopping at the first acceptance or at index $N$.
--   6. **Sequential graphical testing (Algorithm 2).** Start from initial levels $\delta_i$ and edge weights $g_{i,j}$. While some unrejected $i$ has $p_i\le\delta_i$, choose such an $i$, reject it, and update $\delta_j\leftarrow\delta_j+\delta_ig_{i,j}$ for unrejected $j$ (else $0$) and $g_{k,j}\leftarrow\dfrac{g_{k,j}+g_{k,i}g_{i,j}}{1-g_{k,i}g_{i,k}}$ for unrejected $k\ne j$ (else $0$). The choice of $i$ is made by an arbitrary choice rule.
--   7. **Hoeffding–Bentkus p-value (Proposition 1, eq. (1)).** With empirical risk $\hat R=\frac1n\sum_{i=1}^nL_i$ and $h_1(a,b)=a\log(a/b)+(1-a)\log\frac{1-a}{1-b}$,
--   $$p^{\mathrm{HB}}=\min\Big(\exp\{-n\,h_1(\hat R\wedge\alpha,\alpha)\},\ e\,\mathbb P\big(\mathrm{Bin}(n,\alpha)\le\lceil n\hat R\rceil\big)\Big).$$
--   8. **CLT p-value (Appendix B).** With the empirical standard deviation $\hat\sigma=\Big(\big((L_1-\hat R)^2+\dots+(L_n-\hat R)^2\big)/(n-1)\Big)^{1/2}$ and $\Phi$ the standard normal distribution function, $p^{\mathrm{CLT}}=1-\Phi\Big(\dfrac{\alpha-\hat R}{\hat\sigma/\sqrt n}\Big)$.
--
--   **Formalization Note** Hypotheses are indexed by $\mathrm{Fin}\,N=\{0,\dots,N-1\}$, and an algorithm is a map $\mathbb R^N\to 2^{\{0,\dots,N-1\}}$; only its values on $[0,1]^N$ matter. Definition 2 quantifies over joint laws $\mu$ of the p-value vector, and it also requires each event $\{j\in\mathcal A(x)\}$ to be Borel measurable so that the probability in Definition 2 is defined. Algorithm 1 visits $\mathcal J$ in increasing order; its output does not depend on the order. Algorithm 2 is run for $N$ passes of its loop. Each pass rejects a new hypothesis, so the loop has stopped by then. Its loop condition ranges over unrejected hypotheses only. A division by $0$ in the weight update returns $0$. The paper prints $\hat\sigma=\big(\sum_i(L_i-\hat R)^2\big)^{1/2}/(n-1)$ while calling it the empirical standard deviation. That printed value is the sample standard deviation divided by $\sqrt{n-1}$, and with it $p^{\mathrm{CLT}}$ is not the CLT p-value (it is badly anti-conservative at finite $n$). The definition uses the empirical standard deviation the text names. A division by $0$ (for $n\le1$) returns $0$.
-- source:
--   Angelopoulos, Bates, Candès, Jordan and Lei, Learn then Test: Calibrating Predictive Algorithms to Achieve Risk Control, arXiv:2110.01052v5 (2022), Section 1.1 (Definition 1), Section 2.2 (valid p-values, Proposition 1, eq. (1)), Section 2.3 (Definition 2, Proposition 2, Algorithms 1 and 2), Appendix B (CLT p-value)

import Mathlib

/-!
Angelopoulos, Bates, Candès, Jordan and Lei, *Learn then Test: Calibrating Predictive Algorithms to
Achieve Risk Control*, arXiv:2110.01052v5 (2022): risk-controlling predictions (Definition 1,
Section 1.1), valid p-values (Section 2.2), the Hoeffding–Bentkus p-value (Proposition 1, eq. (1)),
FWER-controlling algorithms (Definition 2, Section 2.3), the Bonferroni correction
(Proposition 2), fixed sequence testing (Algorithm 1, Section 2.3.1), sequential graphical testing
(Algorithm 2, Section 2.3.2) and the CLT p-value (Appendix B).
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace LearnThenTest

/-- Definition 1 (Section 1.1): for a random parameter `λ̂ : Ω → Λ`, `T_λ̂` is an
`(α, δ)`-risk-controlling prediction if `P(R(T_λ̂) ≤ α) ≥ 1 - δ`; here `R l` is the risk `R(T_l)`. -/
def IsRCP {Ω L : Type*} [MeasurableSpace Ω] (P : Measure Ω) (R : L → ℝ) (α δ : ℝ)
    (lhat : Ω → L) : Prop :=
  ENNReal.ofReal (1 - δ) ≤ P {ω | R (lhat ω) ≤ α}

/-- Section 2.2: a statistic `p` is a valid p-value (its law stochastically dominates the uniform
law on `[0,1]`, Theorem 1) if `P(p ≤ u) ≤ u` for every `u ∈ [0,1]`. -/
def IsValidPValue {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : Ω → ℝ) : Prop :=
  ∀ u ∈ Set.Icc (0 : ℝ) 1, P {ω | p ω ≤ u} ≤ ENNReal.ofReal u

/-- Definition 2 (Section 2.3): an algorithm `A : [0,1]^N → 2^{1,…,N}` (applied to the p-values
`x = (p_1, …, p_N)`, and returning the indices of the rejected hypotheses) is FWER-controlling at
level `δ` if `P(A(p_1, …, p_N) ⊆ J_1) ≥ 1 - δ` for every joint law of the p-values on `[0,1]^N`,
with arbitrary dependence, and every set `J_0` of true nulls whose p-values are valid
(`J_1` is the complement of `J_0`). The event `{j ∈ A(x)}` is required to be measurable so that
the probability is defined. -/
def IsFWERControlling (N : ℕ) (δ : ℝ) (A : (Fin N → ℝ) → Finset (Fin N)) : Prop :=
  (∀ j : Fin N, MeasurableSet {x : Fin N → ℝ | j ∈ A x}) ∧
  ∀ μ : Measure (Fin N → ℝ), IsProbabilityMeasure μ → ∀ J0 : Finset (Fin N),
    (∀ᵐ x ∂μ, ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) →
    (∀ j ∈ J0, IsValidPValue μ (fun x => x j)) →
    ENNReal.ofReal (1 - δ) ≤ μ {x | A x ⊆ J0ᶜ}

/-- Section 2.3: the family-wise error rate of the rejection rule `A` applied to the p-values
`p_1, …, p_N`, when `J_0` is the set of true nulls: `P(A(p_1, …, p_N) ∩ J_0 ≠ ∅)`. -/
def fwer {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (A : (Fin N → ℝ) → Finset (Fin N)) (p : Fin N → Ω → ℝ) (J0 : Finset (Fin N)) : ENNReal :=
  P {ω | ∃ j ∈ A (fun i => p i ω), j ∈ J0}

/-- Proposition 2 (Section 2.3): the Bonferroni correction
`A^(Bf)(p_1, …, p_N) = {j : p_j ≤ δ / |Λ|}`, with `|Λ| = N`. -/
def bonferroni (N : ℕ) (δ : ℝ) (x : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun j => x j ≤ δ / N)

/-- Algorithm 1, lines 5–8 (Section 2.3.1): the indices added by the inner `while` loop started at
`j` with threshold `thr`: all `i ≥ j` such that `p_k ≤ thr` for every `k` with `j ≤ k ≤ i`. The
loop stops at the last index `N`. -/
def fixedSeqChain {N : ℕ} (thr : ℝ) (x : Fin N → ℝ) (j : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => j ≤ i ∧ ∀ k : Fin N, j ≤ k → k ≤ i → x k ≤ thr)

/-- Algorithm 1 (Section 2.3.1), fixed sequence testing with initializations `J`: for each
`j ∈ J` (in increasing order) not already rejected, reject `j, j+1, …` while `p ≤ δ / |J|`. -/
def fixedSeq (N : ℕ) (δ : ℝ) (J : Finset (Fin N)) (x : Fin N → ℝ) : Finset (Fin N) :=
  (J.sort (· ≤ ·)).foldl
    (fun S j => if j ∈ S then S else S ∪ fixedSeqChain (δ / J.card) x j) ∅

/-- Algorithm 2 (Section 2.3.2): the state of sequential graphical testing: the rejected set
`Λ̂`, the current error levels `δ_j` and the current edge weights `g_{k,j}`. -/
structure SGTState (N : ℕ) where
  /-- The indices rejected so far. -/
  rej : Finset (Fin N)
  /-- The current error levels `δ_j`. -/
  lev : Fin N → ℝ
  /-- The current edge weights `g_{k,j}`. -/
  wt : Fin N → Fin N → ℝ

/-- Algorithm 2, lines 5–7: reject `i` and update the levels and the graph:
`δ_j ← δ_j + δ_i g_{i,j}` for unrejected `j` (else `0`), and
`g_{k,j} ← (g_{k,j} + g_{k,i} g_{i,j}) / (1 - g_{k,i} g_{i,k})` for unrejected `k ≠ j` (else `0`). -/
def sgtUpdate {N : ℕ} (s : SGTState N) (i : Fin N) : SGTState N where
  rej := insert i s.rej
  lev := fun j => if j ∉ insert i s.rej then s.lev j + s.lev i * s.wt i j else 0
  wt := fun k j =>
    if k ∉ insert i s.rej ∧ j ∉ insert i s.rej ∧ k ≠ j then
      (s.wt k j + s.wt k i * s.wt i j) / (1 - s.wt k i * s.wt i k)
    else 0

/-- Algorithm 2, line 3: the unrejected hypotheses `i` with `p_i ≤ δ_i`. -/
def sgtEligible {N : ℕ} (x : Fin N → ℝ) (s : SGTState N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i ∉ s.rej ∧ x i ≤ s.lev i)

/-- One pass of the `while` loop of Algorithm 2: if some hypothesis is eligible, reject the one
chosen by the rule `pick` ("choose any `i` such that `p_i ≤ δ_i`") and update; else stop. -/
def sgtStep {N : ℕ} (pick : SGTState N → Finset (Fin N) → Fin N) (x : Fin N → ℝ)
    (s : SGTState N) : SGTState N :=
  if (sgtEligible x s).Nonempty then sgtUpdate s (pick s (sgtEligible x s)) else s

/-- Algorithm 2 (Section 2.3.2), sequential graphical testing with initial error budget `δ0`,
graph `g` and choice rule `pick`, returning `Λ̂`. Each pass rejects a new hypothesis, so the
loop has stopped after `N` passes. -/
def sgt (N : ℕ) (pick : SGTState N → Finset (Fin N) → Fin N) (δ0 : Fin N → ℝ)
    (g : Fin N → Fin N → ℝ) (x : Fin N → ℝ) : Finset (Fin N) :=
  ((sgtStep pick x)^[N] ⟨∅, δ0, g⟩).rej

/-- Section 2.2: the empirical risk `R̂ = (1/n) ∑_{i=1}^n L_i` of the calibration losses. -/
def empRisk {n : ℕ} (l : Fin n → ℝ) : ℝ := (∑ i, l i) / n

/-- Proposition 1: `h_1(a, b) = a log(a/b) + (1 - a) log((1 - a)/(1 - b))` (with `0 log 0 = 0`). -/
def h1 (a b : ℝ) : ℝ := a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))

/-- The distribution function `P(Bin(n, a) ≤ x)` of the binomial law. -/
def binomCdf (n : ℕ) (a x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    if (i : ℝ) ≤ x then (n.choose i : ℝ) * a ^ i * (1 - a) ^ (n - i) else 0

/-- Proposition 1, eq. (1): the Hoeffding–Bentkus p-value
`p^HB = min(exp{-n h_1(R̂ ∧ α, α)}, e P(Bin(n, α) ≤ ⌈n R̂⌉))`. -/
def hbPValue (n : ℕ) (α Rhat : ℝ) : ℝ :=
  min (Real.exp (-((n : ℝ) * h1 (min Rhat α) α)))
    (Real.exp 1 * binomCdf n α (⌈(n : ℝ) * Rhat⌉ : ℝ))

/-- The standard normal distribution function `Φ`. -/
def stdNormalCdf (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- Appendix B: the empirical standard deviation
`σ̂ = (((L_1 - R̂)^2 + … + (L_n - R̂)^2) / (n - 1))^{1/2}`. The printed
`(…)^{1/2} / (n - 1)` is a typo for this: it is not the empirical standard deviation the text
names, but that value divided by `√(n - 1)`. -/
def sigmaHat {n : ℕ} (l : Fin n → ℝ) : ℝ :=
  Real.sqrt ((∑ i, (l i - empRisk l) ^ 2) / ((n : ℝ) - 1))

/-- Proposition B.1 (Appendix B): the CLT p-value `1 - Φ((α - R̂) / (σ̂ / √n))`. -/
def cltPValue {n : ℕ} (α : ℝ) (l : Fin n → ℝ) : ℝ :=
  1 - stdNormalCdf ((α - empRisk l) / (sigmaHat l / Real.sqrt n))

end LearnThenTest


