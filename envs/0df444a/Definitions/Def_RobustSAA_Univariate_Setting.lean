-- Prove2me | Definitions.Def_RobustSAA_Univariate_Setting
-- name    : RobustSAA_Univariate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:16:16.527978+00:00
-- url     : https://prove2.me/theorems/2a94f330-4dc2-4b5c-845e-6fea2e0b4a6b
-- title:
--   §1.2, §3.2 (8), (7), Definition 3, §10.7 — order statistics, the KS, Kuiper, CvM, Watson and AD statistics, their regions, the Lévy metric, uniform consistency
-- statement:
--   This definition file fixes the objects of Theorem 5 of Bertsimas, Gupta and Kallus for univariate data.
--
--   **Distributions and data.** Distributions are Borel probability measures $F_0$ on $\mathbb R$, with the topology of weak convergence; the cdf is $F_0(t)=F_0((-\infty,t])$ (§1.2, p. 4). The data $\xi^1,\xi^2,\dots$ are iid from a law $F$, realised on the product space $\mathbb R^{\mathbb N}$ with the product law $F^{\otimes\mathbb N}$; the sample of size $N$ is $(\xi^1,\dots,\xi^N)$. The order statistics $\xi^{(1)}\le\dots\le\xi^{(N)}$ are the sorted sample, and the empirical cdf is $\hat F_N(t)=\#\{i:\xi^i\le t\}/N$.
--
--   **Statistics (8), p. 9.** With $u_i=F_0(\xi^{(i)})$, $i=1,\dots,N$:
--
--   $$
--   \begin{aligned}
--   D_N&=\max_{i}\max\Big\{\tfrac iN-u_i,\;u_i-\tfrac{i-1}N\Big\},\qquad
--   V_N=\max_i\Big(u_i-\tfrac{i-1}N\Big)+\max_i\Big(\tfrac iN-u_i\Big),\\
--   W_N&=\Big(\tfrac1{12N^2}+\tfrac1N\sum_{i=1}^N\Big(\tfrac{2i-1}{2N}-u_i\Big)^2\Big)^{1/2},\qquad
--   U_N=\Big(W_N^2-\Big(\tfrac1N\sum_{i=1}^Nu_i-\tfrac12\Big)^2\Big)^{1/2},\\
--   A_N&=\Big(-1-\sum_{i=1}^N\tfrac{2i-1}{N^2}\big(\log u_i+\log(1-u_{N+1-i})\big)\Big)^{1/2}.
--   \end{aligned}
--   $$
--
--   $A_N$ takes values in $[0,\infty]$ and equals $+\infty$ when some $u_i\in\{0,1\}$. Also $D'_N(F_0)=\max_i|u_i-\tfrac{2i-1}{2N}|$ (§10.7, p. 39).
--
--   **Regions (7), p. 7.** For thresholds $\tau_N$ (playing $Q_{S_N}(\alpha)$), the confidence region of a statistic $S_N$ is $\mathcal F_N=\{F_0: S_N(F_0)\le\tau_N\}$. The threshold condition $Q_{S_N}(\alpha)=O(N^{-1/2})$ is: there is $q$ with $\tau_N\le q/\sqrt N$ for all $N\ge1$.
--
--   **Lévy metric (§10.7, p. 38).** $d_{\text{Lévy}}(G,G')=\inf\{\epsilon>0: G(\xi-\epsilon)-\epsilon\le G'(\xi)\le G(\xi+\epsilon)+\epsilon\ \forall\xi\in\mathbb R\}$.
--
--   **Uniform consistency (Definition 3, p. 13).** For a class of admissible data laws, a family of regions is uniformly consistent if for every admissible $F$, almost surely, every sequence $F_N$ that does not converge weakly to $F$ satisfies $F_N\notin\mathcal F_N$ infinitely often. The class used for Theorem 5 is the continuous (atomless) laws, the standing assumption of §3.2 ("ξ is a univariate continuous random variable").
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Indices are 0-based in Lean: Lean's `i` is the paper's $i+1$, so $i/N$ is written `(i+1)/N`, $(2i-1)/(2N)$ is `(2(i+1)-1)/(2N)`, and $\xi^{(N+1-i)}$ is `Fin.rev i`. The sorted sample is `s ∘ Tuple.sort s`. Maxima over $i$ are `⨆ i : Fin N`, which is $0$ at $N=0$; every statement of the mission about fixed $N$ assumes $N\ge1$. $A_N$ is valued in $[0,\infty]$ with an explicit $+\infty$ branch so that $\log 0=0$ in Lean never makes a distribution look close. The Lévy infimum is over a nonempty set bounded below by $0$ whenever $G,G'$ take values in $[0,1]$.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §1.2 p. 4; (7) p. 7; §3.2 and (8) p. 9; Definition 3 p. 13; §10.7 pp. 38–39 (d_Lévy p. 38, D′_N p. 39)

import Mathlib

namespace RobustSAA.Univariate

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The cdf of a distribution on `ℝ`, `F₀(t) = F₀((−∞, t])` (§1.2, p. 4). -/
noncomputable def cdfOf (F₀ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  ProbabilityTheory.cdf (F₀ : Measure ℝ) t

/-- The law of the iid data sequence `ξ¹, ξ², …` drawn from `F`, on the canonical product space
`ℕ → ℝ` (`ω 0` is the paper's `ξ¹`). -/
noncomputable def dataLaw (F : ProbabilityMeasure ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => (F : Measure ℝ))

/-- The sample `ξ¹, …, ξ^N` of size `N` (0-based indices). -/
def sample (ω : ℕ → ℝ) (N : ℕ) : Fin N → ℝ :=
  fun i => ω i

/-- The sorted sample: `ord s i` is the paper's `ξ^(i+1)`, so `ord s 0 ≤ ⋯ ≤ ord s (N-1)`. -/
noncomputable def ord {N : ℕ} (s : Fin N → ℝ) : Fin N → ℝ :=
  s ∘ ⇑(Tuple.sort s)

/-- `u i = F₀(ξ^(i+1))`, the null cdf at the `(i+1)`-th order statistic. -/
noncomputable def u {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) (i : Fin N) : ℝ :=
  cdfOf F₀ (ord s i)

/-- The empirical cdf `F̂_N(t) = #{i : ξ^i ≤ t} / N`. -/
noncomputable def empCdf {N : ℕ} (s : Fin N → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i => s i ≤ t)).card : ℝ) / N

/-- Kolmogorov–Smirnov statistic (8):
`D_N = max_{i=1..N} max{ i/N − F₀(ξ^(i)), F₀(ξ^(i)) − (i−1)/N }`. -/
noncomputable def ksStat {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) : ℝ :=
  ⨆ i : Fin N, max (((i : ℕ) + 1 : ℝ) / N - u F₀ s i) (u F₀ s i - ((i : ℕ) : ℝ) / N)

/-- Kuiper statistic (8):
`V_N = max_i (F₀(ξ^(i)) − (i−1)/N) + max_i (i/N − F₀(ξ^(i)))`. -/
noncomputable def kuiperStat {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) : ℝ :=
  (⨆ i : Fin N, (u F₀ s i - ((i : ℕ) : ℝ) / N)) + (⨆ i : Fin N, (((i : ℕ) + 1 : ℝ) / N - u F₀ s i))

/-- Cramér–von Mises statistic (8):
`W_N = ( 1/(12N²) + (1/N) Σ_i ((2i−1)/(2N) − F₀(ξ^(i)))² )^{1/2}`. -/
noncomputable def cvmStat {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) : ℝ :=
  Real.sqrt (1 / (12 * (N : ℝ) ^ 2) +
    (1 / (N : ℝ)) * ∑ i : Fin N, ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N) - u F₀ s i) ^ 2)

/-- The centring term `(1/N) Σ_i F₀(ξ^(i)) − 1/2` of the Watson statistic. -/
noncomputable def meanDev {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i : Fin N, u F₀ s i - 1 / 2

/-- Watson statistic (8): `U_N = ( W_N² − ((1/N) Σ_i F₀(ξ^(i)) − 1/2)² )^{1/2}`. -/
noncomputable def watsonStat {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) : ℝ :=
  Real.sqrt (cvmStat F₀ s ^ 2 - meanDev F₀ s ^ 2)

/-- The real expression under the root of the Anderson–Darling statistic (8):
`A_N² = −1 − Σ_i ((2i−1)/N²) (log F₀(ξ^(i)) + log(1 − F₀(ξ^(N+1−i))))`.
Index `Fin.rev i` is the paper's `N + 1 − i`. Meaningful only when every `F₀(ξ^(i)) ∈ (0, 1)`. -/
noncomputable def adSq {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) : ℝ :=
  -1 - ∑ i : Fin N, ((2 * ((i : ℕ) + 1 : ℝ) - 1) / (N : ℝ) ^ 2) *
    (Real.log (u F₀ s i) + Real.log (1 - u F₀ s (Fin.rev i)))

/-- Anderson–Darling statistic (8), valued in `[0, ∞]`: `A_N = (A_N²)^{1/2}` when every
`F₀(ξ^(i))` lies in `(0, 1)`, and `+∞` when some `F₀(ξ^(i))` is `0` or `1` (a logarithm of `0`). -/
noncomputable def adStat {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) : ENNReal :=
  if ∀ i, 0 < u F₀ s i ∧ u F₀ s i < 1 then ENNReal.ofReal (Real.sqrt (adSq F₀ s)) else ⊤

/-- `D′_N(F₀) = max_i |F₀(ξ^(i)) − (2i−1)/(2N)|` (§10.7, p. 39). -/
noncomputable def Dprime {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) : ℝ :=
  ⨆ i : Fin N, |u F₀ s i - (2 * ((i : ℕ) + 1 : ℝ) - 1) / (2 * N)|

/-- Thresholds `Q_{S_N}(α) = O(N^{−1/2})`: some constant `q` with `τ N ≤ q / √N` for all `N ≥ 1`. -/
def ThresholdRate (τ : ℕ → ℝ) : Prop :=
  ∃ q : ℝ, ∀ N : ℕ, 0 < N → τ N ≤ q / Real.sqrt N

/-- Confidence region (7) of the KS test with thresholds `τ`. -/
noncomputable def ksRegion (τ : ℕ → ℝ) (N : ℕ) (s : Fin N → ℝ) : Set (ProbabilityMeasure ℝ) :=
  {F₀ | ksStat F₀ s ≤ τ N}

/-- Confidence region (7) of the Kuiper test with thresholds `τ`. -/
noncomputable def kuiperRegion (τ : ℕ → ℝ) (N : ℕ) (s : Fin N → ℝ) :
    Set (ProbabilityMeasure ℝ) :=
  {F₀ | kuiperStat F₀ s ≤ τ N}

/-- Confidence region (7) of the CvM test with thresholds `τ`. -/
noncomputable def cvmRegion (τ : ℕ → ℝ) (N : ℕ) (s : Fin N → ℝ) : Set (ProbabilityMeasure ℝ) :=
  {F₀ | cvmStat F₀ s ≤ τ N}

/-- Confidence region (7) of the Watson test with thresholds `τ`. -/
noncomputable def watsonRegion (τ : ℕ → ℝ) (N : ℕ) (s : Fin N → ℝ) :
    Set (ProbabilityMeasure ℝ) :=
  {F₀ | watsonStat F₀ s ≤ τ N}

/-- Confidence region (7) of the AD test with thresholds `τ`. -/
noncomputable def adRegion (τ : ℕ → ℝ) (N : ℕ) (s : Fin N → ℝ) : Set (ProbabilityMeasure ℝ) :=
  {F₀ | adStat F₀ s ≤ ENNReal.ofReal (τ N)}

/-- The Lévy metric (§10.7, p. 38):
`d_Lévy(G, G′) = inf{ε > 0 : G(ξ − ε) − ε ≤ G′(ξ) ≤ G(ξ + ε) + ε ∀ ξ ∈ ℝ}`. -/
noncomputable def levyDist (G G' : ℝ → ℝ) : ℝ :=
  sInf {ε : ℝ | 0 < ε ∧ ∀ ξ : ℝ, G (ξ - ε) - ε ≤ G' ξ ∧ G' ξ ≤ G (ξ + ε) + ε}

/-- §3.2, p. 9: the data-generating variable `ξ` is a continuous random variable, i.e. its law
has no atoms. -/
def IsContinuousLaw (F : ProbabilityMeasure ℝ) : Prop :=
  ∀ x : ℝ, (F : Measure ℝ) {x} = 0

/-- Definition 3, p. 13, for the data-generating laws `F` satisfying `Adm F`: almost surely, every
sequence `F_N` that does not converge weakly to `F` lies outside `𝓕_N` infinitely often. -/
def IsUniformlyConsistent (Adm : ProbabilityMeasure ℝ → Prop)
    (region : (N : ℕ) → (Fin N → ℝ) → Set (ProbabilityMeasure ℝ)) : Prop :=
  ∀ F : ProbabilityMeasure ℝ, Adm F →
    ∀ᵐ ω ∂dataLaw F,
      ∀ G : ℕ → ProbabilityMeasure ℝ,
        ¬ Tendsto G atTop (nhds F) →
          ∃ᶠ N in atTop, G N ∉ region N (sample ω N)

end RobustSAA.Univariate


