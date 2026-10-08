-- Prove2me | Definitions.Def_KleywegtSAA_ExpRate_Setting
-- name    : KleywegtSAA_ExpRate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:08.837089+00:00
-- url     : https://prove2.me/theorems/e9a99755-8b09-4780-9a51-4fe4f8cd8888
-- title:
--   §1–§2.2, pp. 1–4 — the finite stochastic program (1.1), its SAA (2.1), ε-optimal sets, δ_N (2.2), α(ε) (2.3), Assumption A and the rate function I
-- statement:
--   Let $\mathcal S$ be a nonempty finite set, $G : \mathcal S \times \mathcal W \to \mathbb R$, and let $W^1, W^2, \dots$ be random elements of $\mathcal W$ on a probability space $(\Omega, P)$; $W$ denotes a random element with the common law of the sample.
--
--   1. The **true objective** of (1.1) is $g(x) = \mathbb E\, G(x, W)$, and the **sample average function** of §2 is
--   $$\hat g_N(x) = \frac1N \sum_{n=1}^N G(x, W^n),$$
--   evaluated along a realization $\omega$.
--   2. For a function $f$ on $\mathcal S$, $\min_{\mathcal S} f$ is its minimum over the finite set; $v^* = \min_{\mathcal S} g$ and $\hat v_N = \min_{\mathcal S} \hat g_N$.
--   3. For $\varepsilon \ge 0$ the set of **$\varepsilon$-optimal solutions** of $f$ is $\{x \in \mathcal S : f(x) \le \min_{\mathcal S} f + \varepsilon\}$. With $f = g$ it is $\mathcal S^\varepsilon$, with $f = \hat g_N$ it is $\hat{\mathcal S}^\varepsilon_N$; at $\varepsilon = 0$ these are the optimal sets $\mathcal S^*$ and $\hat{\mathcal S}_N$. Its complement in $\mathcal S$ is $\mathcal S \setminus \mathcal S^\varepsilon = \{x \in \mathcal S : f(x) > \min_{\mathcal S} f + \varepsilon\}$.
--   4. When $\mathcal S \setminus \mathcal S^\varepsilon$ is nonempty, the **well-conditioning number** of (2.3) is
--   $$\alpha(\varepsilon) = \min_{x \in \mathcal S \setminus \mathcal S^\varepsilon} g(x) - v^* - \varepsilon.$$
--   5. The **maximal deviation** of (2.2) is $\delta_N = \max_{x \in \mathcal S} |\hat g_N(x) - g(x)|$.
--   6. **Assumption A** (p. 4): for every $x \in \mathcal S$ the moment generating function $M(t) = \mathbb E\, e^{t G(x,W)}$ is finite for all $t$ in a neighbourhood of $0$.
--   7. For a real random variable $X$ with i.i.d. copies $X_1, X_2, \dots$, the sample average is $Z_N = N^{-1}\sum_{i=1}^N X_i$, and the **rate function** is
--   $$I(z) = \sup_{t \ge 0} \{ t z - \Lambda(t) \}, \qquad \Lambda(t) = \log M(t) = \log \mathbb E\, e^{tX} \in (-\infty, +\infty].$$
--
--   These are the objects of Propositions 2.1 and 2.2: the probability that every $\varepsilon$-optimal solution of the SAA problem is $\varepsilon$-optimal for the true problem, and the large-deviations rate at which it tends to one.
--
--   **Formalization Note** Minima and maxima over $\mathcal S$ are `Finset.inf'`/`Finset.sup'` over the nonempty finite set, so they are attained and never junk values; $\alpha(\varepsilon)$ takes the nonemptiness of $\mathcal S \setminus \mathcal S^\varepsilon$ as an argument. The sample is a $0$-indexed sequence `W : ℕ → Ω → 𝒲`; the paper's $W^n$ is `W (n - 1)` and the expectation $g$ is taken against the first term. At $N = 0$ the sample average is the junk value $0$; every statement about a fixed sample size assumes $N \ge 1$. Assumption A is stated as integrability of $e^{tG(x,W)}$ near $0$ (Mathlib's `integrableExpSet`), not through the value of `mgf`, which is $0$ where the expectation is infinite. $\Lambda$ is the published `BellWilliams2001.ThresholdPolicy.logMGF`, the extended-real logarithm of the lower Lebesgue integral of $e^{tX}$, which equals $+\infty$ where $M(t) = +\infty$; a $t$ with $\Lambda(t) = +\infty$ contributes $-\infty$ to the supremum, so $I(z) \in [0, +\infty]$ is computed in the extended reals.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), pp. 1–4, (1.1), (2.1), (2.2), (2.3), Assumption A, the rate function I(z) below (2.4)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation

namespace KleywegtSAA.ExpRate

open MeasureTheory ProbabilityTheory

/-!
Kleywegt & Shapiro, *The sample average approximation method for stochastic discrete optimization*
(two-author preprint), §1 (1.1), §2 (2.1), §2.1 (2.2), (2.3), §2.2 (2.4), Assumption A, pp. 1–4.

A finite feasible set `S : Finset X`, an integrand `G : X → 𝒲 → ℝ`, and a sample sequence
`W : ℕ → Ω → 𝒲` on a probability space `(Ω, P)`; the paper's `Wⁿ` (`n = 1, 2, …`) is `W (n - 1)`.
-/

/-- The true objective `g(x) = E_P G(x, W)` of (1.1), with `W` distributed as the first sample `W 0`. -/
noncomputable def trueObj {X 𝒲 Ω : Type*} [MeasurableSpace Ω] (G : X → 𝒲 → ℝ) (P : Measure Ω)
    (W : ℕ → Ω → 𝒲) (x : X) : ℝ :=
  ∫ ω, G x (W 0 ω) ∂P

/-- The sample average function `ĝ_N(x) = N⁻¹ ∑_{n=1}^N G(x, Wⁿ)` of §2, evaluated along the
realization `ω`; the paper's `Wⁿ` is `W (n - 1)`. -/
noncomputable def sampleObj {X 𝒲 Ω : Type*} (G : X → 𝒲 → ℝ) (W : ℕ → Ω → 𝒲) (N : ℕ) (ω : Ω)
    (x : X) : ℝ :=
  (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, G x (W n ω)

/-- The optimal value `min_{x ∈ S} f(x)` of a real function over the nonempty finite set `S`;
`v* = minVal S hS g` and `v̂_N = minVal S hS ĝ_N`. -/
noncomputable def minVal {X : Type*} (S : Finset X) (hS : S.Nonempty) (f : X → ℝ) : ℝ :=
  S.inf' hS f

/-- The set of `ε`-optimal solutions `{x ∈ S : f(x) ≤ min_S f + ε}`; with `f = g` this is `S^ε`,
with `f = ĝ_N` it is `Ŝ^ε_N`; at `ε = 0` these are `S*` and `Ŝ_N`. -/
def epsSet {X : Type*} (S : Finset X) (hS : S.Nonempty) (f : X → ℝ) (ε : ℝ) : Set X :=
  {x | x ∈ S ∧ f x ≤ minVal S hS f + ε}

/-- The finite set `S \ S^ε = {x ∈ S : f(x) > min_S f + ε}` of points that are not `ε`-optimal. -/
noncomputable def nonOptSet {X : Type*} (S : Finset X) (hS : S.Nonempty) (f : X → ℝ) (ε : ℝ) :
    Finset X :=
  S.filter (fun x => minVal S hS f + ε < f x)

/-- `α(ε) = min_{x ∈ S \ S^ε} f(x) − min_S f − ε` of (2.3), defined when `S \ S^ε` is nonempty. -/
noncomputable def alpha {X : Type*} (S : Finset X) (hS : S.Nonempty) (f : X → ℝ) (ε : ℝ)
    (hne : (nonOptSet S hS f ε).Nonempty) : ℝ :=
  (nonOptSet S hS f ε).inf' hne f - minVal S hS f - ε

/-- `δ_N = max_{x ∈ S} |ĝ_N(x) − g(x)|` of (2.2), along the realization `ω`. -/
noncomputable def devMax {X 𝒲 Ω : Type*} [MeasurableSpace Ω] (S : Finset X) (hS : S.Nonempty)
    (G : X → 𝒲 → ℝ) (P : Measure Ω) (W : ℕ → Ω → 𝒲) (N : ℕ) (ω : Ω) : ℝ :=
  S.sup' hS (fun x => |sampleObj G W N ω x - trueObj G P W x|)

/-- Assumption A (p. 4): for every `x ∈ S` the moment generating function `t ↦ E e^{t G(x, W)}` is
finite in a neighbourhood of `t = 0`, i.e. `0` is an interior point of the set of `t` for which
`e^{t G(x, W)}` is integrable. -/
def AssumptionA {X 𝒲 Ω : Type*} [MeasurableSpace Ω] (S : Finset X) (G : X → 𝒲 → ℝ)
    (P : Measure Ω) (W : ℕ → Ω → 𝒲) : Prop :=
  ∀ x ∈ S, (0 : ℝ) ∈ interior (integrableExpSet (fun ω => G x (W 0 ω)) P)

/-- The sample average `Z_N = N⁻¹ ∑_{i=1}^N X_i` of a real sequence (§2.2); `X_i` is `Y (i - 1)`. -/
noncomputable def sampleMean {Ω : Type*} (Y : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (1 / (N : ℝ)) * ∑ i ∈ Finset.range N, Y i ω

/-- The large-deviations rate function `I(z) = sup_{t ≥ 0} {t z − Λ(t)}` of §2.2, where
`Λ(t) = log E e^{tY} ∈ (−∞, +∞]` is the logarithmic moment generating function
(`BellWilliams2001.ThresholdPolicy.logMGF`). A `t` with `E e^{tY} = +∞` contributes `−∞`.
The value lies in `[0, +∞]`. -/
noncomputable def rateFn {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) (z : ℝ) :
    EReal :=
  ⨆ (t : ℝ) (_ : 0 ≤ t), ((t * z : ℝ) : EReal) - BellWilliams2001.ThresholdPolicy.logMGF P Y t

end KleywegtSAA.ExpRate


