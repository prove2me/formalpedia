-- Prove2me | Definitions.Def_KleywegtSAA_ValueCLT_Setting
-- name    : KleywegtSAA_ValueCLT_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:16.581491+00:00
-- url     : https://prove2.me/theorems/3bfcf490-bcf8-4d61-8239-203b361a9040
-- title:
--   §1–§2.2, pp. 1, 2, 5 — the finite stochastic program (1.1), its SAA (2.1), optimal values v*, v̂_N, optimal sets 𝒮*, Ŝ_N, and the autocovariance of G(x, W)
-- statement:
--   Let $\mathcal S$ be a nonempty finite set, $G : \mathcal S \times \mathcal W \to \mathbb R$, and let $W^1, W^2, \dots$ be random elements of $\mathcal W$ on a probability space $(\Omega, P)$; $W$ denotes a random element with the common law of the sample.
--
--   1. The **true objective** of problem (1.1) is $g(x) = \mathbb E\, G(x, W)$, and the **sample average function** of §2 is
--   $$\hat g_N(x) = \frac1N \sum_{n=1}^N G(x, W^n),$$
--   evaluated along a realization $\omega$ of the sample.
--   2. The optimal values of the true problem (1.1) and of the sample average approximation (SAA) problem (2.1) are $v^* = \min_{x \in \mathcal S} g(x)$ and $\hat v_N = \min_{x \in \mathcal S} \hat g_N(x)$.
--   3. For a real function $f$ on $\mathcal S$, its set of minimizers is $\{x \in \mathcal S : f(x) = \min_{\mathcal S} f\}$; it is nonempty because $\mathcal S$ is finite. With $f = g$ it is the optimal set $\mathcal S^*$ of (1.1), with $f = \hat g_N$ the optimal set $\hat{\mathcal S}_N$ of (2.1).
--   4. $\min_{x \in \mathcal S^*} \hat g_N(x)$ is the minimum of the sample average function over the true optimal set.
--   5. For a finite set $T \subseteq \mathcal S$, the **autocovariance matrix** of $G(x, W)$ on $T$ is the $T \times T$ matrix with entries $\operatorname{Cov}\big(G(x, W), G(x', W)\big)$, $x, x' \in T$.
--   6. For a finite set $T$, the **scaled deviation vector** is the random vector
--   $$\Big(\sqrt N\,\big[\hat g_N(x) - g(x)\big]\Big)_{x \in T} \in \mathbb R^T.$$
--
--   These are the objects of Proposition 2.3 (the asymptotic distribution of the SAA optimal value) and of the negative-bias inequality preceding it.
--
--   **Formalization Note** Minima over $\mathcal S$ and over $\mathcal S^*$ are `Finset.inf'` over nonempty finite sets, so they are attained and never junk values; $\mathcal S^*$ and $\hat{\mathcal S}_N$ are `Finset`s, and the nonemptiness of a minimizer set is a one-line lemma in this file. The sample is a $0$-indexed sequence `W : ℕ → Ω → 𝒲`; the paper's $W^n$ is `W (n - 1)` and the expectation $g$ is taken against the first term. At $N = 0$ the sample average is the junk value $0$. The autocovariance entries are Mathlib's `covariance`, which is the true covariance only for square-integrable variables; every statement using it assumes finite second moments on the index set. The scaled deviation vector lives in the Euclidean space $\mathbb R^T$ (`EuclideanSpace ℝ T`), where Mathlib's multivariate Gaussian measures are defined.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 1 (1.1), p. 2 (2.1) and the definitions of 𝒮*, Ŝ_N, v*, v̂_N, p. 5 (2.7) and the autocovariance function of G(x, W)

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting

namespace KleywegtSAA.ValueCLT

open MeasureTheory ProbabilityTheory

/-!
Kleywegt & Shapiro, *The sample average approximation method for stochastic discrete optimization*
(two-author preprint), §1 (1.1), §2 (2.1), §2.2 (2.7), pp. 1, 2, 5.

A finite feasible set `S : Finset X`, an integrand `G : X → 𝒲 → ℝ`, and a sample sequence
`W : ℕ → Ω → 𝒲` on a probability space `(Ω, P)`; the paper's `Wⁿ` (`n = 1, 2, …`) is `W (n - 1)`,
and the paper's random vector `W` is represented by the first sample `W 0`.
-/

/-- The set of minimizers `{x ∈ S : f(x) = min_{y ∈ S} f(y)}` of a real function `f` over the
nonempty finite set `S`. With `f = g` this is `S*`, with `f = ĝ_N` it is `Ŝ_N`. -/
noncomputable def optSet {X : Type*} (S : Finset X) (hS : S.Nonempty) (f : X → ℝ) : Finset X :=
  open Classical in S.filter (fun x => f x ≤ S.inf' hS f)

/-- The set of minimizers of `f` over a nonempty finite set is nonempty (the minimum is attained). -/
theorem optSet_nonempty {X : Type*} (S : Finset X) (hS : S.Nonempty) (f : X → ℝ) :
    (optSet S hS f).Nonempty := by
  obtain ⟨x, hx, hmin⟩ := Finset.exists_mem_eq_inf' hS f
  exact ⟨x, Finset.mem_filter.2 ⟨hx, hmin.symm.le⟩⟩

/-- `min_{x ∈ S*} ĝ_N(x)`, the minimum of the sample average function over the set `S*` of optimal
solutions of the true problem (1.1), along the realization `ω`. -/
noncomputable def minOnOpt {X 𝒲 Ω : Type*} [MeasurableSpace Ω] (S : Finset X) (hS : S.Nonempty)
    (G : X → 𝒲 → ℝ) (P : Measure Ω) (W : ℕ → Ω → 𝒲) (N : ℕ) (ω : Ω) : ℝ :=
  (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W)).inf' (optSet_nonempty S hS (KleywegtSAA.ExpRate.trueObj G P W)) (KleywegtSAA.ExpRate.sampleObj G W N ω)

/-- The autocovariance matrix of the random variables `G(x, W)`, `x ∈ T`, indexed by the finite set
`T`: its `(x, x')` entry is `Cov(G(x, W), G(x', W))`. -/
noncomputable def covMat {X 𝒲 Ω : Type*} [MeasurableSpace Ω] (G : X → 𝒲 → ℝ) (P : Measure Ω)
    (W : ℕ → Ω → 𝒲) (T : Finset X) : Matrix T T ℝ :=
  fun x x' => covariance (fun ω => G x (W 0 ω)) (fun ω => G x' (W 0 ω)) P

/-- The random vector `(√N [ĝ_N(x) − g(x)])_{x ∈ T}` in the Euclidean space indexed by `T`, along
the realization `ω`. -/
noncomputable def scaledDev {X 𝒲 Ω : Type*} [MeasurableSpace Ω] (G : X → 𝒲 → ℝ) (P : Measure Ω)
    (W : ℕ → Ω → 𝒲) (T : Finset X) (N : ℕ) (ω : Ω) : EuclideanSpace ℝ T :=
  WithLp.toLp 2 (fun x : T => Real.sqrt N * (KleywegtSAA.ExpRate.sampleObj G W N ω x - KleywegtSAA.ExpRate.trueObj G P W x))

end KleywegtSAA.ValueCLT


