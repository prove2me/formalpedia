-- Prove2me | Definitions.Def_FracPSG_Abstract_Basic
-- name    : FracPSG_Abstract_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:07:55.304031+00:00
-- url     : https://prove2.me/theorems/f59546fd-546f-46b6-9158-ef62ab8b9346
-- title:
--   The abstract descent framework (H1)–(H5), cluster sets Ω and Ω₀, and the KL property with an exponent (pp. 6, 13–15)
-- statement:
--   Let $\mathcal K$ and $\mathcal H$ be finite-dimensional real Hilbert spaces. This file fixes the objects of the abstract convergence framework of Boţ, Dao and Li.
--
--   1. **KL property with an exponent.** A function $h:\mathcal K\to(-\infty,+\infty]$ has the Kurdyka–Łojasiewicz property at $\bar z$ *with exponent* $a\in[0,1)$ when there are $\eta>0$, a neighbourhood $V$ of $\bar z$ and $\gamma>0$ such that, with $\varphi(s)=\gamma s^{1-a}$,
--   $$\varphi'\big(h(z)-h(\bar z)\big)\,\operatorname{dist}\big(0,\partial_L h(z)\big)\ge 1\quad\text{for all } z\in V \text{ with } h(\bar z)<h(z)<h(\bar z)+\eta .$$
--   2. **Cluster sets.** For a sequence $(z_n)$, $\Omega$ is the set of its cluster points and $\Omega_0:=\{\bar z\in\Omega: h(z_n)\to h(\bar z)\}$.
--   3. **Standing setting (p. 13).** $h$ is proper and lower semicontinuous; $(\alpha_n)$, $(\beta_n)$ are positive; $(\varepsilon_n)$ and $(\Delta_n)$ are nonnegative, with $\Delta_k=0$ for $k<0$; $\underline\imath\le\bar\imath$ are integers (possibly negative), $I=\{\underline\imath,\dots,\bar\imath\}$, and $\lambda_i\ge0$ with $\sum_{i\in I}\lambda_i=1$.
--   4. **Conditions (H1)–(H5).** For all $n\in\mathbb N$:
--      - (H1) $h(z_{n+1})+\alpha_n\Delta_n^2\le h(z_n)$;
--      - (H2) $\beta_n\operatorname{dist}(0,\partial_L h(z_n))\le\sum_{i\in I}\lambda_i\Delta_{n-i}+\varepsilon_n$;
--      - (H3) some subsequence $z_{k_n}\to\tilde z$ has $h(z_{k_n})\to h(\tilde z)$;
--      - (H4) $\inf_n\alpha_n>0$, $\inf_n\alpha_n\beta_n>0$ and $\sum_n\varepsilon_n<+\infty$;
--      - (H5) there are $j\in\mathbb Z$, $c\in\mathbb R$ with $\|x_{n+1}-x_n\|\le c\,\Delta_{n+j}$.
--   5. **Positivity of $\underline\delta=\inf_{n\in\mathbb N,\,i\in I}\alpha_{n-i}\beta_n^2$**, expressed as: some $d>0$ satisfies $d\le\alpha_{n-i}\beta_n^2$ for every $n\in\mathbb N$ and $i\in I$ with $n-i\ge0$.
--
--   These conditions abstract the convergence analysis of inexact, multi-step descent methods: (H1) is a sufficient decrease, (H2) a relative error bound involving several past (or future) steps, and (H5) ties the iterates $x_n$ of an algorithm to the quantities $\Delta_n$.
--
--   **Formalization Note** $\mathcal K$ is `EuclideanSpace ℝ (Fin P)` and $\mathcal H$ is `EuclideanSpace ℝ (Fin N)` in the theorems; the definitions are stated for any real inner-product space. $\Delta$ is a function on $\mathbb Z$, which encodes the paper's convention $\Delta_k=0$ for $k<0$. $\operatorname{dist}(0,\partial_L h(z))$ is never computed with `Metric.infDist` (which gives $0$ on $\emptyset$, while the paper's distance is $+\infty$): (H2) asks for some $v\in\partial_L h(z_n)$ with $\beta_n\|v\|\le\cdots$, which is equivalent because $\partial_L h(z_n)$ is closed, and which forces $h(z_n)<+\infty$. The KL exponent uses the published `KLIneq`, which quantifies over every $v\in\partial_L h(z)$. In $\underline\delta$, $\alpha_{n-i}$ is only defined for $n-i\ge0$; only such pairs are constrained. The summability $\sum_{n\ge1}\varepsilon_n<\infty$ of (H4) is `Summable ε`, the same thing for a nonnegative sequence.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 6 (KL property with an exponent), p. 13 (setting of §5), p. 14 (H1)–(H5), Lemma 5.1(iii) (δ̲)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty

open Filter Topology

namespace FracPSG.Abstract

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

/-- The KL property with an exponent (Boţ–Dao–Li, arXiv:2003.04124v2, p. 6): `h` has the KL
property at `x̄` with exponent `a ∈ [0, 1)` when the desingularizing function of the KL property
can be chosen as `φ(s) = γ s^{1-a}` with `γ > 0`, i.e. there are `η > 0` and a neighbourhood `V`
of `x̄` such that `γ(1-a)(h(x) - h(x̄))^{-a} ‖v‖ ≥ 1` for every `x ∈ V` with
`h(x̄) < h(x) < h(x̄) + η` and every `v ∈ ∂_L h(x)`. (The exponent is called `a`, not `α`, because
the paper also uses `α` for the sequence `αₙ`.) -/
def HasKLPropertyExp {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (h : X → EReal) (xbar : X) (a : ℝ) : Prop :=
  0 ≤ a ∧ a < 1 ∧ ∃ η : ℝ, 0 < η ∧ ∃ V ∈ 𝓝 xbar, ∃ γ : ℝ, 0 < γ ∧
    KLIneq h xbar η V (fun s => γ * s ^ (1 - a))

/-- The set `Ω` of cluster points of a sequence `(zₙ)`. -/
def clusterSet {X : Type*} [TopologicalSpace X] (z : ℕ → X) : Set X :=
  {zbar | MapClusterPt zbar atTop z}

/-- The set `Ω₀ := {z̄ ∈ Ω : h(zₙ) → h(z̄) as n → +∞}` (Boţ–Dao–Li, Lemma 2.3, Lemma 5.1). -/
def omega0 {X : Type*} [TopologicalSpace X] (h : X → EReal) (z : ℕ → X) : Set X :=
  {zbar | zbar ∈ clusterSet z ∧ Tendsto (fun n => h (z n)) atTop (𝓝 (h zbar))}

/-- The standing setting of §5 (Boţ–Dao–Li, p. 13): `h : 𝒦 → (-∞, +∞]` is proper and lower
semicontinuous; `αₙ, βₙ > 0`; `εₙ ≥ 0`; `Δ` is a nonnegative sequence indexed by `ℤ` with
`Δ_k = 0` for `k < 0`; `ı̲ ≤ ı̄` are integers (`ilo`, `ihi`) and `λᵢ ≥ 0` for
`i ∈ I = {ı̲, …, ı̄}` with `∑_{i ∈ I} λᵢ = 1`. -/
structure AbstractSetting {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (h : K → EReal) (α β ε : ℕ → ℝ) (Δ : ℤ → ℝ) (ilo ihi : ℤ) (lam : ℤ → ℝ) : Prop where
  proper : IsProperFn h
  lsc : LowerSemicontinuous h
  alpha_pos : ∀ n, 0 < α n
  beta_pos : ∀ n, 0 < β n
  eps_nonneg : ∀ n, 0 ≤ ε n
  delta_nonneg : ∀ k, 0 ≤ Δ k
  delta_neg : ∀ k, k < 0 → Δ k = 0
  ilo_le_ihi : ilo ≤ ihi
  lam_nonneg : ∀ i ∈ Finset.Icc ilo ihi, 0 ≤ lam i
  lam_sum : ∑ i ∈ Finset.Icc ilo ihi, lam i = 1

/-- (H1) Sufficient decrease condition: `h(zₙ₊₁) + αₙΔₙ² ≤ h(zₙ)` for each `n ∈ ℕ`. -/
def H1 {K : Type*} (h : K → EReal) (z : ℕ → K) (α : ℕ → ℝ) (Δ : ℤ → ℝ) : Prop :=
  ∀ n : ℕ, h (z (n + 1)) + ((α n * Δ n ^ 2 : ℝ) : EReal) ≤ h (z n)

/-- (H2) Relative error condition: `βₙ dist(0, ∂_L h(zₙ)) ≤ ∑_{i ∈ I} λᵢΔₙ₋ᵢ + εₙ` for each
`n ∈ ℕ`. Since `∂_L h(zₙ)` is closed, the distance is attained when the set is nonempty, and
`dist(0, ∅) = +∞`; so the condition says that some `v ∈ ∂_L h(zₙ)` has
`βₙ‖v‖ ≤ ∑_{i ∈ I} λᵢΔₙ₋ᵢ + εₙ`. -/
def H2 {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (h : K → EReal) (z : ℕ → K) (β ε : ℕ → ℝ) (Δ : ℤ → ℝ) (ilo ihi : ℤ) (lam : ℤ → ℝ) :
    Prop :=
  ∀ n : ℕ, ∃ v ∈ LimitingSubdiff h (z n),
    β n * ‖v‖ ≤ ∑ i ∈ Finset.Icc ilo ihi, lam i * Δ ((n : ℤ) - i) + ε n

/-- (H3) Continuity condition: there are a subsequence `(z_{kₙ})` and `z̃` with `z_{kₙ} → z̃` and
`h(z_{kₙ}) → h(z̃)`. -/
def H3 {K : Type*} [TopologicalSpace K] (h : K → EReal) (z : ℕ → K) : Prop :=
  ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ zt : K, Tendsto (fun n => z (k n)) atTop (𝓝 zt) ∧
    Tendsto (fun n => h (z (k n))) atTop (𝓝 (h zt))

/-- (H4) Parameter condition: `inf αₙ > 0`, `inf αₙβₙ > 0` and `∑ εₙ < +∞` (for nonnegative
`εₙ`, summability is the finiteness of the series). -/
def H4 (α β ε : ℕ → ℝ) : Prop :=
  (∃ a : ℝ, 0 < a ∧ ∀ n, a ≤ α n) ∧ (∃ g : ℝ, 0 < g ∧ ∀ n, g ≤ α n * β n) ∧ Summable ε

/-- (H5) Distance condition: there are `j ∈ ℤ` and `c ∈ ℝ` with `‖xₙ₊₁ - xₙ‖ ≤ cΔₙ₊ⱼ` for all
`n ∈ ℕ`. -/
def H5 {H : Type*} [NormedAddCommGroup H] (x : ℕ → H) (Δ : ℤ → ℝ) : Prop :=
  ∃ j : ℤ, ∃ c : ℝ, ∀ n : ℕ, ‖x (n + 1) - x n‖ ≤ c * Δ ((n : ℤ) + j)

/-- The positivity of `δ̲ = inf_{n ∈ ℕ, i ∈ I} α_{n-i} βₙ²` (Lemma 5.1(iii), Theorem 5.2(iv)),
read over the pairs for which `α_{n-i}` is defined (`n - i ≥ 0`): some `d > 0` bounds every such
`α_{n-i} βₙ²` from below. -/
def DeltaLowerBound (α β : ℕ → ℝ) (ilo ihi : ℤ) (d : ℝ) : Prop :=
  0 < d ∧ ∀ n : ℕ, ∀ i ∈ Finset.Icc ilo ihi, 0 ≤ (n : ℤ) - i →
    d ≤ α ((n : ℤ) - i).toNat * β n ^ 2

end FracPSG.Abstract


