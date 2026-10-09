-- Prove2me | Definitions.Def_SBMThreshold_Main_Setting
-- name    : SBMThreshold_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:15:26.16541+00:00
-- url     : https://prove2.me/theorems/36587c92-0f9e-4d26-946b-e50998014f1f
-- title:
--   Definition 1.1, p. 2 — the stochastic block model G(n, a/n, b/n), d and s, conditioning on σ_U, the overlap and an estimator's success probability
-- statement:
--   This file fixes the probabilistic objects of E. Mossel, J. Neeman and A. Sly, *A Proof of the Block Model Threshold Conjecture*.
--
--   **The stochastic block model.** Let $n\ge 0$ and $a,b>0$. In $\mathcal G(n,a/n,b/n)$ every vertex $u\in\{1,\dots,n\}$ receives, independently and uniformly at random, a label $\sigma_u\in\{+1,-1\}$; then, given the labels, each unordered pair $\{u,v\}$, $u\ne v$, is an edge independently with probability
--   $$
--   q_{uv}(\sigma)=\begin{cases} a/n & \text{if } \sigma_u=\sigma_v,\\ b/n & \text{if } \sigma_u\ne\sigma_v.\end{cases}
--   $$
--   So the labelled graph $(\sigma,G)$ has probability
--   $$
--   \mathbb P(\sigma,G)=2^{-n}\prod_{\{u,v\}}\bigl(q_{uv}(\sigma)\,\mathbf 1_{uv\in E(G)}+(1-q_{uv}(\sigma))\,\mathbf 1_{uv\notin E(G)}\bigr).
--   $$
--   Expectations $\mathbb E[X]$ and probabilities $\mathbb P[E]$ of functions $X(\sigma,G)$ and events $E(\sigma,G)$ are the corresponding finite sums.
--
--   **Parameters.** $d=(a+b)/2$ is the average degree and $s=(a-b)/2$; $s$ may be negative.
--
--   **Conditioning.** For a vertex set $U$ and a labelling $\tau$, $\mathbb E[X\mid\sigma_U=\tau_U]$ is the average of $X$ over the labelled graphs whose labels agree with $\tau$ on $U$, weighted by $\mathbb P(\sigma,G)$; the event $\sigma_U=\tau_U$ has probability $2^{-|U|}>0$. $\mathbb P[E\mid\sigma_U=\tau_U]$ is the conditional expectation of the indicator of $E$.
--
--   **Overlap and detection.** The overlap of labellings $\sigma,\tau$ is
--   $$
--   \operatorname{ov}(\sigma,\tau)=\Bigl|\frac1n\sum_{v}\sigma_v\tau_v\Bigr| ,
--   $$
--   which is invariant under the global flip $\tau\mapsto-\tau$. An estimator is a map $\hat\tau$ from graphs to probability distributions on labellings: it sees only $G$, and may use internal randomness. Its success probability at level $\varepsilon$ is $\mathbb P[\operatorname{ov}(\sigma,\hat\tau(G))\ge\varepsilon]$, the probability taken jointly over $(\sigma,G)\sim\mathcal G(n,a/n,b/n)$ and over the estimator's randomness.
--
--   These are the objects in which Theorems 2.1–2.3 and the moment estimates of Theorem 2.8 and Lemmas 3.5 and 5.1 are stated.
--
--   **Formalization Note** Vertices are `Fin n`, graphs `SimpleGraph (Fin n)`, labellings `Fin n → Bool` with `true ↦ +1`, `false ↦ -1`. The product runs over the pairs $u<v$, so each unordered pair is counted once. For $n\le\max(a,b)$ the numbers $a/n$, $b/n$ are not probabilities (Definition 1.1 has $q,q'\in(0,1)$); non-asymptotic theorems of the mission assume $a,b<n$, and asymptotic ones only concern large $n$. An estimator's output law is a `PMF` on the finite set of labellings, so it is a genuine probability distribution for every graph.
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 2, Definition 1.1 and §1.2; p. 3, §1.3; p. 6, Theorem 2.9 (overlap)

import Mathlib

namespace SBMThreshold.Main

/-! Mossel, Neeman and Sly, *A Proof of the Block Model Threshold Conjecture*, arXiv:1311.4115v4:
the stochastic block model `G(n, a/n, b/n)` (Definition 1.1, p. 2; §1.2, p. 2), the parameters
`d = (a+b)/2`, `s = (a-b)/2`, conditioning on the labels of a vertex set (§1.3, p. 3), and the
overlap of a labelling with the planted one (Theorem 2.9, p. 6).

Vertices are `Fin n`, graphs are `SimpleGraph (Fin n)`, labellings are `Fin n → Bool` with
`true ↦ +1`, `false ↦ -1`. Every probability and expectation is a finite sum over pairs
`(σ, G)` weighted by the joint law of Definition 1.1. -/

open Finset
open scoped Classical

/-- The label `±1` of a Boolean label: `spin true = 1`, `spin false = -1`. -/
def spin (x : Bool) : ℝ := if x then 1 else -1

/-- `d = (a + b)/2` (§1.2, p. 2). -/
noncomputable def dPar (a b : ℝ) : ℝ := (a + b) / 2

/-- `s = (a - b)/2` (§1.2, p. 2); `s` may be negative. -/
noncomputable def sPar (a b : ℝ) : ℝ := (a - b) / 2

/-- The probability that `{u, v}` is an edge, given the labelling `σ`: `q = a/n` if
`σ_u = σ_v`, and `q' = b/n` otherwise (Definition 1.1 with `q = a/n`, `q' = b/n`). -/
noncomputable def edgeProb (n : ℕ) (a b : ℝ) (σ : Fin n → Bool) (u v : Fin n) : ℝ :=
  if σ u = σ v then a / n else b / n

/-- The unordered pairs `{u, v}`, `u ≠ v`, of vertices, each listed once as `(u, v)` with `u < v`. -/
def vertexPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  univ.filter (fun p => p.1 < p.2)

/-- The joint probability of the labelling `σ` and the graph `G` in `G(n, a/n, b/n)`: the labels
are i.i.d. uniform on `{±1}` (factor `2⁻ⁿ`), and given `σ` each unordered pair `{u, v}` is an edge
independently with probability `edgeProb n a b σ u v`. -/
noncomputable def sbmWeight (n : ℕ) (a b : ℝ) (σ : Fin n → Bool) (G : SimpleGraph (Fin n)) : ℝ :=
  (1 / 2 : ℝ) ^ n * ∏ p ∈ vertexPairs n,
    (if G.Adj p.1 p.2 then edgeProb n a b σ p.1 p.2 else 1 - edgeProb n a b σ p.1 p.2)

/-- `E[X(σ, G)]` for `(σ, G) ∼ G(n, a/n, b/n)`. -/
noncomputable def sbmExp (n : ℕ) (a b : ℝ) (X : (Fin n → Bool) → SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∑ σ : Fin n → Bool, ∑ G : SimpleGraph (Fin n), sbmWeight n a b σ G * X σ G

/-- `P[E]` for an event `E` of the labelled graph `(σ, G) ∼ G(n, a/n, b/n)`. -/
noncomputable def sbmProb (n : ℕ) (a b : ℝ) (E : (Fin n → Bool) → SimpleGraph (Fin n) → Prop) : ℝ :=
  sbmExp n a b (fun σ G => if E σ G then 1 else 0)

/-- `σ` agrees with `τ` on the vertex set `U`, i.e. `σ_U = τ_U`. -/
def AgreeOn {n : ℕ} (U : Finset (Fin n)) (σ τ : Fin n → Bool) : Prop :=
  ∀ u ∈ U, σ u = τ u

/-- The conditional expectation `E[X | σ_U = τ_U]` in `G(n, a/n, b/n)`: the weighted average of
`X` over the labelled graphs whose labelling agrees with `τ` on `U`. The denominator is the
probability `2^{-|U|}` of `σ_U = τ_U`, which is positive. -/
noncomputable def condExp (n : ℕ) (a b : ℝ) (U : Finset (Fin n)) (τ : Fin n → Bool)
    (X : (Fin n → Bool) → SimpleGraph (Fin n) → ℝ) : ℝ :=
  (∑ σ ∈ univ.filter (fun σ => AgreeOn U σ τ), ∑ G : SimpleGraph (Fin n),
      sbmWeight n a b σ G * X σ G) /
    (∑ σ ∈ univ.filter (fun σ => AgreeOn U σ τ), ∑ G : SimpleGraph (Fin n), sbmWeight n a b σ G)

/-- The conditional probability `P[E | σ_U = τ_U]` in `G(n, a/n, b/n)`. -/
noncomputable def condProb (n : ℕ) (a b : ℝ) (U : Finset (Fin n)) (τ : Fin n → Bool)
    (E : (Fin n → Bool) → SimpleGraph (Fin n) → Prop) : ℝ :=
  condExp n a b U τ (fun σ G => if E σ G then 1 else 0)

/-- The overlap `|(1/n) Σ_v σ_v τ_v|` of two labellings (Theorem 2.9, p. 6); the absolute value
makes it invariant under the global flip `τ ↦ -τ`. -/
noncomputable def overlap {n : ℕ} (σ τ : Fin n → Bool) : ℝ :=
  |(1 / (n : ℝ)) * ∑ v : Fin n, spin (σ v) * spin (τ v)|

/-- The probability that the randomized estimator `τhat`, which sees only the graph `G`, outputs
a labelling whose overlap with the planted labelling `σ` is at least `ε`:
`P[|(1/n) Σ_v σ_v τ_v| ≥ ε]`, the probability taken over `(σ, G) ∼ G(n, a/n, b/n)` and over the
internal randomness of the estimator (its output law `τhat G`). -/
noncomputable def detectProb (n : ℕ) (a b : ℝ) (τhat : SimpleGraph (Fin n) → PMF (Fin n → Bool))
    (ε : ℝ) : ℝ :=
  ∑ σ : Fin n → Bool, ∑ G : SimpleGraph (Fin n),
    sbmWeight n a b σ G * ((τhat G).toOuterMeasure {τ | ε ≤ overlap σ τ}).toReal

end SBMThreshold.Main


