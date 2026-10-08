-- Prove2me | Definitions.Def_MFGLimit_LDP_LDP
-- name    : MFGLimit_LDP_LDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:21:54.43199+00:00
-- url     : https://prove2.me/theorems/8fcc6100-71ae-4446-b60b-4db6f2fc5cc3
-- title:
--   Large deviation bounds at speed n: lower bound on open sets, upper bounds on compact and closed sets, F_δ, good rate functions
-- statement:
--   The vocabulary of large deviations used in Theorems 3.9, 3.10, 6.8, 6.13 and Proposition 6.15.
--
--   Let $(S,D)$ be a metric space and, for each $n$, let $Y_n$ be a random element of $S$; let $J:S\to[0,\infty]$. The sets of $S$ are open, closed or compact for the topology of $D$; the closed $\delta$-enlargement of $F\subseteq S$ is $F_\delta=\{y: \inf_{x\in F}D(x,y)\le\delta\}$. The bounds are:
--
--   1. lower bound on open sets: $\liminf_{n\to\infty}\frac1n\log\mathbb P(Y_n\in O)\ge-\inf_{x\in O}J(x)$;
--   2. upper bound on compact sets: $\limsup_{n\to\infty}\frac1n\log\mathbb P(Y_n\in K)\le-\inf_{x\in K}J(x)$;
--   3. upper bound on closed sets: $\limsup_{n\to\infty}\frac1n\log\mathbb P(Y_n\in F)\le-\inf_{x\in F}J(x)$;
--   4. relaxed upper bound on closed sets:
--   $$\limsup_{n\to\infty}\frac1n\log\mathbb P(Y_n\in F)\le-\lim_{\delta\searrow0}\inf_{x\in F_\delta}J(x).$$
--
--   $J$ is a good rate function if it is lower semicontinuous and its level sets $\{J\le a\}$, $a\ge0$, are compact.
--
--   **Formalization Note** Logarithms are taken in $[-\infty,\infty]$ (`EReal`, $\log 0=-\infty$) and rates in $[0,\infty]$. A random element is represented by its events $\{Y_n\in A\}$; $\mathbb P$ of a possibly non-measurable event is the outer measure. Open, closed and compact sets are those of the metric $D$ (balls; complements; sequential compactness). Since $\delta\mapsto\inf_{F_\delta}J$ is non-increasing, $\lim_{\delta\searrow0}$ is written as the supremum over $\delta>0$.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, pp. 14–15, Theorems 3.9–3.10; p. 28, Theorem 6.8; p. 32, Proposition 6.15

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLimit.LDP

variable {S : Type*}

/-! The topology of a space `S` carrying a metric `D : S → S → ℝ≥0∞` (open balls `{y : D x y < ε}`),
and the bounds of a (weak) large deviation principle at speed `n` for random elements of `S`. -/

/-- `O` is open for the metric `D`: it contains a `D`-ball around each of its points. -/
def IsOpenD (D : S → S → ℝ≥0∞) (O : Set S) : Prop :=
  ∀ x ∈ O, ∃ ε : ℝ≥0∞, 0 < ε ∧ {y | D x y < ε} ⊆ O

/-- `F` is closed for the metric `D`: its complement is open. -/
def IsClosedD (D : S → S → ℝ≥0∞) (F : Set S) : Prop := IsOpenD D Fᶜ

/-- `K` is compact for the metric `D` (sequentially): every sequence of `K` has a subsequence
converging in `D` to a point of `K`. -/
def IsCompactD (D : S → S → ℝ≥0∞) (K : Set S) : Prop :=
  ∀ u : ℕ → S, (∀ k, u k ∈ K) →
    ∃ x ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => D (u (φ k)) x) atTop (𝓝 0)

/-- The closed `δ`-enlargement `F_δ = {y : inf_{x ∈ F} D(x, y) ≤ δ}`. -/
def enlarge (D : S → S → ℝ≥0∞) (F : Set S) (δ : ℝ≥0∞) : Set S := {y | ⨅ x ∈ F, D x y ≤ δ}

/-- `(1/n) log p` in `EReal` (with `log 0 = −∞`). -/
noncomputable def scaledLog (n : ℕ) (p : ℝ≥0∞) : EReal := (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log p

variable {Ω : Type*} [MeasurableSpace Ω]

/-- LDP lower bound with rate `J` for the events `ev n A = {Y_n ∈ A}`: for every open `O`,
`liminf_n (1/n) log P(Y_n ∈ O) ≥ − inf_{x ∈ O} J(x)`. -/
def LDPLower (P : Measure Ω) (ev : ℕ → Set S → Set Ω) (D : S → S → ℝ≥0∞) (J : S → ℝ≥0∞) :
    Prop :=
  ∀ O, IsOpenD D O →
    -(((⨅ x ∈ O, J x : ℝ≥0∞)) : EReal) ≤ liminf (fun n => scaledLog n (P (ev n O))) atTop

/-- LDP upper bound on compact sets: `limsup_n (1/n) log P(Y_n ∈ K) ≤ − inf_{x ∈ K} J(x)`. -/
def LDPUpperCompact (P : Measure Ω) (ev : ℕ → Set S → Set Ω) (D : S → S → ℝ≥0∞)
    (J : S → ℝ≥0∞) : Prop :=
  ∀ K, IsCompactD D K →
    limsup (fun n => scaledLog n (P (ev n K))) atTop ≤ -(((⨅ x ∈ K, J x : ℝ≥0∞)) : EReal)

/-- LDP upper bound on closed sets: `limsup_n (1/n) log P(Y_n ∈ F) ≤ − inf_{x ∈ F} J(x)`. -/
def LDPUpperClosed (P : Measure Ω) (ev : ℕ → Set S → Set Ω) (D : S → S → ℝ≥0∞)
    (J : S → ℝ≥0∞) : Prop :=
  ∀ F, IsClosedD D F →
    limsup (fun n => scaledLog n (P (ev n F))) atTop ≤ -(((⨅ x ∈ F, J x : ℝ≥0∞)) : EReal)

/-- The relaxed upper bound on closed sets:
`limsup_n (1/n) log P(Y_n ∈ F) ≤ − lim_{δ↘0} inf_{x ∈ F_δ} J(x)`; since `δ ↦ inf_{F_δ} J` is
non-increasing, the limit `δ ↘ 0` equals the supremum over `δ > 0`. -/
def LDPUpperClosedDelta (P : Measure Ω) (ev : ℕ → Set S → Set Ω) (D : S → S → ℝ≥0∞)
    (J : S → ℝ≥0∞) : Prop :=
  ∀ F, IsClosedD D F →
    limsup (fun n => scaledLog n (P (ev n F))) atTop ≤
      -(((⨆ (δ : ℝ≥0∞) (_ : 0 < δ), ⨅ x ∈ enlarge D F δ, J x : ℝ≥0∞)) : EReal)

/-- `J` is a good rate function for `D`: lower semicontinuous and with compact level sets
`{J ≤ a}`, `a ≥ 0`. -/
def IsGoodRate (D : S → S → ℝ≥0∞) (J : S → ℝ≥0∞) : Prop :=
  (∀ x (u : ℕ → S), Tendsto (fun k => D (u k) x) atTop (𝓝 0) →
      J x ≤ liminf (fun k => J (u k)) atTop) ∧
    ∀ a : ℝ≥0, IsCompactD D {x | J x ≤ a}

end MFGLimit.LDP


