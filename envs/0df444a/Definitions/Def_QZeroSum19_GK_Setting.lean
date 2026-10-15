-- Prove2me | Definitions.Def_QZeroSum19_GK_Setting
-- name    : QZeroSum19_GK_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:58:34.691888+00:00
-- url     : https://prove2.me/theorems/e239749c-df9b-4e6b-89f8-a4dfe507890f
-- title:
--   §1–2 and Definition 5, pp. 1–3, 7 — matrix game value, ε-optimal strategies, Gibbs distribution, Algorithm 1 and its sample-path law
-- statement:
--   This file fixes the objects of the classical part of van Apeldoorn and Gilyén's paper: a two-player zero-sum matrix game, its value, $\varepsilon$-optimal strategies, the Gibbs distribution, and the randomized algorithm of Grigoriadis and Khachiyan (Algorithm 1) described through the probability law of its sample paths.
--
--   1. **The game** (p. 1). A matrix $A\in\mathbb R^{n\times m}$; Alice picks a row $i\in[n]$ and receives $A_{ij}$, Bob picks a column $j\in[m]$ and receives $-A_{ij}$. Mixed strategies are points of the simplices $\Delta^n$ and $\Delta^m$.
--   2. **The value** (LP (1), p. 2). $$v^* = \min_{y\in\Delta^m}\ \max_{i\in[n]}\ (Ay)_i .$$
--   3. **$\varepsilon$-optimality** (p. 2). Bob's $y\in\Delta^m$ is $\varepsilon$-optimal when $Ay\le (v^*+\varepsilon)e$; Alice's $x\in\Delta^n$ is $\varepsilon$-optimal when $A^{\mathsf T}x\ge (v^*-\varepsilon)e$ (here $e$ is the all-ones vector).
--   4. **Gibbs distribution** (Definition 5, p. 7). For $v\in\mathbb R^k$, $G(v)_l = e^{v_l}/\sum_{l'} e^{v_{l'}}$.
--   5. **ℓ₁-normalization** $v\mapsto v/\|v\|_1$, written $(\sum_k v_k)^{-1}v$, and the **potential** $\Phi(x,y)=\big(\sum_{j} e^{-(A^{\mathsf T}x)_j}\big)\big(\sum_i e^{(Ay)_i}\big)$ used in the proof of Lemma 1 (p. 4).
--   6. **Algorithm 1** (p. 3). Start from $x=0\in\mathbb R^n$, $y=0\in\mathbb R^m$. In iteration $\tau=1,2,\dots$, with step $\eta(\tau)$, sample independently $a\sim p=G(-A^{\mathsf T}x)$ in $[m]$ and $b\sim q=G(Ay)$ in $[n]$, both computed from the current iterates, and update $y\leftarrow y+\eta(\tau)e_a$, $x\leftarrow x+\eta(\tau)e_b$. A run of $t$ iterations is a sample path $\omega=((a_1,b_1),\dots,(a_t,b_t))$; after $s\le t$ updates $x_s=\sum_{\tau=1}^{s}\eta(\tau)e_{b_\tau}$ and $y_s=\sum_{\tau=1}^{s}\eta(\tau)e_{a_\tau}$, and the probability of the path is
--   $$\Pr[\omega]=\prod_{\tau=1}^{t} G(-A^{\mathsf T}x_{\tau-1})_{a_\tau}\,G(Ay_{\tau-1})_{b_\tau}.$$
--   Probabilities of events and expectations of functions of the path are the corresponding finite sums.
--   7. **Step schedules** (p. 3): the fixed accuracy-goal step $\eta(\tau)=\varepsilon/4$ and the anytime step $\eta(\tau)=1/(2\sqrt\tau)$, together with the anytime accuracy $\varepsilon'(t)=\frac{2}{\sqrt t}\big(3\ln t+\ln(nm)+\ln(1/\delta)+2\big)$ of Lemma 1.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** The value is the infimum of $y\mapsto\max_i (Ay)_i$ over the *image* of the simplex; for a nonempty column set this image is nonempty and bounded below, so the infimum is the minimum of LP (1). The constraint $\lambda\in[-1,1]$ of LP (1) is inactive for entries in $[-1,1]$ and is not encoded. Algorithm 1 as printed starts its loop at $t=1$ while initializing only $x^{(0)}$; the reading used here is that the $\tau$-th update uses step $\eta(\tau)$ and the Gibbs distributions of the iterates after $\tau-1$ updates, so that $\|x_t\|_1=\sum_{\tau=1}^t\eta(\tau)$ as in the proof's display (3). The path $\omega$ is a map from $\{0,\dots,t-1\}$ to $[m]\times[n]$, entry $\tau$ holding the draws $(a,b)$ of iteration $\tau+1$. The anytime step at $\tau=0$ evaluates to $0$ in Lean and is never read.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 1 (the game), p. 2 (LP (1), (2), value, ε-optimal), p. 3 (Algorithm 1, Lemma 1), p. 4 (potential Φ), p. 7 (Definition 5)

import Mathlib

/-!
# Quantum algorithms for zero-sum games, §1–2: the game and Algorithm 1

J. van Apeldoorn and A. Gilyén, *Quantum algorithms for zero-sum games*, arXiv:1904.03180v1,
pp. 1–3 (the matrix game, LP (1), ε-optimality, Algorithm 1) and p. 7 (Definition 5).

A matrix game is `A : Matrix (Fin n) (Fin m) ℝ`. Alice plays rows `i ∈ [n]` and maximizes `xᵀAy`;
Bob plays columns `j ∈ [m]` and minimizes it. Algorithm 1 is encoded through the law of its
sample path: after `t` iterations the draws are `ω : Fin t → Fin m × Fin n`, where `(ω τ).1` is
Bob's sampled move `a` and `(ω τ).2` is Alice's sampled move `b` of the `(τ+1)`-th iteration.
-/

namespace QZeroSum19.GK

open Matrix

/-- **Definition 5** (p. 7), classical Gibbs distribution: `G(v) = e^v / ‖e^v‖₁`, i.e.
`G(v)_k = e^{v_k} / Σ_l e^{v_l}`. -/
noncomputable def gibbs {ι : Type*} [Fintype ι] (v : ι → ℝ) : ι → ℝ :=
  fun k => Real.exp (v k) / ∑ l, Real.exp (v l)

/-- The **value** of the matrix game `M` (LP (1), p. 2): `min_{y ∈ Δ} max_i (M y)_i`, the
infimum over Bob's mixed strategies `y` of Alice's best pure-response payoff.

The infimum is taken over the image of the simplex, never as `⨅ y ∈ stdSimplex …` (which would
be `min(0, ·)` over `ℝ`). For a nonempty column type the image is nonempty and bounded below. -/
noncomputable def gameValue {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) : ℝ :=
  sInf ((fun y => ⨆ i, (M *ᵥ y) i) '' stdSimplex ℝ κ)

/-- Bob's strategy `y` is **ε-optimal** (p. 2): `y ∈ Δm` and `Ay ≤ (v* + ε) e`. -/
def IsEpsOptimalBob {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) (y : Fin m → ℝ) : Prop :=
  y ∈ stdSimplex ℝ (Fin m) ∧ ∀ i, (A *ᵥ y) i ≤ gameValue A + ε

/-- Alice's strategy `x` is **ε-optimal** ("similar for Alice", p. 2, with Alice's LP (2)):
`x ∈ Δn` and `Aᵀx ≥ (v* − ε) e`. -/
def IsEpsOptimalAlice {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) (x : Fin n → ℝ) : Prop :=
  x ∈ stdSimplex ℝ (Fin n) ∧ ∀ j, gameValue A - ε ≤ (Aᵀ *ᵥ x) j

/-- ℓ₁-normalization `v / ‖v‖₁`, written `(Σ_k v_k)⁻¹ • v`; it agrees with `v / ‖v‖₁` for the
nonnegative iterates of Algorithm 1. -/
noncomputable def normalize {ι : Type*} [Fintype ι] (v : ι → ℝ) : ι → ℝ :=
  (∑ k, v k)⁻¹ • v

/-- The potential `Φ = (Σ_j P_j)(Σ_i Q_i)` of the proof of Lemma 1 (p. 4), with
`P = e^{−Aᵀx}` and `Q = e^{Ay}`. -/
noncomputable def potential {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ)
    (y : Fin m → ℝ) : ℝ :=
  (∑ j, Real.exp (-(Aᵀ *ᵥ x) j)) * (∑ i, Real.exp ((A *ᵥ y) i))

/-- A sample path of `t` iterations of Algorithm 1: `(ω τ).1 = a ∈ [m]` (sampled from `p`, added
to `y`) and `(ω τ).2 = b ∈ [n]` (sampled from `q`, added to `x`) of iteration `τ + 1`. -/
abbrev SamplePath (n m t : ℕ) : Type := Fin t → Fin m × Fin n

/-- Alice's iterate after `s` updates: `x = Σ_{τ=1}^{s} η(τ) e_{b_τ}` (starting from `x = 0`). -/
noncomputable def xAfter {n m t : ℕ} (η : ℕ → ℝ) (ω : SamplePath n m t) (s : ℕ) : Fin n → ℝ :=
  ∑ τ : Fin t, if (τ : ℕ) < s then η ((τ : ℕ) + 1) • Pi.single (ω τ).2 (1 : ℝ) else 0

/-- Bob's iterate after `s` updates: `y = Σ_{τ=1}^{s} η(τ) e_{a_τ}` (starting from `y = 0`). -/
noncomputable def yAfter {n m t : ℕ} (η : ℕ → ℝ) (ω : SamplePath n m t) (s : ℕ) : Fin m → ℝ :=
  ∑ τ : Fin t, if (τ : ℕ) < s then η ((τ : ℕ) + 1) • Pi.single (ω τ).1 (1 : ℝ) else 0

/-- The probability of a sample path under Algorithm 1 with step schedule `η`: the draws of
iteration `τ + 1` are independent, `a ∼ p = G(−Aᵀx)` and `b ∼ q = G(Ay)`, both computed from the
iterates `x, y` after `τ` updates. -/
noncomputable def pathProb {n m t : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (η : ℕ → ℝ)
    (ω : SamplePath n m t) : ℝ :=
  ∏ τ : Fin t, gibbs (-(Aᵀ *ᵥ xAfter η ω τ)) (ω τ).1 * gibbs (A *ᵥ yAfter η ω τ) (ω τ).2

open Classical in
/-- The probability, under the law of the first `t` iterations of Algorithm 1, of an event `E`. -/
noncomputable def prob {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (η : ℕ → ℝ) (t : ℕ)
    (E : SamplePath n m t → Prop) : ℝ :=
  ∑ ω, if E ω then pathProb A η ω else 0

/-- The expectation, under the law of the first `t` iterations of Algorithm 1, of `f`. -/
noncomputable def expect {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (η : ℕ → ℝ) (t : ℕ)
    (f : SamplePath n m t → ℝ) : ℝ :=
  ∑ ω, pathProb A η ω * f ω

/-- The fixed accuracy-goal step `η(τ) = ε/4` (Algorithm 1, p. 3). -/
noncomputable def etaFixed (ε : ℝ) : ℕ → ℝ := fun _ => ε / 4

/-- The anytime step `η(τ) = 1/(2√τ)` (Algorithm 1, p. 3); only read at `τ ≥ 1`. -/
noncomputable def etaAnytime : ℕ → ℝ := fun τ => 1 / (2 * Real.sqrt τ)

/-- The anytime accuracy of Lemma 1 (p. 3): `ε′(t) = (2/√t)(3 ln t + ln(nm) + ln(1/δ) + 2)`. -/
noncomputable def epsAnytime (n m : ℕ) (δ : ℝ) (t : ℕ) : ℝ :=
  2 / Real.sqrt t * (3 * Real.log t + Real.log ((n : ℝ) * m) + Real.log (1 / δ) + 2)

end QZeroSum19.GK


