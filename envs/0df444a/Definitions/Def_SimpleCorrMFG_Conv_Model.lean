-- Prove2me | Definitions.Def_SimpleCorrMFG_Conv_Model
-- name    : SimpleCorrMFG_Conv_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:46.20433+00:00
-- url     : https://prove2.me/theorems/d6813839-75c6-4ebb-bd3c-f24e81984b71
-- title:
--   §2, (A1), (A2), pp. 4–5, 17–18 — the finite model: $\mathcal P(\mathcal X)$, dist, $\Psi$, $f$, $F$, restricted strategies, assumptions (A1)–(A2)
-- statement:
--   This file sets up the data of the discrete-time, finite-state mean field game of Campi and Fischer.
--
--   **Spaces.** Fix a horizon $T\in\mathbb N$ (initial time zero), a nonempty finite set $\mathcal X$ of individual states and a nonempty finite set $\Gamma$ of actions, both with the discrete topology and σ-algebra. The noise space is $\mathcal Z=[0,1]$ with the uniform distribution $\nu$. The set $\mathcal P(\mathcal X)$ of probability measures on $\mathcal X$ carries the metric
--   $$\mathrm{dist}(m,\tilde m)=\frac12\sum_{x\in\mathcal X}|m(x)-\tilde m(x)|,$$
--   which induces the topology of weak convergence. For a finite family of points $x_j$, $j\in S$, with $S\neq\emptyset$, the empirical measure is $|S|^{-1}\sum_{j\in S}\delta_{x_j}$; in particular, for states $x=(x_1,\dots,x_N)$ the empirical measure of all players except $l$ is $\mu_l=(N-1)^{-1}\sum_{j\neq l}\delta_{x_j}$. The product law $\otimes^N m$ on $\mathcal X^N$ is also defined here. A flow of measures is a vector $(m(0),\dots,m(T))\in\mathcal P(\mathcal X)^{T+1}$.
--
--   **Model data.** A model consists of a system function $\Psi:\{0,\dots,T-1\}\times\mathcal X\times\mathcal P(\mathcal X)\times\Gamma\times\mathcal Z\to\mathcal X$, a running cost $f:\{0,\dots,T-1\}\times\mathcal X\times\mathcal P(\mathcal X)\times\Gamma\to\mathbb R$ and a terminal cost $F:\mathcal X\times\mathcal P(\mathcal X)\to\mathbb R$. The standing assumptions (p. 5) are that $\Psi$ is measurable and that $f$ and $F$ are bounded and measurable.
--
--   **Strategies.** A restricted strategy is a map $\varphi:\{0,\dots,T-1\}\times\mathcal X\to\Gamma$; their (finite) set is $\mathcal R$. A strategy modification is any map $u:\mathcal R\to\mathcal R$.
--
--   **Assumptions.**
--   1. (A1) There is a measurable $w:[0,\infty)\to[0,1]$ with $w(s)\to0$ as $s\to0^+$ such that for all $t,x,a$ and all $m,\tilde m\in\mathcal P(\mathcal X)$
--   $$\int_{\mathcal Z}\mathbf 1_{\Psi(t,x,m,a,z)\neq\Psi(t,x,\tilde m,a,z)}\,\nu(dz)\le w(\mathrm{dist}(m,\tilde m));$$
--   moreover, for every $t$ and every probability measure $\tau$ on $\mathcal X\times\mathcal P(\mathcal X)\times\Gamma$, $\Psi(t,\cdot)$ is continuous at $\tau\otimes\nu$-almost every point.
--   2. (A2) The cost coefficients $f$ and $F$ are continuous.
--
--   **Formalization Note** $\mathcal P(\mathcal X)$ is the standard simplex `stdSimplex ℝ X` with the subspace topology and Borel σ-algebra of $\mathbb R^{\mathcal X}$; `Meas.toPM` turns a point of the simplex into a probability measure. $\nu$ is `volume` on `unitInterval`. Times of actions and noises are `Fin T`, times of states and flows are `Fin (T+1)`; `iterFin` builds a path from its initial value and one-step maps. The empirical measure `empOn S x` of an empty family is a junk Dirac mass, never used. (A1) is split into its two parts `A1a`, `A1b`; the modulus $w$ is a measurable function on $\mathbb R$ with values in $[0,1]$ on $[0,\infty)$. As time, $\mathcal X$ and $\Gamma$ are discrete, (A2) is continuity in the measure argument. The standing assumptions are `Model.Standing`.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, pp. 4–5 (§2, dist, (2.1) setting, model data, R, U), pp. 17–18 ((A1), (A2))

import Mathlib

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- `P(X)` (§2, p. 4): the probability measures on the finite set `X`, represented as the standard
simplex `{p : X → ℝ | p ≥ 0, ∑ₓ p x = 1}` with the subspace topology and Borel σ-algebra of
`X → ℝ`. On a finite set these are the topology and σ-algebra of weak convergence. -/
abbrev Meas (X : Type) [Fintype X] : Type := ↥(stdSimplex ℝ X)

/-- The metric `dist(m, m̃) := ½ ∑_{x ∈ X} |m(x) − m̃(x)|` on `P(X)` (§2, p. 4). -/
noncomputable def distTV {X : Type} [Fintype X] (m m' : Meas X) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |(m : X → ℝ) x - (m' : X → ℝ) x|

/-- An element of the simplex as a probability measure on `X`: `∑ₓ m(x) δₓ`. -/
noncomputable def Meas.toPM {X : Type} [Fintype X] [MeasurableSpace X] (m : Meas X) :
    ProbabilityMeasure X :=
  ⟨(PMF.ofFintype (fun x => ENNReal.ofReal ((m : X → ℝ) x)) (by
      have h : ∑ x, ENNReal.ofReal ((m : X → ℝ) x) = ENNReal.ofReal (∑ x, (m : X → ℝ) x) :=
        (ENNReal.ofReal_sum_of_nonneg (fun x _ => m.2.1 x)).symm
      exact h.trans (by simp))).toMeasure,
    inferInstance⟩

/-- The product law `⊗^N m` on `X^N` (the initial law of assumption (A5), p. 18). -/
noncomputable def prodInit {X : Type} [Fintype X] [MeasurableSpace X] (N : ℕ) (m : Meas X) :
    ProbabilityMeasure (Fin N → X) :=
  ⟨Measure.pi (fun _ : Fin N => ((m.toPM : ProbabilityMeasure X) : Measure X)), inferInstance⟩

/-- The empirical measure `|S|⁻¹ ∑_{j ∈ S} δ_{x_j}` of the points `x_j`, `j ∈ S`, as an element of
`P(X)`. For `S = ∅` it is not defined in the paper; here it is set to the Dirac mass at an arbitrary
point of `X` (a junk value, never used: every statement takes `S` nonempty). -/
noncomputable def empOn {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {ι : Type}
    (S : Finset ι) (x : ι → X) : Meas X :=
  if hS : S.Nonempty then
    ⟨fun y => (∑ j ∈ S, if x j = y then (1 : ℝ) else 0) / (S.card : ℝ), by
      have hpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
      refine ⟨fun y => div_nonneg (Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num) hpos.le, ?_⟩
      rw [← Finset.sum_div, Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, nsmul_eq_mul,
        mul_one]
      exact div_self hpos.ne'⟩
  else ⟨Pi.single (Classical.arbitrary X) 1, single_mem_stdSimplex ℝ _⟩

/-- `μ_l^N = (N−1)⁻¹ ∑_{j ≠ l} δ_{x_j}` (p. 6): the empirical measure of the states of all players
except player `l`. Meaningful for `N ≥ 2`; for `N = 1` it is the junk value of `empOn ∅`. -/
noncomputable abbrev empOthers {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {N : ℕ}
    (x : Fin N → X) (l : Fin N) : Meas X :=
  empOn (Finset.univ.erase l) x

/-- Flows of measures `(m(0), …, m(T)) ∈ P(X)^{T+1}`. -/
abbrev Flow (T : ℕ) (X : Type) [Fintype X] : Type := Fin (T + 1) → Meas X

/-- The set `R = {φ : {0, …, T−1} × X → Γ}` of restricted strategies (p. 5); time `t` is
`t : Fin T`. A strategy modification `u ∈ U` is any map `Strat T X Γ → Strat T X Γ`. -/
abbrev Strat (T : ℕ) (X Γ : Type) : Type := Fin T → X → Γ

/-- The path `(s(0), …, s(T))` generated from `s(0) = s₀` by `s(t+1) = step t (s(t))`,
`t ∈ {0, …, T−1}`. -/
def iterFin {T : ℕ} {S : Type} (s₀ : S) (step : Fin T → S → S) : Fin (T + 1) → S :=
  fun t => go t.val
where
  go : ℕ → S
    | 0 => s₀
    | k + 1 => if h : k < T then step ⟨k, h⟩ (go k) else go k

/-- The model data of §2 (p. 5): the system function `Ψ : {0,…,T−1} × X × P(X) × Γ × Z → X`
with noise space `Z = [0,1]`, the running cost `f : {0,…,T−1} × X × P(X) × Γ → ℝ` and the
terminal cost `F : X × P(X) → ℝ`. -/
structure Model (T : ℕ) (X Γ : Type) [Fintype X] where
  Ψ : Fin T → X → Meas X → Γ → I → X
  f : Fin T → X → Meas X → Γ → ℝ
  F : X → Meas X → ℝ

namespace Model

variable {T : ℕ} {X Γ : Type} [Fintype X] [MeasurableSpace X] [MeasurableSpace Γ]

/-- The standing assumptions of §2 (p. 5): `Ψ` is measurable, and `f`, `F` are bounded and
measurable. -/
def Standing (M : Model T X Γ) : Prop :=
  (∀ t, Measurable (fun p : X × Meas X × Γ × I => M.Ψ t p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧
  (∀ t, Measurable (fun p : X × Meas X × Γ => M.f t p.1 p.2.1 p.2.2)) ∧
  Measurable (fun p : X × Meas X => M.F p.1 p.2) ∧
  ∃ C : ℝ, (∀ t x m a, |M.f t x m a| ≤ C) ∧ ∀ x m, |M.F x m| ≤ C

/-- First part of assumption (A1) (p. 17): there is a measurable `w : [0,∞) → [0,1]` with
`w(s) → 0` as `s → 0+` such that `ν{z : Ψ(t,x,m,a,z) ≠ Ψ(t,x,m̃,a,z)} ≤ w(dist(m, m̃))`. -/
def A1a (M : Model T X Γ) : Prop :=
  ∃ w : ℝ → ℝ, Measurable w ∧ (∀ s, 0 ≤ s → 0 ≤ w s ∧ w s ≤ 1) ∧
    Tendsto w (𝓝[>] 0) (𝓝 0) ∧
    ∀ (t : Fin T) (x : X) (a : Γ) (m m' : Meas X),
      (volume : Measure I) {z | M.Ψ t x m a z ≠ M.Ψ t x m' a z} ≤ ENNReal.ofReal (w (distTV m m'))

/-- Second part of assumption (A1) (p. 17): for every `t` and every probability measure `τ` on
`X × P(X) × Γ`, the map `Ψ(t, ·)` on `X × P(X) × Γ × Z` is continuous at `τ ⊗ ν`-almost every
point. -/
def A1b [TopologicalSpace X] [TopologicalSpace Γ] (M : Model T X Γ) : Prop :=
  ∀ (t : Fin T) (τ : Measure (X × Meas X × Γ)), IsProbabilityMeasure τ →
    ∀ᵐ p ∂(τ.prod (volume : Measure I)),
      ContinuousAt (fun q : (X × Meas X × Γ) × I => M.Ψ t q.1.1 q.1.2.1 q.1.2.2 q.2) p

/-- Assumption (A1) (p. 17): both parts. -/
def A1 [TopologicalSpace X] [TopologicalSpace Γ] (M : Model T X Γ) : Prop :=
  M.A1a ∧ M.A1b

/-- Assumption (A2) (p. 18): the cost coefficients `f` and `F` are continuous. Since time, `X` and
`Γ` are discrete, this is continuity in the measure argument. -/
def A2 (M : Model T X Γ) : Prop :=
  (∀ (t : Fin T) (x : X) (a : Γ), Continuous (fun m : Meas X => M.f t x m a)) ∧
  ∀ x : X, Continuous (fun m : Meas X => M.F x m)

end Model

end SimpleCorrMFG.Conv


