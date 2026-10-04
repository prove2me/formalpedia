-- Prove2me | Definitions.Def_StochApproxDyn_Interpolation_AsymptoticPseudotrajectory
-- name    : StochApproxDyn_Interpolation_AsymptoticPseudotrajectory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:52:50.04992+00:00
-- url     : https://prove2.me/theorems/1828a595-94e7-407d-9cbb-2235a88f8360
-- title:
--   Asymptotic pseudotrajectories, the translation flow Θ, trajectories S_Φ and limit points of {Θ^t(X)}
-- statement:
--   This file fixes the dynamical vocabulary of §3 of Benaïm's notes, on a metric space $(M,d)$.
--
--   1. **Asymptotic pseudotrajectory.** Let $\Phi$ be a flow on $M$ (or a semiflow; only the maps $\Phi_h$ with $h\ge0$ enter). A continuous map $X:\mathbb R_+\to M$ is an *asymptotic pseudotrajectory* of $\Phi$ if for every $T>0$
--   $$\lim_{t\to\infty}\ \sup_{0\le h\le T} d\big(X(t+h),\Phi_h(X(t))\big)=0 .$$
--   For each fixed $T$, the curve $h\mapsto X(t+h)$ on $[0,T]$ shadows the $\Phi$-trajectory of $X(t)$ with arbitrary accuracy once $t$ is large.
--   2. **Translation flow.** $C^0(\mathbb R,M)$ is the space of continuous maps $\mathbb R\to M$ with the topology of uniform convergence on compact intervals. A continuous $X:\mathbb R_+\to M$ is regarded as an element of $C^0(\mathbb R,M)$ by setting $X(s)=X(0)$ for $s<0$, and $\Theta^t(X)(s)=X(t+s)$.
--   3. **Trajectories.** For a flow $\Phi$ and $p\in M$, $\Phi^p(s)=\Phi_s(p)$, $s\in\mathbb R$, and $S_\Phi=\{\Phi^p:p\in M\}\subseteq C^0(\mathbb R,M)$. An element $Y$ lies in $S_\Phi$ exactly when it is a fixed point of the retraction $\hat\Phi(Y)=\Phi^{Y(0)}$.
--   4. **Limit points.** $Y\in C^0(\mathbb R,M)$ is a *limit point of $\{\Theta^t(X)\}$* if $Y=\lim_k\Theta^{t_k}(X)$ in $C^0(\mathbb R,M)$ for some sequence $t_k\to\infty$.
--
--   These notions are the language of the mission's goal: the interpolated stochastic approximation process is shown to be an asymptotic pseudotrajectory of the flow of the mean vector field.
--
--   **Formalization Note** The time half-line $\mathbb R_+$ is `ℝ≥0`; the extension $X(s)=X(0)$ for $s<0$ is `X ∘ Real.toNNReal`. The dynamics in the asymptotic pseudotrajectory definition is a bare function `Φ : ℝ → M → M`, used only at times `h ≥ 0`, so it applies to a flow given by hypotheses (as the flow of a vector field is) as well as to Mathlib's bundled `Flow ℝ M`. The limit is written with $\varepsilon$: for all $T>0$, $\varepsilon>0$ there is $t_0$ with $d(X(t+h),\Phi_h(X(t)))<\varepsilon$ for $t\ge t_0$, $0\le h\le T$; this is equivalent to the supremum tending to $0$ and involves no real supremum. $C^0(\mathbb R,M)$ is Mathlib's `C(ℝ, M)` with the compact-open topology, which for a metric target is the topology of uniform convergence on compacts, the topology of the paper's metric $d(f,g)=\sum_k2^{-k}\min(1,d_k(f,g))$. $S_\Phi$ is stated for flows (`Flow ℝ M`): with the paper's semiflow convention $\Phi^p(t)=p$ for $t<0$ the characterization in Theorem 3.2 fails (see the mission notes).
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 9, §3 (semiflow, asymptotic pseudotrajectory); p. 10, §3.1 (C⁰(ℝ,M), translation flow Θ, S_Φ, retraction Φ̂, footnote 1)

import Mathlib

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- An *asymptotic pseudotrajectory* (Benaïm 1999, §3, p. 9): a continuous `X : ℝ₊ → M` such that
for every `T > 0`, `lim_{t → ∞} sup_{0 ≤ h ≤ T} d(X(t + h), Φ_h(X(t))) = 0`. The dynamics
`Φ : ℝ → M → M` is a flow or (through its values at `h ≥ 0`) a semiflow; only `Φ_h` with
`h ≥ 0` is used. The limit is written with `ε`: for all `T > 0` and `ε > 0` there is `t₀` with
`d(X(t + h), Φ_h(X(t))) < ε` for all `t ≥ t₀` and `0 ≤ h ≤ T`. -/
def IsAsymptoticPseudotrajectory {M : Type*} [MetricSpace M] (Φ : ℝ → M → M) (X : ℝ≥0 → M) :
    Prop :=
  Continuous X ∧
    ∀ T : ℝ≥0, 0 < T → ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t → ∀ h : ℝ≥0, h ≤ T →
      dist (X (t + h)) (Φ (h : ℝ) (X t)) < ε

/-- The translate `Θ^t(X) ∈ C⁰(ℝ, M)`, `Θ^t(X)(s) = X(t + s)` (p. 10), where `X : ℝ₊ → M` is
extended to `ℝ` by `X(s) = X(0)` for `s < 0`; `Real.toNNReal` performs this extension. -/
def translate {M : Type*} [MetricSpace M] (X : C(ℝ≥0, M)) (t : ℝ≥0) : C(ℝ, M) :=
  ⟨fun s => X (Real.toNNReal ((t : ℝ) + s)),
    X.continuous.comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))⟩

/-- The trajectory `Φ^p : s ↦ Φ_s(p)` of a point `p` under a flow `Φ`, an element of
`C⁰(ℝ, M)` (p. 10). -/
def trajectory {M : Type*} [MetricSpace M] (Φ : Flow ℝ M) (p : M) : C(ℝ, M) :=
  ⟨fun s => Φ s p, Φ.continuous continuous_id continuous_const⟩

/-- `S_Φ ⊆ C⁰(ℝ, M)`, the set of all trajectories `Φ^p`, `p ∈ M` (p. 10). An element `Y` lies in
`S_Φ` iff it is a fixed point of the retraction `Φ̂(Y) = Φ^{Y(0)}`. -/
def trajectorySet {M : Type*} [MetricSpace M] (Φ : Flow ℝ M) : Set C(ℝ, M) :=
  Set.range (trajectory Φ)

/-- `Y` is a *limit point of `{Θ^t(X)}`* (p. 10, footnote 1): `Y` is the limit in `C⁰(ℝ, M)`
(compact-open topology, i.e. uniform convergence on compact intervals) of a sequence
`Θ^{t_k}(X)` with `t_k → ∞`. -/
def IsLimitPointOfTranslates {M : Type*} [MetricSpace M] (X : C(ℝ≥0, M)) (Y : C(ℝ, M)) : Prop :=
  ∃ t : ℕ → ℝ≥0, Tendsto t atTop atTop ∧ Tendsto (fun k => translate X (t k)) atTop (𝓝 Y)

end StochApproxDyn.Interpolation


