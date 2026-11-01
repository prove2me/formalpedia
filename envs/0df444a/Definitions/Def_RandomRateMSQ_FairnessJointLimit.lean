-- Prove2me | Definitions.Def_RandomRateMSQ_FairnessJointLimit
-- name    : RandomRateMSQ_FairnessJointLimit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:28:11.003975+00:00
-- url     : https://prove2.me/theorems/5b2f8a7c-112a-4644-8036-e9ea6f1f7fb0
-- title:
--   Joint convergence in distribution of the initial condition, rate fluctuation, noise and shifted fairness processes
-- statement:
--   The prelimit tuple of the $n$-th system is
--
--   $$
--   \Theta^n=\big(\hat X^n(0),\ \hat\sigma^n,\ \hat N^n,\ (\tau^n_{\varepsilon_k})_{k\ge0},\ (S^n_{\varepsilon_k}\eta^n)_{k\ge0}\big),\qquad \varepsilon_k=\frac1{k+1},
--   $$
--
--   and a limit tuple is $\Theta=\big(\xi_0,\ \tilde\sigma,\ N,\ (\tau_{\varepsilon_k})_k,\ (S_{\varepsilon_k}\eta)_k\big)$ with $S_{\varepsilon_k}\eta$ the shift of a limit process $\eta$ at $\tau_{\varepsilon_k}$.
--
--   $\Theta^n\Rightarrow\Theta$ **jointly** means: on some probability space there are a copy of each $\Theta^n$ and a copy of $\Theta$ such that almost surely the real components converge, the noise paths converge in Skorokhod $J_1$ (càdlàg), each $\tau^n_{\varepsilon_k}$ converges in $[0,\infty]$, and each $S^n_{\varepsilon_k}\eta^n$ converges in left-continuous $J_1$ with the Lévy–Prokhorov distance.
--
--   When this holds, $\eta$ is the limiting fairness process of Definition 1 along $\varepsilon_k$, and $\hat X^n(0)\Rightarrow\xi_0$ (Assumption 2). Nothing is assumed about what $N$ and $\tilde\sigma$ are; Theorem 5 identifies them.
--
--   **Formalization Note** This is the joint reading of the paper's hypothesis "the sequence of fairness processes has a unique limiting process" (p.17), used jointly on p.18 through the limit of $\Xi^n$. The joint law matters: the law of the limit $\xi$ depends on it.
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, Definition 1, p.10, and proof of Theorem 5, pp.17–18

import Mathlib
import Definitions.Def_RandomRateMSQ_fairness

open MeasureTheory ProbabilityTheory Filter Topology
open PuhaWardFluid.Limit
open scoped NNReal ENNReal

namespace RandomRateMSQ

/-- The space of the tuple `Θ = (initial condition, rate fluctuation, noise path,
(τ_{ε_k})_k, (S_{ε_k} η)_k)` of the proof of Theorem 5 (Büke–Qin, arXiv:1905.04198v1, p.18).
Measurable structure: products and countable products of the Borel σ-algebras (paths carry the
product σ-algebra; `ProbabilityMeasure ℝ≥0` its Giry σ-algebra). -/
abbrev Theta : Type :=
  ℝ × ℝ × (ℝ≥0 → ℝ) × (ℕ → ℝ≥0∞) × (ℕ → ℝ≥0 → ProbabilityMeasure ℝ≥0)

/-- The shift levels `ε_k = 1/(k + 1)`, `k = 0, 1, 2, …` (the paper's `ε_k = 1/k`, `k ≥ 1`,
arXiv:1905.04198v1, p.10 and p.18). -/
noncomputable def epsK (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

/-- The prelimit tuple `Θⁿ = (X̂ⁿ(0), σ̂ⁿ, N̂ⁿ, (τⁿ_{ε_k})_k, (Sⁿ_{ε_k} ηⁿ)_k)` of the `n`-th
system (arXiv:1905.04198v1, proof of Theorem 5, p.18, with the noise `N̂ⁿ = Âⁿ − M̂ⁿ₁ − M̂ⁿ₂` in
place of its three summands). -/
noncomputable def thetaN {Ω : Type*} {n : ℕ} (F : Measure ℝ≥0) (lam γ : ℝ)
    (ζ : ProbabilityMeasure ℝ≥0) (s : System Ω n) (ω : Ω) : Theta :=
  (Xhat s ω 0, sigmaHat F s ω, Nhat lam γ s ω, fun k => tau s (epsK k) ω,
    fun k => shiftedFairness ζ s (epsK k) ω)

/-- The limit tuple `Θ = (ξ₀, σ̃, N, (τ_{ε_k})_k, (S_{ε_k} η)_k)` built from the limit objects; its
fairness components are literally `shift ζ τ_{ε_k} η` (Definition 1, p.10: "define S_ε η by
replacing τⁿ_ε with τ_ε in (3.4)"). -/
noncomputable def thetaLim {Ω' : Type*} (ζ : ProbabilityMeasure ℝ≥0) (ξ₀ σ : Ω' → ℝ)
    (N : Ω' → ℝ≥0 → ℝ) (τ : ℕ → Ω' → ℝ≥0∞) (η : Ω' → ℝ≥0 → ProbabilityMeasure ℝ≥0)
    (ω : Ω') : Theta :=
  (ξ₀ ω, σ ω, N ω, fun k => τ k ω, fun k => shift ζ (τ k ω) (η ω))

/-- Pathwise convergence of tuples: the two real components converge; the noise paths converge in
`J₁` (public `PuhaWardFluid.Limit.J1Tendsto`, càdlàg paths); each `τ_{ε_k}` converges in `[0, ∞]`;
each shifted fairness path converges in left-continuous `J₁` with the Lévy–Prokhorov distance
(each component with its own time changes: the product topology). -/
def ThetaConverges (θs : ℕ → Theta) (θ : Theta) : Prop :=
  Tendsto (fun n => (θs n).1) atTop (𝓝 θ.1) ∧
  Tendsto (fun n => (θs n).2.1) atTop (𝓝 θ.2.1) ∧
  J1Tendsto (fun a b : ℝ => dist a b) (fun n => (θs n).2.2.1) θ.2.2.1 ∧
  (∀ k, Tendsto (fun n => (θs n).2.2.2.1 k) atTop (𝓝 (θ.2.2.2.1 k))) ∧
  ∀ k, J1LeftTendsto lpDist (fun n => (θs n).2.2.2.2 k) (θ.2.2.2.2 k)

/-- **Joint convergence in distribution of the tuples** `Θⁿ ⇒ Θ`, in coupling form: on some
probability space there are, for every `n`, a copy of the whole tuple `Θⁿ` (one law on `Theta`) and
a copy of `Θ`, such that almost surely `ThetaConverges`.

This is the hypothesis of Theorem 5 read jointly (arXiv:1905.04198v1, p.17: "we assume that the
sequence of fairness processes has a unique limiting process in the sense in Definition 1", and
p.18, where the limit of `Ξⁿ = (X̂ⁿ(0), Âⁿ, M̂ⁿ₁, M̂ⁿ₂, σ̂ⁿ, Sⁿ_{ε₁}ηⁿ, …)` is used as a joint law).
Nothing is assumed about which processes the noise and rate components converge to. -/
def FairnessJointLimit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Θn : ℕ → Ω → Theta)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (Θ : Ω' → Theta) : Prop :=
  IsProbabilityMeasure P ∧ IsProbabilityMeasure P' ∧
    ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'') (W : ℕ → Ω'' → Theta)
      (W' : Ω'' → Theta),
      IsProbabilityMeasure P'' ∧ (∀ n, IdentDistrib (W n) (Θn n) P'' P) ∧
      IdentDistrib W' Θ P'' P' ∧ ∀ᵐ ω ∂P'', ThetaConverges (fun n => W n ω) (W' ω)

end RandomRateMSQ


