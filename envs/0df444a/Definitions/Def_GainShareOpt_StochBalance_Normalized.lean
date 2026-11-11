-- Prove2me | Definitions.Def_GainShareOpt_StochBalance_Normalized
-- name    : GainShareOpt_StochBalance_Normalized
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:46:54.791693+00:00
-- url     : https://prove2.me/theorems/68323b06-98bb-40ff-9280-03b1d8032d60
-- title:
--   The class $G$, the functionals $A(g)$, $H_g(\sigma,\ell)$ and the fixed-domain Program (73) (App. J.1)
-- statement:
--   Let $G$ be the set of continuous, non-increasing $g:[0,1]\to[1/e,1]$. For $g\in G$ and $0\le\ell\le\sigma\le1$ put
--   $$A(g)=1-\frac1{e^2}-\int_0^1e^{-z}g(z)\,dz,\qquad H_g(\sigma,\ell)=1-e^{-\sigma}+(1-\sigma+\ell)\,g(\sigma)-\int_0^\ell e^{-z}g(z)\,dz .$$
--   **Program (73)** maximizes $\gamma$ over $\gamma\in\mathbb R$, $g\in G$ subject to $A(g)\ge\gamma$ and $H_g(\sigma,\ell)\ge\gamma$ for all $0\le\ell\le\sigma\le1$. We also write $\min_{0\le\ell\le\sigma\le1}H_g(\sigma,\ell)$ for its partial-load constraint value.
--
--   This is the normalized form $g=1-f$ of Program (31) used in the comparison argument.
--
--   **Formalization Note** Profiles are `ℝ → ℝ`; membership in $G$ constrains them on $[0,1]$ only. The minimum of $H_g$ is a real `sInf`.
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 49, (70)–(73)

import Mathlib

namespace GainShareOpt.StochBalance

/-- The class `G` of Appendix J.1: continuous non-increasing `g` on `[0, 1]` with
`1/e ≤ g ≤ 1`. -/
def ClassG : Set (ℝ → ℝ) :=
  {g | ContinuousOn g (Set.Icc 0 1) ∧ AntitoneOn g (Set.Icc 0 1) ∧
    ∀ z ∈ Set.Icc (0 : ℝ) 1, Real.exp (-1) ≤ g z ∧ g z ≤ 1}

/-- The scalar functional `A(g) = 1 - 1/e² - ∫_0^1 e^{-z} g(z) dz` (71). -/
noncomputable def scoreA (g : ℝ → ℝ) : ℝ :=
  1 - 1 / Real.exp 1 ^ 2 - ∫ z in (0 : ℝ)..1, Real.exp (-z) * g z

/-- The partial-load test `H_g(σ, ℓ) = 1 - e^{-σ} + (1 - σ + ℓ) g(σ) - ∫_0^ℓ e^{-z} g(z) dz` (72). -/
noncomputable def testH (g : ℝ → ℝ) (σ ℓ : ℝ) : ℝ :=
  1 - Real.exp (-σ) + (1 - σ + ℓ) * g σ - ∫ z in (0 : ℝ)..ℓ, Real.exp (-z) * g z

/-- Feasibility of `(γ, g)` in the fixed-domain Program (73). -/
def Feasible73 (γ : ℝ) (g : ℝ → ℝ) : Prop :=
  g ∈ ClassG ∧ γ ≤ scoreA g ∧ ∀ σ ℓ : ℝ, 0 ≤ ℓ → ℓ ≤ σ → σ ≤ 1 → γ ≤ testH g σ ℓ

/-- The supremal value of Program (73). -/
noncomputable def gamma73 : ℝ :=
  sSup {γ | ∃ g, Feasible73 γ g}

/-- `min_{0 ≤ ℓ ≤ σ ≤ 1} H_g(σ, ℓ)`, the partial-load constraint value of Program (73). -/
noncomputable def minTestH (g : ℝ → ℝ) : ℝ :=
  sInf {r | ∃ σ ℓ : ℝ, 0 ≤ ℓ ∧ ℓ ≤ σ ∧ σ ≤ 1 ∧ r = testH g σ ℓ}

end GainShareOpt.StochBalance


