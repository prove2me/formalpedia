-- Prove2me | Definitions.Def_SensitivityPoA_Lipschitz_SpecialCosts
-- name    : SensitivityPoA_Lipschitz_SpecialCosts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T17:38:55.81164+00:00
-- url     : https://prove2.me/theorems/57834058-a316-4405-9935-0516d422088d
-- title:
--   Theorem 12 hypotheses — costs constant on [0, T(d)]; costs C¹ on [0, T(d)] with derivative ≥ m
-- statement:
--   Two hypotheses on a game $\Gamma=(\tau,d)$ that appear in Theorem 12 of Wu and Möhring.
--
--   1. **Constant costs on the used range.** Every arc cost is constant on $[0,T(d)]$:
--   $$\tau_a(x)=\tau_a(0)\qquad\text{for all } a\in A,\ x\in[0,T(d)].$$
--   Nothing is assumed about $\tau_a$ beyond $T(d)$.
--   2. **Continuously differentiable costs with slope at least $m$.** For a constant $m$, every arc cost $\tau_a$ is continuously differentiable on the closed interval $[0,T(d)]$ and
--   $$\tau_a'(x)\ge m\qquad\text{for all } a\in A,\ x\in[0,T(d)],$$
--   where the derivative at the endpoints $0$ and $T(d)$ is one-sided.
--
--   These are the two special classes of games at which the price of anarchy is locally Lipschitz continuous (Theorem 12 a) and b)).
--
--   **Formalization Note** The second hypothesis is `ContDiffOn ℝ 1` on `Set.Icc 0 (T d)` together with a lower bound on `derivWithin` relative to that interval, which is the one-sided derivative at the endpoints and the ordinary derivative inside. The positivity $m>0$ is a separate hypothesis of the theorems that use it.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), pp. 36–37, Theorem 12a)–b) hypotheses

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Lipschitz_Setting

namespace SensitivityPoA.Lipschitz

variable {N : Network}

/-- Theorem 12a)'s hypothesis: every arc cost of `Γ` is constant on `[0, T(d)]`,
`τ_a(x) = τ_a(0)` for all arcs `a` and all `x ∈ [0, T(d)]`. -/
def ConstOnDemand (Γ : Game N) : Prop :=
  ∀ j, ∀ x ∈ Set.Icc 0 (totalDemand Γ.d), Γ.τ j x = Γ.τ j 0

/-- Theorem 12b)'s hypothesis with slope `m`: every arc cost of `Γ` is continuously
differentiable on `[0, T(d)]` with derivative (one-sided at the endpoints) at least `m`. -/
def C1SlopeOnDemand (Γ : Game N) (m : ℝ) : Prop :=
  ∀ j, ContDiffOn ℝ 1 (Γ.τ j) (Set.Icc 0 (totalDemand Γ.d)) ∧
    ∀ x ∈ Set.Icc 0 (totalDemand Γ.d), m ≤ derivWithin (Γ.τ j) (Set.Icc 0 (totalDemand Γ.d)) x

end SensitivityPoA.Lipschitz


