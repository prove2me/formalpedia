-- Prove2me | Definitions.Def_NonlinSSD_DualFunctional_Supplement_TotalDual
-- name    : NonlinSSD_DualFunctional_Supplement_TotalDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:06:40.289959+00:00
-- url     : https://prove2.me/theorems/392ea2be-b5eb-40cd-9a4f-fc789a581992
-- title:
--   Eqs. (30)–(31) — total dual functional, dual feasibility and attained dual optimality
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and let $\mathcal Z$ be the separable locally convex Hausdorff real decision space of the published problem. Its convex decision set is $Z$, its integrable random objective is $H(z)$, its integrable outcome operators are $G_i(z)$, and its integrable reference outcomes are $Y_i$, for $1\le i\le m$. Use the published utility Lagrangian $L$ and utility cones $\mathcal U_1([a_i,b_i])$.
--
--   The **total dual functional**, distinct from the published component $D_i$, is
--
--   $$D(u,\theta)=\sup_{z\in Z,\;X\in\mathcal L_1^m} L(z,X,u,\theta)\in\overline{\mathbb R}.$$
--
--   A dual pair is feasible exactly when every $u_i\in\mathcal U_1([a_i,b_i])$ and every $\theta_i\in\mathcal L_\infty$ is nonnegative almost surely. It is optimal exactly when it is feasible and
--
--   $$D(u,\theta)\le D(v,\zeta)\quad\text{for every feasible pair }(v,\zeta).$$
--
--   These definitions express (30)–(31) without putting primal feasibility, complementarity, a Lagrangian maximizer or a zero duality gap into dual optimality.
--
--   **Formalization Note** The supremum uses `EReal` and ranges over every integrable split vector, without dominance or splitting constraints. It is $-\infty$ for empty $Z$ and $+\infty$ when the Lagrangian is unbounded above. On the admissible domain the utility compositions and multiplier products are integrable: each utility is Lipschitz and each multiplier essentially bounded. The functions are total Lean definitions, but their mathematical domain is the admissible one just specified. The published utility convention $c\ge0$ is inherited, allowing zero utilities; the printed $c>0$ on p. 7 is inconsistent with the cone assertion on that page and with dual attainment (see DISPROOF.md). No finiteness or attainment of the supremum is part of dual feasibility or dual optimality.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 11, Eqs. (30)–(31); governing model pp. 2–4, utilities and L p. 7

import Mathlib
import Definitions.Def_NonlinSSD_Optimality_Basic

namespace NonlinSSD.DualFunctional.Supplement

open MeasureTheory
open NonlinSSD.Optimality

variable {Ω 𝒵 : Type*} [MeasurableSpace Ω]
    [AddCommGroup 𝒵] [Module ℝ 𝒵] [TopologicalSpace 𝒵]
    [IsTopologicalAddGroup 𝒵] [ContinuousSMul ℝ 𝒵]
    [LocallyConvexSpace ℝ 𝒵] [T2Space 𝒵]
    [TopologicalSpace.SeparableSpace 𝒵]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}

/-- Equation (30), p. 11: the total dual functional, as an extended-real supremum
of the published Lagrangian over Z and the entire integrable split-vector space.
For admissible utilities and essentially bounded multipliers every integrand is
integrable. No dominance or splitting constraint is imposed in this supremum.
Empty Z gives bottom; an unbounded-above set of Lagrangian values gives top. -/
noncomputable def totalDual (pr : Problem Ω 𝒵 P m)
    (u : Fin m → ℝ → ℝ) (θ : Fin m → Ω → ℝ) : EReal :=
  ⨆ (z : 𝒵) (_ : z ∈ pr.Z) (X : Fin m → Ω → ℝ)
    (_ : ∀ i, Integrable (X i) P), ((pr.L z X u θ : ℝ) : EReal)

/-- Feasible multipliers in (31), p. 11: utility membership and nonnegative
L-infinity multipliers. This contains no primal condition or value equality. -/
def DualFeasible (pr : Problem Ω 𝒵 P m)
    (u : Fin m → ℝ → ℝ) (θ : Fin m → Ω → ℝ) : Prop :=
  pr.UtilityAdmissible u ∧ pr.MultiplierAdmissible θ

/-- An attained minimum in (31). Extended values remain allowed in the definition;
finiteness at a dual optimum is a conclusion of Theorem 3 when a primal optimum exists. -/
def IsDualOptimal (pr : Problem Ω 𝒵 P m)
    (u : Fin m → ℝ → ℝ) (θ : Fin m → Ω → ℝ) : Prop :=
  DualFeasible pr u θ ∧
  ∀ (v : Fin m → ℝ → ℝ) (ζ : Fin m → Ω → ℝ),
    DualFeasible pr v ζ → totalDual pr u θ ≤ totalDual pr v ζ

end NonlinSSD.DualFunctional.Supplement


