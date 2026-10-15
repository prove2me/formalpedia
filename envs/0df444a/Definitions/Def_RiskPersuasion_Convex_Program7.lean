-- Prove2me | Definitions.Def_RiskPersuasion_Convex_Program7
-- name    : RiskPersuasion_Convex_Program7
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:14.979113+00:00
-- url     : https://prove2.me/theorems/80ee0ff3-b32d-4d05-8411-f1fc3986a3d5
-- title:
--   The convex program (7) and the target t* of Theorem 2 (pp. 17, 21)
-- statement:
--   Let $\Omega$ be finite, $A$ finite, $\mu^* \in \Delta(\Omega)$ the prior, $P_a \subseteq \Delta(\Omega)$ the sets of Eq. (1), and $v$ the sender's utility. The convex program (7) of the paper is
--   $$\max_{\{t_a : a \in A\}} \ \sum_{\omega \in \Omega} \sum_{a \in A} t_a(\omega)\, v(\omega,a) \quad \text{s.t.} \quad \sum_{a \in A} t_a(\omega) = \mu^*(\omega)\ \ (\omega \in \Omega), \qquad t_a \in \operatorname{Conv}(P_a \cup \{0\})\ \ (a \in A),$$
--   where $\operatorname{Conv}$ is the set of finite convex combinations and $0 \in \mathbb{R}^{\Omega}$ is the zero vector. This file defines feasibility for (7) and its objective.
--
--   It also defines, for Theorem 2, the vector $t^*_a(\omega) = \mu^*(\omega)\, \mathbb{1}\{\omega \in \Upsilon_a\}$, where $\Upsilon_a$ is the set of states at which action $a$ is sender-optimal.
--
--   The variable $t_a(\omega)$ is the joint probability that the state is $\omega$ and the receiver takes action $a$.
--
--   **Formalization Note** $t$ is a function $A \to (\Omega \to \mathbb{R})$ and $\operatorname{Conv}$ is Mathlib's `convexHull ℝ`.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 17, program (7); p. 21, definition of t*_a

import Mathlib
import Definitions.Def_RiskPersuasion_Convex_Receiver

namespace RiskPersuasion.Convex

/-- Feasibility for the convex program (7): `∑_a t_a(ω) = μstar(ω)` for each `ω`, and
`t_a ∈ Conv(P_a ∪ {0})` for each action `a`, where `0` is the zero vector of `ℝ^Ω`. -/
def Feasible7 {Ω A : Type} [Fintype Ω] [Fintype A] (μstar : Ω → ℝ) (ρ : (Ω → ℝ) → A → ℝ)
    (t : A → Ω → ℝ) : Prop :=
  (∀ ω : Ω, ∑ a, t a ω = μstar ω) ∧ ∀ a : A, t a ∈ convexHull ℝ (P ρ a ∪ {0})

/-- The objective of program (7): `∑_ω ∑_a t_a(ω) v(ω, a)`. -/
def objective7 {Ω A : Type} [Fintype Ω] [Fintype A] (v : Ω → A → ℝ) (t : A → Ω → ℝ) : ℝ :=
  ∑ ω, ∑ a, t a ω * v ω a

/-- `t*_a(ω) = μstar(ω) · 1{ω ∈ Υ_a}`. -/
noncomputable def tstar {Ω A : Type} (μstar : Ω → ℝ) (v : Ω → A → ℝ) (a : A) : Ω → ℝ :=
  (Upsilon v a).indicator μstar

end RiskPersuasion.Convex


