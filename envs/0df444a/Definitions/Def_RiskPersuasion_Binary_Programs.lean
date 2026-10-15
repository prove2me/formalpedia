-- Prove2me | Definitions.Def_RiskPersuasion_Binary_Programs
-- name    : RiskPersuasion_Binary_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:41.608982+00:00
-- url     : https://prove2.me/theorems/1f55d4e0-22ab-4c0e-ba76-b0d5330ad1a6
-- title:
--   The sender's convex program (7) and the linear program (10) for binary persuasion (pp. 17, 24)
-- statement:
--   The two optimization problems compared in Theorem 3, for the binary model with prior $\mu^*\in\Delta(\Omega)$ and sender utility $v(\omega,a)$.
--
--   A candidate solution is a pair $t=(t_0,t_1)$ of vectors in $\mathbb R^{\Omega}$; $t_a(\omega)$ is the joint probability that the state is $\omega$ and the receiver takes action $a$. Both programs maximize the sender's expected utility
--   $$\sum_{\omega\in\Omega}\sum_{a\in\{0,1\}} t_a(\omega)\,v(\omega,a)=\sum_{\omega\in\Omega}v(\omega,1)\,t_1(\omega)+v(\omega,0)\,t_0(\omega).$$
--
--   1. **Program (7)** (p. 17): $t$ is feasible when $t_0(\omega)+t_1(\omega)=\mu^*(\omega)$ for each $\omega\in\Omega$ and $t_a\in\operatorname{Conv}(P_a\cup\{0\})$ for each $a\in\{0,1\}$, where $0$ is the zero vector of $\mathbb R^{\Omega}$ and $\operatorname{Conv}$ is the set of finite convex combinations.
--   2. **Program (10)** (p. 24): $t$ is feasible when
--   $$t_1\in\operatorname{Conv}(K_1\cup K_{01}\cup\{0\}),\qquad t_0\in\operatorname{Conv}(L_0\cup\{0\}),\qquad t_0(\omega)+t_1(\omega)=\mu^*(\omega)\ \text{ for each }\omega\in\Omega,$$
--   with states identified with their point masses $e_\omega$.
--
--   Program (7) is the paper's general reformulation of the persuasion problem (Theorem 1), specialized to two actions; program (10) has a polytope as feasible region and is a linear program.
--
--   **Formalization Note** A pair $t$ is a function `Fin 2 → Ω → ℝ`; `objective v t` is the double sum above in the form of (7). Feasibility of each program is a predicate (`Feasible7`, `Feasible10`), and the comparison of the programs is stated through feasibility and objective values, never through a supremum.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 17 (program (7)), p. 24 (program (10))

import Mathlib
import Definitions.Def_RiskPersuasion_Binary_Model

namespace RiskPersuasion.Binary

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The sender's objective of programs (7) and (10) (pp. 17, 24) for `A = {0, 1}`:
`∑_{ω ∈ Ω} ∑_{a ∈ A} t_a(ω) v(ω, a)`, where `t a : ℝ^Ω` is the variable `t_a`. -/
def objective (v : Ω → Fin 2 → ℝ) (t : Fin 2 → Ω → ℝ) : ℝ :=
  ∑ ω, ∑ a, t a ω * v ω a

/-- Feasibility for program (7), p. 17, with `A = {0, 1}`: `∑_a t_a(ω) = μ*(ω)` for each `ω`, and
`t_a ∈ Conv(P_a ∪ {0})` for each `a`, where `0` is the zero vector of `ℝ^Ω`. -/
def Feasible7 (ρ : (Ω → ℝ) → Fin 2 → ℝ) (μstar : Ω → ℝ) (t : Fin 2 → Ω → ℝ) : Prop :=
  (∀ ω, ∑ a, t a ω = μstar ω) ∧ ∀ a : Fin 2, t a ∈ convexHull ℝ (P ρ a ∪ {0})

/-- Feasibility for the linear program (10), p. 24: `t₁ ∈ Conv(K₁ ∪ K₀₁ ∪ {0})`,
`t₀ ∈ Conv(L₀ ∪ {0})` and `t₀(ω) + t₁(ω) = μ*(ω)` for each `ω`; states are identified with
their point masses `e_ω`. -/
def Feasible10 (ρ : (Ω → ℝ) → Fin 2 → ℝ) (μstar : Ω → ℝ) (t : Fin 2 → Ω → ℝ) : Prop :=
  t 1 ∈ convexHull ℝ (e '' K1 ρ ∪ K01 ρ ∪ {0}) ∧
    t 0 ∈ convexHull ℝ (e '' L0 ρ ∪ {0}) ∧
    ∀ ω, t 0 ω + t 1 ω = μstar ω

end RiskPersuasion.Binary


