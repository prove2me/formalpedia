-- Prove2me | Definitions.Def_TeamDelegation_Optimal_FiniteGame
-- name    : TeamDelegation_Optimal_FiniteGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:49.999995+00:00
-- url     : https://prove2.me/theorems/7e9a7798-90b0-4063-8b37-04f67e24a448
-- title:
--   Finite two-player stage game and mixed Nash equilibrium
-- statement:
--   A finite two-player stage game has finite action sets $A$ and $B$, a specified feasible subset for each player, and real payoff functions $u_A,u_B:A\times B\to\mathbb R$. An independent mixed profile consists of one probability distribution on each feasible action set. It is a Nash equilibrium when neither player can gain by changing unilaterally to any feasible pure action:
--
--   $$
--   \mathbb E_{\sigma}[u_i]\ge \mathbb E_{\sigma_{-i}}[u_i(a_i,\cdot)]
--   \quad\text{for every feasible }a_i,\ i\in\{A,B\}.
--   $$
--
--   The definition supplies the reusable normal-form game interface used for both centralised and delegated stage games. Zero probability is required on infeasible actions; mixed strategies include pure strategies as point masses.
--
--   **Formalization Note** This is a finite representation of the stage games displayed in Figures 1–3; it does not impose the paper's production parameters by itself.
-- source:
--   Upton, Implicit Incentives and Delegation in Teams, TRR 266 Working Paper No. 67 (SSRN 3991736, 17 Dec 2021), p. 10 (PDF 11), §3, Figures 1–3

import Mathlib

namespace TeamDelegation.Optimal

/-- A finite two-player normal-form game with permitted pure actions and real payoffs. -/
structure FiniteGame (A B : Type) where
  feasibleA : A → Prop
  feasibleB : B → Prop
  payoffA : A → B → ℝ
  payoffB : A → B → ℝ

/-- Independent mixed actions for the two players. -/
structure Mixed (A B : Type) where
  σA : A → ℝ
  σB : B → ℝ

/-- Probability and action-feasibility conditions for independent mixed actions. -/
def Mixed.IsValid {A B : Type} [Fintype A] [Fintype B]
    (G : FiniteGame A B) (σ : Mixed A B) : Prop :=
  (∀ a, 0 ≤ σ.σA a) ∧ (∀ b, 0 ≤ σ.σB b) ∧
  (∑ a, σ.σA a) = 1 ∧ (∑ b, σ.σB b) = 1 ∧
  (∀ a, ¬ G.feasibleA a → σ.σA a = 0) ∧
  (∀ b, ¬ G.feasibleB b → σ.σB b = 0)

/-- The first player's payoff under independent mixed actions. -/
def FiniteGame.expPayA {A B : Type} [Fintype A] [Fintype B]
    (G : FiniteGame A B) (σ : Mixed A B) : ℝ :=
  ∑ a, ∑ b, σ.σA a * σ.σB b * G.payoffA a b

/-- The second player's payoff under independent mixed actions. -/
def FiniteGame.expPayB {A B : Type} [Fintype A] [Fintype B]
    (G : FiniteGame A B) (σ : Mixed A B) : ℝ :=
  ∑ a, ∑ b, σ.σA a * σ.σB b * G.payoffB a b

/-- Nash equilibrium, checking every feasible pure deviation against the mixed profile. -/
def FiniteGame.IsNash {A B : Type} [Fintype A] [Fintype B]
    (G : FiniteGame A B) (σ : Mixed A B) : Prop :=
  σ.IsValid G ∧
  (∀ a, G.feasibleA a → (∑ b, σ.σB b * G.payoffA a b) ≤ G.expPayA σ) ∧
  (∀ b, G.feasibleB b → (∑ a, σ.σA a * G.payoffB a b) ≤ G.expPayB σ)

end TeamDelegation.Optimal


