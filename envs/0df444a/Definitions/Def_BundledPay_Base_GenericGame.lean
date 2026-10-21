-- Prove2me | Definitions.Def_BundledPay_Base_GenericGame
-- name    : BundledPay_Base_GenericGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:13.349346+00:00
-- url     : https://prove2.me/theorems/fb9e81c7-04ea-4894-98c6-f3406e46357c
-- title:
--   Pure Nash and two-stage subgame-perfect equilibrium
-- statement:
--   For two feasible strategy sets $A$ and $B$ and real-valued payoffs $u$ and $v$, a pure Nash equilibrium $(x,y)$ satisfies
--
--   $$x\in A,\quad y\in B,\quad u(x',y)\le u(x,y)\ (x'\in A),\quad v(x,y')\le v(x,y)\ (y'\in B).$$
--
--   For a two-stage game, a pure subgame-perfect equilibrium consists of a feasible leader choice $a$ and a continuation selection $\sigma$. The selection is a Nash equilibrium after every feasible leader choice, and $a$ maximizes the leader's payoff among all feasible choices under that selection.
--
--   This generic interface is used for the hospital–physician effort game and its gainsharing stage.
-- source:
--   Vlachy, Ayer, Ayvaci & Raghunathan, The Business of Healthcare: The Role of Physician Integration in Bundled Payments, SSRN preprint 3539596, pp. 13–14, §4.2, two-stage game description

import Mathlib

namespace BundledPay.Base

/-- Pure Nash equilibrium of a two-player game with feasible strategy sets. -/
def IsNash {α β : Type} (A : Set α) (B : Set β)
    (u : α → β → ℝ) (v : α → β → ℝ) (x : α) (y : β) : Prop :=
  x ∈ A ∧ y ∈ B ∧
    (∀ x' ∈ A, u x' y ≤ u x y) ∧
    (∀ y' ∈ B, v x y' ≤ v x y)

/-- Subgame-perfect equilibrium of a two-stage pure-strategy game. -/
def IsTwoStageSPNE {α β γ : Type} (A : Set α)
    (stageNash : α → β → γ → Prop) (leaderPayoff : α → β → γ → ℝ)
    (σ : α → β × γ) (a : α) : Prop :=
  a ∈ A ∧
    (∀ a' ∈ A, stageNash a' (σ a').1 (σ a').2) ∧
    (∀ a' ∈ A, leaderPayoff a' (σ a').1 (σ a').2 ≤
      leaderPayoff a (σ a).1 (σ a).2)

end BundledPay.Base


