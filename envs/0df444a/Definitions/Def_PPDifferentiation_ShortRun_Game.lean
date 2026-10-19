-- Prove2me | Definitions.Def_PPDifferentiation_ShortRun_Game
-- name    : PPDifferentiation_ShortRun_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T12:57:59.861226+00:00
-- url     : https://prove2.me/theorems/00930245-709a-4865-89bb-e5d11acb3a91
-- title:
--   §6 and Proposition 5 — PP choices and pure Nash equilibrium
-- statement:
--   At stage 1 each firm chooses either personalized pricing (PP) or uniform pricing (U). For any two-player game with real payoffs $u_A(a,b)$ and $u_B(a,b)$, the action pair $(a,b)$ is a pure Nash equilibrium when
--
--   $$
--   u_A(a',b)\le u_A(a,b)\quad\text{for every }a',\qquad u_B(a,b')\le u_B(a,b)\quad\text{for every }b'.
--   $$
--
--   This reusable equilibrium predicate represents the simultaneous implementation decisions in Section 6. There are exactly two PP choices; no mixed strategies are included.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), §6, p. 23, first-stage PP decisions; p. 25, Proposition 5

import Mathlib

namespace PPDifferentiation.ShortRun

/-- The two available actions at the implementation stage. -/
inductive PPChoice where
  | PP
  | U
deriving DecidableEq

/-- Pure Nash equilibrium in a two-player normal-form game. -/
def IsPureNE {α β : Type} (uA uB : α → β → ℝ) (a : α) (b : β) : Prop :=
  (∀ a', uA a' b ≤ uA a b) ∧ (∀ b', uB a b' ≤ uB a b)

end PPDifferentiation.ShortRun


