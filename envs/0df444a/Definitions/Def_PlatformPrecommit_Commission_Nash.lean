-- Prove2me | Definitions.Def_PlatformPrecommit_Commission_Nash
-- name    : PlatformPrecommit_Commission_Nash
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:52.379326+00:00
-- url     : https://prove2.me/theorems/36724c51-716d-4dc2-87cd-39dfb34c16d4
-- title:
--   Pure Nash equilibrium with admissible unilateral actions
-- statement:
--   A profile is a pure Nash equilibrium of a two-player game when it is admissible and neither player can increase its payoff by replacing its own action with any admissible action while the rival's action stays fixed.
--
--   $$u_i(x[i\leftarrow a])\leq u_i(x)\qquad(i=1,2;\ a\text{ admissible for }i).$$
--
--   This standard game object supplies the unilateral-deviation condition used by both competition modes in the paper.
-- source:
--   Hu, Liu, Precommitments in Two-Sided Market Competition, submitted manuscript (SSRN 3734828; TSpace), pp. 9–10, §3 modes P and C, and p. 12, §3.4

import Mathlib

namespace PlatformPrecommit.Commission

/-- A pure Nash equilibrium for a two-player normal-form game with admissible profiles
and admissible unilateral actions. -/
def IsNash {S A : Type} (payoff : Fin 2 → S → ℝ) (admissible : S → Prop)
    (allowed : Fin 2 → A → Prop) (deviate : S → Fin 2 → A → S) (x : S) : Prop :=
  admissible x ∧ ∀ i a, allowed i a → payoff i (deviate x i a) ≤ payoff i x

end PlatformPrecommit.Commission


