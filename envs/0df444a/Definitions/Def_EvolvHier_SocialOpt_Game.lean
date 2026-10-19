-- Prove2me | Definitions.Def_EvolvHier_SocialOpt_Game
-- name    : EvolvHier_SocialOpt_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:06.888262+00:00
-- url     : https://prove2.me/theorems/e998880f-e07c-49c3-85f6-0da176f023ce
-- title:
--   Nonnegative-action game and pure Nash equilibrium
-- statement:
--   A **nonnegative-action game** has a set of players, each choosing a nonnegative real action, and an extended-real payoff for each player at every action profile. A **pure Nash equilibrium** is a feasible profile at which no player can improve her payoff by changing her own action to any other nonnegative real number while all other actions stay fixed.
--
--   $$\nu_i(x[i\leftarrow y])\leq \nu_i(x)\qquad\text{for every player }i\text{ and }y\geq0.$$
--
--   This reusable interface expresses the unilateral-deviation quantifier used in the hierarchy model. Extended-real payoffs allow the infinite receipts noted in footnote 8.
-- source:
--   Hougaard, Moreno-Ternero & Østerdal, Optimal Management of Evolving Hierarchies, UPO WP ECON 21.15 (Aug. 3, 2021; Manag. Sci. doi:10.1287/mnsc.2021.4185), §2, pp. 7–10

import Mathlib

namespace EvolvHier.SocialOpt

/-- A normal-form game with a nonnegative real action for each player and
possibly infinite (extended-real) payoffs. -/
structure NonnegativeActionGame (ι : Type) where
  payoff : (ι → ℝ) → ι → EReal

/-- A feasible action profile. -/
def IsNonnegativeProfile {ι : Type} (x : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ x i

/-- Pure Nash equilibrium, with every unilateral nonnegative deviation tested. -/
def NonnegativeActionGame.IsNashEquilibrium {ι : Type} [DecidableEq ι]
    (G : NonnegativeActionGame ι) (x : ι → ℝ) : Prop :=
  IsNonnegativeProfile x ∧
    ∀ i (y : ℝ), 0 ≤ y → G.payoff (Function.update x i y) i ≤ G.payoff x i

end EvolvHier.SocialOpt


