-- Prove2me | Definitions.Def_TurnTables_Reciprocal_BayesGame
-- name    : TurnTables_Reciprocal_BayesGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:07.894982+00:00
-- url     : https://prove2.me/theorems/5ddd163b-1ad7-4789-99f6-7ac745e53ace
-- title:
--   Symmetric binary-action Bayesian game and equilibrium
-- statement:
--   A symmetric two-player Bayesian game with private types in a type space $I$ is represented by its interim payoff $U(\sigma,t,a)$: a player of type $t$ chooses the probability $a$ of its first action, while the other player uses the type-contingent probability function $\sigma$.
--
--   A symmetric Bayesian Nash equilibrium is a feasible profile $\sigma:I\to[0,1]$ for which every type maximizes its own interim payoff:
--
--   $$
--   U(\sigma,t,a)\le U(\sigma,t,\sigma(t))\qquad(t\in I,\;0\le a\le1).
--   $$
--
--   This general game interface keeps the best-response condition separate from the reciprocal-option payoffs. The latter are supplied by the paper-specific model.
-- source:
--   Taneri & Crama, Turning the Tables in R&D Licensing Contracts, SSRN 3711872 (version of October 15, 2020), pp. 21–22, §4.4 (abstract interface for the simultaneous offer game)

import Mathlib

namespace TurnTables.Reciprocal

/-- A symmetric binary-action Bayesian game, given its interim payoff function. -/
structure SymmetricBinaryBayesGame (ι : Type) where
  interim : (ι → ℝ) → ι → ℝ → ℝ

/-- Every type's probability is feasible and maximizes its interim payoff. -/
def SymmetricBinaryBayesGame.IsBNE {ι : Type} (G : SymmetricBinaryBayesGame ι)
    (σ : ι → ℝ) : Prop :=
  (∀ T, 0 ≤ σ T ∧ σ T ≤ 1) ∧
  ∀ T, ∀ a : ℝ, 0 ≤ a → a ≤ 1 → G.interim σ T a ≤ G.interim σ T (σ T)

end TurnTables.Reciprocal


