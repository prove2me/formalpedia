-- Prove2me | Definitions.Def_RubinsteinBargaining_PEP_EquilibriumSets
-- name    : RubinsteinBargaining_PEP_EquilibriumSets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:41:27.12967+00:00
-- url     : https://prove2.me/theorems/d2f1f9e4-47cc-4f59-ad36-ca1539f9dd38
-- title:
--   Perfect-equilibrium partition sets A and B
-- statement:
--   Let $A$ be the set of player-1 shares induced by finite-agreement perfect equilibria when player 1 makes the first offer. Let $B$ be the corresponding set when player 2 makes the first offer. In both sets, a number $s$ still denotes player 1's share, and an equilibrium with perpetual disagreement contributes no partition.
--
--   These sets are the main objects characterized by the paper's theorem and connected by its first four lemmas.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 103, Section 4, definitions of A and B, https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_PerfectEquilibrium

namespace RubinsteinBargaining.PEP

/-- Player-one shares induced by finite-agreement perfect equilibria with `opener`
making the first proposal. -/
noncomputable def equilibriumPartitions (opener : Player)
    (p : Preferences) : Set ℝ :=
  {x | ∃ (s : Partition) (f g : Strategy) (t : ℕ),
    x = s.val ∧ IsPE opener p f g ∧ play f g = agreement s t}

/-- Perfect-equilibrium partitions when player one opens. -/
noncomputable def A (p : Preferences) : Set ℝ :=
  equilibriumPartitions .one p

/-- Perfect-equilibrium partitions when player two opens; the numbers remain
player one's shares. -/
noncomputable def B (p : Preferences) : Set ℝ :=
  equilibriumPartitions .two p

end RubinsteinBargaining.PEP


