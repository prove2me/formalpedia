-- Prove2me | Definitions.Def_RandPurIso_Completion_IsContraction
-- name    : RandPurIso_Completion_IsContraction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:11.300779+00:00
-- url     : https://prove2.me/theorems/4712d808-10a0-45a4-abef-d34fc921be1b
-- title:
--   Contractions, projectors and partial isometries (Definition 3.3)
-- statement:
--   For a linear map $V:A\to B$:
--
--   1. $V$ is a **contraction** if $V^\dagger V\preceq I_A$;
--   2. (for $B=A$) $V$ is a **projector** if $V=V^\dagger$ and $V^2=V$;
--   3. $V$ is a **partial isometry** if $V^\dagger V$ is an orthogonal projector.
--
--   These are the classes of maps that enter the oracle constructions of the paper through the channel $\Phi_V$ of Definition 3.4.
--
--   **Formalization Note** $V^\dagger V\preceq I$ is positive semidefiniteness of $I-V^\dagger V$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 3.3, p. 18

import Mathlib
open Matrix
open scoped ComplexOrder

namespace RandPurIso.Completion

/-- **Contraction** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.3, p. 18): `V†V ⪯ I_A`. -/
def IsContraction {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] (K : Matrix Y X ℂ) : Prop :=
  (1 - Kᴴ * K).PosSemidef

/-- **Projector** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.3, p. 18): `V = V†` and `V² = V`. -/
def IsProjector {X : Type} [Fintype X] (P : Matrix X X ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- **Partial isometry** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.3, p. 18): `V†V` is an orthogonal projector. -/
def IsPartialIsometry {X Y : Type} [Fintype X] [Fintype Y] (K : Matrix Y X ℂ) : Prop :=
  IsProjector (Kᴴ * K)

end RandPurIso.Completion


