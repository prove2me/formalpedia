-- Prove2me | Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting
-- name    : FordFulkerson56_MinCut_IsDisconnecting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:31:39.347993+00:00
-- url     : https://prove2.me/theorems/f79d2727-2b36-4d59-b62c-6017034c0328
-- title:
--   Disconnecting sets, cuts and their value v(D)
-- statement:
--   Let $N$ be a network with source $a$, sink $b$ and capacities $c$ (Ford–Fulkerson, p. 400).
--
--   1. A set $D$ of arcs is a **disconnecting set** if every chain joining $a$ and $b$ meets $D$.
--   2. A disconnecting set no proper subset of which is disconnecting is a **cut**.
--   3. The **value** of a set of arcs $D$ is
--   $$v(D)=\sum_{e\in D} c(e).$$
--
--   The minimum of $v(D)$ over disconnecting sets is the right-hand side of the minimal cut theorem.
--
--   **Formalization Note** "Meets" is read as a nonempty intersection of the two finite sets of arcs. The chains quantified over are exactly those of the chain definition (self-avoiding, possibly traversing arcs in either direction).
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 400, §1, definitions of disconnecting set, cut and value v(D)

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain

namespace FordFulkerson56.MinCut

variable {V E : Type*} [DecidableEq E]

/-- A disconnecting set (Ford–Fulkerson, p. 400): a set of arcs meeting every chain joining the
source and the sink. -/
def IsDisconnecting (N : Network V E) (D : Finset E) : Prop :=
  ∀ C, IsChain N N.source N.sink C → (C ∩ D).Nonempty

/-- A cut (p. 400): a disconnecting set no proper subset of which is disconnecting. -/
def IsCut (N : Network V E) (D : Finset E) : Prop :=
  IsDisconnecting N D ∧ ∀ D' ⊂ D, ¬ IsDisconnecting N D'

/-- The value `v(D)` of a set of arcs: the sum of the capacities of its members (p. 400). -/
def cutValue (N : Network V E) (D : Finset E) : ℝ :=
  ∑ e ∈ D, N.cap e

end FordFulkerson56.MinCut


