-- Prove2me | Definitions.Def_HardCoreLocalSampling_Local_Pinning
-- name    : HardCoreLocalSampling_Local_Pinning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:44.82364+00:00
-- url     : https://prove2.me/theorems/09933b8b-9579-42ae-a933-3beb04dd99ea
-- title:
--   Tri-state vertex pinnings
-- statement:
--   Let $V$ be a vertex type. Each vertex is assigned one of three states: occupied, unoccupied, or unpinned. A finite set $I\subseteq V$ agrees with the pinning $\xi$ when every occupied pin belongs to $I$ and every unoccupied pin lies outside $I$. Unpinned vertices impose no constraint.
--
--   $$
--   I\sim\xi\quad\Longleftrightarrow\quad
--   \forall v,\ (\xi(v)=\mathrm{occupied}\Rightarrow v\in I)
--   \ \text{and}\ (\xi(v)=\mathrm{unoccupied}\Rightarrow v\notin I).
--   $$
--
--   This is the data layer for feasible conditioning. Independence and feasibility are separate predicates; the pinning supplies neither a feasibility certificate nor an algorithm that scans the graph.
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, §2, printed p.2 (PDF p.3)

import Mathlib

namespace HardCoreLocalSampling.Local

/-! Tri-state pins from §2 (printed p.2 / PDF p.3) of Thomas Chen,
STOC 2027 submission #462, October 2026. These are data, not an oracle
that verifies feasibility. -/

/-- A pin specifies absence, presence, or no membership constraint. -/
inductive Pin where
  | unoccupied
  | occupied
  | unpinned
  deriving DecidableEq, Repr

/-- A tri-state assignment on vertices. No global verification is built in. -/
abbrev Pinning (V : Type*) := V → Pin

/-- An independent set agrees with a pinning when all specified memberships hold. -/
def Compatible {V : Type*} (pin : Pinning V) (I : Finset V) : Prop :=
  ∀ v, (pin v = .occupied → v ∈ I) ∧ (pin v = .unoccupied → v ∉ I)

end HardCoreLocalSampling.Local


