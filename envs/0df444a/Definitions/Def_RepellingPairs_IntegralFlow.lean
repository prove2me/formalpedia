-- Prove2me | Definitions.Def_RepellingPairs_IntegralFlow
-- name    : RepellingPairs_IntegralFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:05:23.621616+00:00
-- url     : https://prove2.me/theorems/4856164b-954a-4fcb-b112-bf3a8e54799d
-- title:
--   Integral flows and Properties 2–5
-- statement:
--   An **integral flow** $F$ is a multiset of terminal pairs, each unit sent along its designated path. An integral flow $F'$ is a multiset of terminal paths, trivial paths allowed. Each gives a configuration, with one chord per unit, a cost, and a load on each edge. The properties of §3 are:
--
--   1. **Property 2** (with $\le$): the load of $F'$ on each edge is at most the load of $F$ on it.
--   2. **Property 3**: $\sum_F D<\sum_{F'}D$.
--   3. **Property 4**: at each terminal, $F$ and $F'$ have the same number of unit ends, a trivial path counting twice.
--   4. **Property 5**: for terminals $s,s',t',t$ occurring in this order with $F_{s,s'},F_{t,t'}>0$, the paths $P_{s,s'}$ and $P_{t,t'}$ are disjoint.
--
--   Property 1 of the page is built in, since $F$ uses only designated paths. Also defined: $F$ has **no trivial pair** if no unit of $F$ is on a pair $(t,t)$.
--
--   **Formalization Note** Units of $F$ are stored as ordered pairs, and $P_{i,j}$ and $P_{j,i}$ use the same edges. Property 2 is printed with "greater than", which Farkas' lemma does not give; see the correction on the Farkas alternative.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §3, pp.7–10

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_TerminalPath
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_CyclicallyOrdered

set_option autoImplicit false

namespace RepellingPairs

universe u v

/-- An integral flow `F` of §3: a multiset of terminal pairs, each unit sent along the designated path of
its pair (Property 1, p.7; "F, F′ are collections of paths", p.8). Chen, Pylyavskyy, Tan,
arXiv:2607.02883 (version of October 23, 2026), §3, pp.7–9.

**Formalization Note.** Units are stored as ordered pairs; `P i j` and `P j i` use the same edges, and the
chord of a unit is unordered. -/
abbrev DesignatedFlow (k : ℕ) : Type := Multiset (Fin k × Fin k)

/-- An integral flow `F′`: a multiset of terminal paths, trivial paths allowed. -/
abbrev PathFlow {V : Type u} {E : Type v} {k : ℕ} (G : OSInstance V E k) : Type (max u v) :=
  Multiset (TerminalPath G)

variable {V : Type u} {E : Type v} {k : ℕ} {G : OSInstance V E k}

/-- The configuration `C` of `F`: one chord `(t, t′)` per unit (p.10). -/
def DesignatedFlow.chords (F : DesignatedFlow k) : Config k := F.map fun p => s(p.1, p.2)

/-- The configuration `C′` of `F′`: one chord per path, joining its two ends (p.10). -/
def PathFlow.chords (F' : PathFlow G) : Config k := F'.map fun q => s(q.src, q.tgt)

/-- The cost `∑_{t,t′} F_{t,t′} D(t,t′)`, each unit counted once. -/
def DesignatedFlow.cost (D : Fin k → Fin k → ℝ) (F : DesignatedFlow k) : ℝ :=
  (F.map fun p => D p.1 p.2).sum

/-- The cost `∑_{t,t′} F′_{t,t′} D(t,t′)`, each path counted once. -/
def PathFlow.cost (D : Fin k → Fin k → ℝ) (F' : PathFlow G) : ℝ :=
  (F'.map fun q => D q.src q.tgt).sum

/-- Number of units of `F` through the edge `e`. -/
def DesignatedFlow.load [DecidableEq E] (P : PathStructure G) (F : DesignatedFlow k) (e : E) : ℕ :=
  (F.map fun p => (P.path p.1 p.2).1.edges.count e).sum

/-- Number of paths of `F′` through the edge `e`. -/
def PathFlow.load [DecidableEq E] (F' : PathFlow G) (e : E) : ℕ :=
  (F'.map fun q => q.path.1.edges.count e).sum

/-- Property 2 (corrected to `≤`, p.7): for each edge, the amount of `F′` through it is at most the amount
of `F` through it. -/
def Property2 [DecidableEq E] (P : PathStructure G) (F : DesignatedFlow k) (F' : PathFlow G) : Prop :=
  ∀ e, F'.load e ≤ F.load P e

/-- Property 3 (p.8): `∑ F D < ∑ F′ D`. -/
def Property3 (D : Fin k → Fin k → ℝ) (F : DesignatedFlow k) (F' : PathFlow G) : Prop :=
  DesignatedFlow.cost D F < PathFlow.cost D F'

/-- Property 4 (p.8), for an undirected metric: at each terminal `F` and `F′` have the same number of unit
ends, a trivial path counting twice. -/
def Property4 (F : DesignatedFlow k) (F' : PathFlow G) : Prop :=
  ∀ t, Config.deg (DesignatedFlow.chords F) t = Config.deg (PathFlow.chords F') t

/-- Property 5 (p.9): for terminals `s, s′, t′, t` on the boundary in this order with `F_{s,s′}, F_{t,t′} > 0`,
the designated paths `P s s′` and `P t t′` are disjoint. -/
def Property5 (P : PathStructure G) (F : DesignatedFlow k) : Prop :=
  ∀ s s' t' t, CyclicallyOrdered s s' t' t →
    s(s, s') ∈ DesignatedFlow.chords F → s(t, t') ∈ DesignatedFlow.chords F →
    (P.path s s').1.VertexDisjoint (P.path t t').1

/-- `F` has no unit on a trivial pair `(t, t)`. -/
def NoTrivialPair (F : DesignatedFlow k) : Prop := ∀ p ∈ F, p.1 ≠ p.2

end RepellingPairs


