-- Prove2me | Definitions.Def_HellmanLevy_Graphical_IsGraph
-- name    : HellmanLevy_Graphical_IsGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:19.275873+00:00
-- url     : https://prove2.me/theorems/33e5bb05-5d94-4f09-b31b-2c6f56c31d22
-- title:
--   Borel graph of countable degree
-- statement:
--   A relation $G$ on $X$ is a **Borel graph of countable degree** if it is irreflexive ($g\,G\,g$ never holds), symmetric, Borel (its graph is a measurable subset of $X\times X$), and every vertex has countably many neighbours: $N(g)=\{h : g\,G\,h\}$ is countable.
--
--   Its connected-component relation is then a CBER (Definition 3.3).
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §2.4, p.9; §3.2, p.14; Definition 3.3, p.14

import Mathlib
import Definitions.Def_HellmanLevy_CBER_IsBorelRel

namespace HellmanLevy.Graphical

/-- `G` is a **Borel graph of countable degree** on `X`: an irreflexive, symmetric, Borel
relation in which every vertex has countably many neighbours `N(g) = {h | G g h}`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §2.4, p.9 ("A Borel graph G ⊂ Ω × Ω … is an irreflexive and symmetric Borel relation");
§3.2, p.14 ("the degree of G is countable (i.e., for all g ∈ Ω, N(g) is countable)"). -/
def IsGraph {X : Type*} [MeasurableSpace X] (G : X → X → Prop) : Prop :=
  (∀ g, ¬ G g g) ∧ (∀ g h, G g h → G h g) ∧ CBER.IsBorelRel G ∧ ∀ g, {h | G g h}.Countable

end HellmanLevy.Graphical


