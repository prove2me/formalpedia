-- Prove2me | Definitions.Def_OnlineThreeColorBounds_LowerBound_Construction
-- name    : OnlineThreeColorBounds_LowerBound_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:45.106786+00:00
-- url     : https://prove2.me/theorems/3a61ae51-f60a-4097-9c05-3ccea03c05bc
-- title:
--   Adaptive graph constructions, legal outcomes, and forcing
-- statement:
--   An adaptive construction either stops or reveals the earlier neighbors of a new vertex, then chooses its continuation after observing that vertex's online color set. A construction is an actual well-founded tree with a branch for every finite color set, without a fixed finite palette. Interaction with a rule retains all earlier edges and outputs.
--
--   The predicate $\operatorname{AllOutcomes}_t(S,h,P)$ checks that every revelation in construction $S$ refers only to already arrived vertices, and that every terminal history reachable by legal $t$-element responses satisfies $P$. A construction with budgets $N,D$ and offline color bound $k$ satisfies, on every legal completed play $h$,
--   $$
--   |h|\le N,\qquad \chi(G_h)\le k,\qquad \deg_h^+(v)\le D\quad(v\in V(G_h)).
--   $$
--   It forces $K$ colors when every deterministic rule proper on the promised $k$-colorable inputs uses at least $K$ distinct color names in its interaction. Bipartite constructions instead carry a real size bound and admit a covering bipartition on every legal play. The sides are offline witnesses, not part of a rule's input.
--
--   These predicates express the input and output guarantees of simulation. They do not postulate a winning strategy: existence of such a tree remains a theorem conclusion. Earlier-neighbor legality is checked before branching, and fresh colors always furnish legal responses, preventing an empty-play interpretation.
--
--   Differences from the source:
--   - encoding: adaptive finite graph constructions with size and post-degree bounds → well-founded response-branching trees and an AllOutcomes predicate over every exact-size proper response; reason: bounded finite plays have such a tree, with arbitrary finite-set branching; resource certificates are verified predicates rather than assumed fields
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a, §2.1–2.2 and Lemma 2.5 proof, printed pp. 5–9 / PDF pp. 6–10

import Definitions.Def_OnlineThreeColorBounds_LowerBound_OnlineAlgorithm
set_option autoImplicit false

namespace OnlineThreeColorBounds.LowerBound

/-- An adaptive adversary: stop, or reveal earlier neighbors and branch on the response.
The branching type has every finite subset of the unbounded natural palette. -/
inductive Construction where
  | stop : Construction
  | present (s : Finset ℕ) (next : Finset ℕ → Construction) : Construction

/-- Actual interaction, without passing the tree or a coloring certificate to the rule. -/
def play (A : OnlineRule) : Construction → History → History
  | .stop, h => h
  | .present s next, h =>
      let x := A h s
      play A (next x) (h ++ [(s, x)])

/-- Check legal revelation and the terminal predicate on every legal response branch.
The earlier-neighbor condition is checked before taking a response, so an invalid
revelation cannot make this predicate vacuous. Every finite history admits fresh colors. -/
def AllOutcomes (t : ℕ) : Construction → History → (History → Prop) → Prop
  | .stop, h, P => P h
  | .present s next, h, P =>
      s ⊆ Finset.range h.length ∧ ∀ x : Finset ℕ, LegalResponse t h s x →
        AllOutcomes t (next x) (h ++ [(s, x)]) P

/-- Size and offline bipartiteness are uniform across every legal play. -/
def BipartiteConstruction (t : ℕ) (N : ℝ) (S : Construction) : Prop :=
  AllOutcomes t S [] (fun h => (h.length : ℝ) ≤ N ∧
    ∃ s r : Finset (Fin h.length), CoveringBipartition (historyGraph h) s r)

/-- Integer size and future-degree budgets, and offline k-colorability, on all plays. -/
def BoundedConstruction (t k N D : ℕ) (S : Construction) : Prop :=
  AllOutcomes t S [] (fun h => h.length ≤ N ∧ (historyGraph h).Colorable k ∧
    ∀ v : Fin h.length, postDegree h v ≤ D)

/-- Forcing is tested against every deterministic rule proper on the promised graph class. -/
def Forces (t k K : ℕ) (S : Construction) : Prop :=
  ∀ A : OnlineRule, ProperOn t k A → K ≤ colorCount (play A S [])

end OnlineThreeColorBounds.LowerBound


