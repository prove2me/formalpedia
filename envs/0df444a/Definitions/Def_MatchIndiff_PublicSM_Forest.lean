-- Prove2me | Definitions.Def_MatchIndiff_PublicSM_Forest
-- name    : MatchIndiff_PublicSM_Forest
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:24:56.627181+00:00
-- url     : https://prove2.me/theorems/2f9c2ba9-e878-4a93-a84b-eaec1feaa2d6
-- title:
--   Improving cycles, ordered increasing forests (App. A.5) and the lexicographically first perfect matching (§D.7)
-- statement:
--   **Improving cycles (p. 26).** Take a loop-free directed graph on a publicly ordered vertex set with a marked subset of its arcs. A directed cycle is *improving* if the outgoing arc on the cycle from its earliest vertex is marked.
--
--   **Ordered increasing forests (p. 27).** An ordered forest gives each vertex a parent (or none: a root) and a position among its siblings; roots are siblings under a virtual super-root. It is *increasing* if sibling positions are distinct and a real parent precedes its child in the vertex order. For incomparable $u,v$ (neither an ancestor of the other) the root paths first enter different sibling branches; $u\lhd_F v$ when the branch containing $u$ precedes the branch containing $v$.
--
--   **Lexicographically first perfect matching (p. 97).** A bipartite graph with $m$ ordered rows and $m$ columns with public identifiers; each row privately knows its allowed columns. Among the perfect matchings, the lexicographically first is the one whose vector of column identifiers (in row order) is lexicographically smallest.
--
--   **Formalization Note.** Vertices are `Fin N` with the public order the index order; arcs `adj` and marks `mk` are relations. A cycle is written from its earliest vertex `v₀` followed by `rest`, with distinct vertices, every vertex of `rest` after `v₀`, consecutive arcs (`List.IsChain`), a closing arc and a marked arc from `v₀` to the head of `rest`. A forest stores `parent : Fin N → Option (Fin N)` and `pos : Fin N → ℕ`; `Anc u v` ($u$ a proper ancestor of $v$) is the transitive closure of the parent relation; `BranchLt u v` asks for distinct siblings $a,b$ (same parent, or both roots) with $a$ an ancestor-or-self of $u$, $b$ of $v$, and `pos a < pos b`. A bipartite graph is `G : Fin m → Fin m → Bool` (row $i$ may use column $j$ iff `G i j`), a perfect matching an injective `π` with `G i (π i)`; `lexFirstPM G` is the lexicographically first one (the identity when there is none, which lies outside every domain where it is used).
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), pp. 26–27 (App. A.5, improving cycle, ordered increasing forest); p. 97 (§D.7, exchange digraph, lexicographically first perfect matching)

import Mathlib

namespace MatchIndiff.PublicSM

/-- An improving cycle (Appendix A.5, p. 26) of a directed graph on the publicly ordered vertex
set `Fin N` with arcs `adj` and marked arcs `mk`, written from its earliest vertex `v₀`: the
vertices `v₀ :: rest` are distinct, every vertex of `rest` comes after `v₀`, consecutive vertices
are joined by arcs, the last vertex has an arc back to `v₀`, and the outgoing cycle arc of `v₀`
(to the first vertex of `rest`) is marked. -/
def IsImprovingCycle {N : ℕ} (adj mk : Fin N → Fin N → Prop) (v₀ : Fin N) (rest : List (Fin N)) :
    Prop :=
  (v₀ :: rest).Nodup ∧ (∀ v ∈ rest, v₀ < v) ∧ List.IsChain adj (v₀ :: rest) ∧
    adj ((v₀ :: rest).getLast (List.cons_ne_nil _ _)) v₀ ∧ ∃ w ∈ rest.head?, mk v₀ w

/-- An ordered forest on the vertex set `Fin N` (p. 27): each vertex has a parent (`none` for a
root) and a position among its siblings (roots are siblings under a virtual super-root). -/
structure OrderedForest (N : ℕ) where
  /-- the parent, `none` for a root -/
  parent : Fin N → Option (Fin N)
  /-- the position among siblings -/
  pos : Fin N → ℕ

/-- The forest is ordered increasing: a real parent precedes its child in the vertex order, and
sibling positions (with the roots as siblings) are distinct. -/
def OrderedForest.IsIncreasing {N : ℕ} (F : OrderedForest N) : Prop :=
  (∀ u v, F.parent v = some u → u < v) ∧
    (∀ u v, F.parent u = F.parent v → F.pos u = F.pos v → u = v)

/-- `u` is a proper ancestor of `v` (equivalently, `v` is a proper descendant of `u`). -/
def OrderedForest.Anc {N : ℕ} (F : OrderedForest N) (u v : Fin N) : Prop :=
  Relation.TransGen (fun a b => F.parent b = some a) u v

/-- `u` is an ancestor of `v` or `u = v`. -/
def OrderedForest.AncEq {N : ℕ} (F : OrderedForest N) (u v : Fin N) : Prop :=
  Relation.ReflTransGen (fun a b => F.parent b = some a) u v

/-- `u` and `v` are incomparable: neither is an ancestor of, or equal to, the other. -/
def OrderedForest.Incomparable {N : ℕ} (F : OrderedForest N) (u v : Fin N) : Prop :=
  ¬ F.AncEq u v ∧ ¬ F.AncEq v u

/-- `u ◁_F v`: at the point where the root paths of `u` and `v` first enter different sibling
branches `a ∋ u`, `b ∋ v` (distinct siblings under a common parent or both roots), the branch of
`u` comes first. -/
def OrderedForest.BranchLt {N : ℕ} (F : OrderedForest N) (u v : Fin N) : Prop :=
  ∃ a b : Fin N, F.parent a = F.parent b ∧ a ≠ b ∧ F.AncEq a u ∧ F.AncEq b v ∧ F.pos a < F.pos b

/-- A perfect matching of the bipartite graph `G` (rows `Fin m`, columns `Fin m`, row `i` allowed
to use column `j` iff `G i j`), given as the injective column choice `π`. -/
def IsPM {m : ℕ} (G : Fin m → Fin m → Bool) (π : Fin m → Fin m) : Prop :=
  Function.Injective π ∧ ∀ i, G i (π i) = true

/-- `π` is the lexicographically first perfect matching of `G`: rows in public order
`0, …, m - 1`, columns compared by their public identifiers `0, …, m - 1`. -/
def IsLexFirstPM {m : ℕ} (G : Fin m → Fin m → Bool) (π : Fin m → Fin m) : Prop :=
  IsPM G π ∧ ∀ π', IsPM G π' → ¬ List.Lex (· < ·) (List.ofFn π') (List.ofFn π)

/-- The lexicographically first perfect matching of `G` (the identity when `G` has no perfect
matching; that case lies outside every domain where it is used). -/
noncomputable def lexFirstPM {m : ℕ} (G : Fin m → Fin m → Bool) : Fin m → Fin m :=
  open Classical in
  if hπ : ∃ π, IsLexFirstPM G π then Classical.choose hπ else id

end MatchIndiff.PublicSM


