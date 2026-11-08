-- Prove2me | Definitions.Def_SkewMatching_matchingGraph
-- name    : SkewMatching_matchingGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:41.825885+00:00
-- url     : https://prove2.me/theorems/c2ef6ec0-e060-42e9-8180-ef2a464db5e8
-- title:
--   Definition 5 — the matching graph
-- statement:
--   For a graph $G$ on the vertex set $V$, the **matching graph** $M_G$ is the skew-symmetric graph with:
--
--   1. a vertex $v$ and a symmetric counterpart $v'$ for each $v\in V$;
--   2. an edge $(u,v')$ with symmetric edge $(v,u')$ for each edge $\{u,v\}$ of $G$;
--   3. a source $s$ with counterpart $s'$, and for every $v\in V$ an edge $(s,v)$ with symmetric edge $(v',s')$.
--
--   All edges have capacity $1$. This is the reduction of general matching to integral symmetric flow.
--
--   **Formalization Note** The vertex type is `Option V × Bool`. Because $G$ is a `SimpleGraph` it has no loops; a loop would give a self-symmetric edge, which Definition 3 forbids.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Definition 5, p.3

import Mathlib
import Definitions.Def_SkewMatching_SkewGraph

namespace SkewMatching

/-- The edge type of the matching graph `M_G`: `inl (u, v)` is the edge `(u, v′)` for an ordered adjacent pair; `inr (v, false)`
is `(s, v)` and `inr (v, true)` is `(v′, s′)`. -/
abbrev MatchEdge {V : Type*} (G : SimpleGraph V) : Type _ :=
  {p : V × V // G.Adj p.1 p.2} ⊕ (V × Bool)

/-- The source vertex `s` of `M_G`. The vertex type is `Option V × Bool`: `(some v, false)` is `v`, `(some v, true)` is `v′`,
`(none, false)` is `s` and `(none, true)` is `s′`. -/
def matchingSource (V : Type*) : Option V × Bool := (none, false)

/-- **Definition 5**, p.3: the matching graph `M_G`. Each vertex `v` has a symmetric counterpart `v′`. Each edge `{u, v}` gives the
edge `(u, v′)` with symmetric edge `(v, u′)`. A source `s` with counterpart `s′` is added, with edges `(s, v)` and `(v′, s′)`.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Definition 5,
p.3.

**Formalization Note.** `SimpleGraph` is loopless, which `σ(e) ≠ e` needs: a loop `{u, u}` would give a self-symmetric edge `(u, u′)`. -/
def matchingGraph {V : Type*} (G : SimpleGraph V) : SkewGraph (Option V × Bool) (MatchEdge G) where
  tail
    | .inl p => (some p.1.1, false)
    | .inr (v, false) => (none, false)
    | .inr (v, true) => (some v, true)
  head
    | .inl p => (some p.1.2, true)
    | .inr (v, false) => (some v, false)
    | .inr (v, true) => (none, true)
  σV x := (x.1, !x.2)
  σE
    | .inl p => .inl ⟨(p.1.2, p.1.1), p.2.symm⟩
    | .inr (v, b) => .inr (v, !b)
  σV_invol := fun x => by simp
  σV_ne := fun x h => by
    have := congrArg Prod.snd h
    simp at this
  σE_invol := fun e => by
    rcases e with p | ⟨v, b⟩ <;> simp
  σE_ne := fun e h => by
    rcases e with p | ⟨v, b⟩
    · have h1 : (p.1.2, p.1.1) = p.1 := congrArg Subtype.val (Sum.inl.inj h)
      exact p.2.ne (congrArg Prod.fst h1).symm
    · simp at h
  tail_σE := fun e => by
    rcases e with p | ⟨v, b⟩
    · rfl
    · cases b <;> rfl
  head_σE := fun e => by
    rcases e with p | ⟨v, b⟩
    · rfl
    · cases b <;> rfl

noncomputable instance {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype (MatchEdge G) := by
  classical exact inferInstance

end SkewMatching


