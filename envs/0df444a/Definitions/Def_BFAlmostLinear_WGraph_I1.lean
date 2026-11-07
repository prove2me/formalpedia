-- Prove2me | Definitions.Def_BFAlmostLinear_WGraph_I1
-- name    : BFAlmostLinear_WGraph_I1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:14.482637+00:00
-- url     : https://prove2.me/theorems/dfc6a99c-4d2c-4409-853c-a54b3d4f92c8
-- title:
--   Invariants (I1)–(I4) on negative arcs and Steiner levels
-- statement:
--   Let $G$ be a weighted graph with frozen flags and let $i:V\to\mathbb N$ assign to each vertex its **level** ($S_0$ holds the original vertices, $S_j$ for $j\ge1$ the Steiner vertices added in iteration $j$).
--
--   1. **(I1)** Every vertex is incident to at most one flagged (real or auxiliary) arc. If $r$ is the tail of a real flagged arc, that arc is the only real arc leaving $r$; if $r'$ is its head, it is the only real arc entering $r'$.
--   2. **(I2)** Every arc whose endpoints have equal level joins two vertices of level $0$.
--   3. **(I3)** If $u$ has level $j>0$ and real arcs $(w,u)$, $(u,v)$ with $w,v$ of level $<j$, there is a walk $P$ from $w$ to $v$ with exactly one flagged arc, all of whose vertices have level $<j$, of weight $\omega(w,u)+\omega(u,v)$, whose last arc $(u',v)$ has $\omega(u',v)\ge\omega(u,v)$ and whose first arc $(w,u')$ has $\omega(w,u')\ge\omega(w,u)$. The **path part** of (I3) is the same without the two arc inequalities.
--   4. **(I4)** Both endpoints of every flagged arc have level $0$.
--
--   **Formalization Note** "The only outgoing (incoming) edge" in (I1) is read among real arcs, because (S6) adds auxiliary arcs at negative vertices while Claim 4.11 asserts (I1). The walk of (I3) may use real arcs and flagged auxiliary arcs, since Lemma 4.2 turns negative arcs into flagged auxiliary arcs of the copies and asserts (I3) for the result. The path part is what reweighting preserves; Lemma 4.16 uses only it.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), §3, p.11, invariants (I1), (I2), (I3), (I4)

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph

namespace BFAlmostLinear

namespace WGraph

variable {V E : Type} (G : WGraph V E)

/-- Invariant (I1), §3, p.11: "Every vertex is adjacent to at most one (real or auxiliary) negative edge. If
a vertex r is the tail of a real negative edge, then that edge is the only outgoing edge from r. In
addition, if a vertex r′ is the head of a real negative edge, then that edge is the only incoming edge to
r′."

**Formalization Note.** "The only outgoing (incoming) edge" is read among real arcs, for two reasons. (S6),
p.23 adds auxiliary arcs `(r, r̃)` and `(r̃, r)` at a negative vertex while Claim 4.11, p.24 asserts (I1) for
the result, and the uses (the proof of Claim 4.10, p.24; Lemma 4.12, p.25) concern real walks. The negative
arcs are the flagged ones. -/
def I1 : Prop :=
  (∀ e e', G.neg e = true → G.neg e' = true →
    (G.net.tail e = G.net.tail e' ∨ G.net.tail e = G.net.head e' ∨
      G.net.head e = G.net.tail e' ∨ G.net.head e = G.net.head e') → e = e') ∧
  ∀ e, G.neg e = true → G.aux e = false →
    (∀ e', G.aux e' = false → G.net.tail e' = G.net.tail e → e' = e) ∧
    (∀ e', G.aux e' = false → G.net.head e' = G.net.head e → e' = e)

/-- Invariant (I2), §3.1, p.11: "There are no edges between Steiner vertices in the same level." A vertex of
level `i` is in `S_i`; `S₀` holds the original vertices. Real and auxiliary arcs are both covered. -/
def I2 (level : V → ℕ) : Prop :=
  ∀ e, level (G.net.tail e) = level (G.net.head e) → level (G.net.tail e) = 0

/-- The path part of invariant (I3), §3.1, p.11: if a Steiner vertex `u ∈ S_i` has real incident arcs
`a = (w, u)` and `b = (u, v)` with `v, w ∈ S_{<i}`, then there is a walk from `w` to `v` of weight
`ω(w, u) + ω(u, v)` with exactly one negative arc, all of whose vertices are in `S_{<i}`.

**Formalization Note.** This is the part preserved by a reweighting (p.11: "after which the invariants may
not hold anymore"), so it is the part that holds in `G(t)`, and Lemma 4.16 uses only it. The walk is built of
`Usable` arcs (real arcs and flagged auxiliary arcs): Lemma 4.2, p.13 turns the negative arcs of `G` into
auxiliary arcs of the copies in `G′` and claims (I3) for `G′`, so the walk cannot be required to be real. With
no auxiliary arcs, `Usable` is every arc. -/
def I3Path (level : V → ℕ) : Prop :=
  ∀ a b, G.aux a = false → G.aux b = false → G.net.head a = G.net.tail b →
    0 < level (G.net.head a) →
    level (G.net.tail a) < level (G.net.head a) → level (G.net.head b) < level (G.net.head a) →
    ∃ Q : List E, G.net.IsPathFrom (G.net.tail a) (G.net.head b) Q ∧ (∀ e ∈ Q, G.Usable e) ∧
      G.hops Q = 1 ∧ pathWeight G.w Q = G.w a + G.w b ∧
      ∀ e ∈ Q, level (G.net.tail e) < level (G.net.head a) ∧
        level (G.net.head e) < level (G.net.head a)

/-- Invariant (I3), §3.1, p.11, in full: the path part, and "letting (u′, v) denote the final edge in P, we
have ω(u′, v) ≥ ω(u, v)", and "letting (w, u′) denote the first edge in P, we have
ω(w, u′) ≥ ω(w, u)". -/
def I3 (level : V → ℕ) : Prop :=
  ∀ a b, G.aux a = false → G.aux b = false → G.net.head a = G.net.tail b →
    0 < level (G.net.head a) →
    level (G.net.tail a) < level (G.net.head a) → level (G.net.head b) < level (G.net.head a) →
    ∃ Q : List E, G.net.IsPathFrom (G.net.tail a) (G.net.head b) Q ∧ (∀ e ∈ Q, G.Usable e) ∧
      G.hops Q = 1 ∧ pathWeight G.w Q = G.w a + G.w b ∧
      (∀ e ∈ Q, level (G.net.tail e) < level (G.net.head a) ∧
        level (G.net.head e) < level (G.net.head a)) ∧
      (∀ l, Q.getLast? = some l → G.w b ≤ G.w l) ∧
      (∀ f, Q.head? = some f → G.w a ≤ G.w f)

/-- Invariant (I4), §3.1, p.11: "For any (real or auxiliary) negative edge (r, r′), both r and r′ are in
level 0." -/
def I4 (level : V → ℕ) : Prop :=
  ∀ e, G.neg e = true → level (G.net.tail e) = 0 ∧ level (G.net.head e) = 0

end WGraph

end BFAlmostLinear


