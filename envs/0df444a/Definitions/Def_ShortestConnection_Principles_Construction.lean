-- Prove2me | Definitions.Def_ShortestConnection_Principles_Construction
-- name    : ShortestConnection_Principles_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:53:30.011497+00:00
-- url     : https://prove2.me/theorems/30cd7493-1dee-4314-b400-8644d1c56eb5
-- title:
--   Construction principles P1 and P2, and constructions by N−1 applications
-- statement:
--   Let $G$ be a simple graph on the finite set $V$ of terminals with real edge lengths $w$, and let $F$ be the set of links made so far, with link graph $H(F)$. The connected components of $H(F)$ are the **isolated terminals** (one-terminal components) and the **isolated fragments** (components with at least two terminals). Only edges of $G$ are possible links: a missing edge has infinite length.
--
--   1. **Principle 1** (P1): "Any isolated terminal can be connected to a nearest neighbor." Adding the link $e$ is an application of P1 when $e = \{t,n\}$, where $t$ is an isolated terminal, $\{t,n\}$ is an edge of $G$, and
--   $$w(\{t,n\}) \le w(\{t,m\}) \quad\text{for every } G\text{-neighbor } m \text{ of } t.$$
--   2. **Principle 2** (P2): "Any isolated fragment can be connected to a nearest neighbor by a shortest available link." Adding $e$ is an application of P2 when $e = \{u,n\}$, where $u$ lies in an isolated fragment $C$ (the component of $u$, which contains at least two terminals), $n \notin C$, $\{u,n\}$ is an edge of $G$, and
--   $$w(\{u,n\}) \le w(\{u',n'\}) \quad\text{for every edge } \{u',n'\} \text{ of } G \text{ with } u' \in C,\ n' \notin C.$$
--   3. An **application** is an application of P1 or of P2, to any isolated terminal or isolated fragment.
--   4. A **construction** is a finite sequence of links $e_0, e_1, \dots, e_{k-1}$ in which each $e_i$ is an application with respect to the set $\{e_0,\dots,e_{i-1}\}$ of links made before it.
--   5. A **complete construction** is a construction with exactly $N - 1$ links, where $N = |V|$.
--
--   The distance of a terminal $n$ from a fragment $C$ is the least length of a link from $n$ into $C$, so the single inequality in P2 says exactly that $n$ is a nearest neighbor of $C$ and that $\{u,n\}$ is a shortest link from $n$ to $C$. P1 and P2 may be applied in any order and to any component; Prim's systematic variant (one growing fragment) and Kruskal's rule (globally shortest link) are special cases.
--
--   **Formalization Note** A construction is a Lean list of unordered pairs; each entry is checked against the set of entries before it. $N-1$ is natural-number subtraction, used only for nonempty $V$.
-- source:
--   Prim, Shortest Connection Networks And Some Generalizations, Bell System Tech. J. 36 (1957), p. 1391, §II (isolated terminal, fragment, isolated fragment, nearest neighbor; Principle 1, Principle 2); p. 1392 (N-1 applications); p. 1399 (non-existent edges have length ∞)

import Mathlib
import Definitions.Def_ShortestConnection_Principles_SpanningSubtree

namespace ShortestConnection.Principles

/-- One application of Principle 1 (Prim 1957, p. 1391: "Any isolated terminal can be connected
to a nearest neighbor") to the links `F` made so far, adding the link `e`.
The terminal `t` is isolated (no link of `F` meets it), and `e = s(t, n)` joins `t` to a nearest
neighbor `n`: `t–n` is an edge of `G` and `w s(t, n) ≤ w s(t, m)` for every `G`-neighbor `m` of `t`.
Only edges of `G` count as possible links (a missing edge has length `∞`, p. 1399). -/
def IsP1Step {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (e : Sym2 V) : Prop :=
  ∃ t n : V, (∀ x : V, ¬ (linkGraph F).Adj t x) ∧ G.Adj t n ∧ e = s(t, n) ∧
    ∀ m : V, G.Adj t m → w s(t, n) ≤ w s(t, m)

/-- One application of Principle 2 (Prim 1957, p. 1391: "Any isolated fragment can be connected to
a nearest neighbor by a shortest available link") to the links `F` made so far, adding `e`.
The isolated fragment is the connected component `C = {x | (linkGraph F).Reachable u x}` of a
terminal `u` that has at least one link (so `C` has at least two terminals; an isolated fragment
has no external connections, so it is a whole component). The link `e = s(u, n)` is an edge of
`G` with `n ∉ C`, and it is no longer than any edge `s(u', n')` of `G` with `u' ∈ C`, `n' ∉ C`.
Since the distance of `n` from `C` is the least length of a `G`-edge from `n` into `C`, this single
inequality says exactly that `n` is a nearest neighbor of `C` and `u–n` a shortest link from `n`
to `C`. -/
def IsP2Step {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (e : Sym2 V) : Prop :=
  ∃ u n : V, (∃ x : V, (linkGraph F).Adj u x) ∧ ¬ (linkGraph F).Reachable u n ∧ G.Adj u n ∧
    e = s(u, n) ∧
    ∀ u' n' : V, (linkGraph F).Reachable u u' → ¬ (linkGraph F).Reachable u n' → G.Adj u' n' →
      w s(u, n) ≤ w s(u', n')

/-- An application of P1 or P2 to the links `F` made so far, adding the link `e`
(Prim 1957, pp. 1391–1392; P1 and P2 may be applied to any isolated terminal or fragment, in any
order). -/
def IsApplication {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (F : Finset (Sym2 V))
    (e : Sym2 V) : Prop :=
  IsP1Step G w F e ∨ IsP2Step G w F e

/-- A construction by P1 and P2 (Prim 1957, §II): a list of links in which each link is an
application of P1 or P2 with respect to the links chosen before it. -/
def IsConstruction {V : Type*} [DecidableEq V] (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (l : List (Sym2 V)) : Prop :=
  ∀ (i : ℕ) (h : i < l.length), IsApplication G w (l.take i).toFinset l[i]

/-- A complete construction by P1 and P2: a construction with `N - 1` links, where `N` is the
number of terminals (Prim 1957, p. 1392: "an N-terminal network is connected by N-1
applications"). `Fintype.card V - 1` is natural-number subtraction; it is used only for nonempty
`V`. -/
def IsCompleteConstruction {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (w : Sym2 V → ℝ) (l : List (Sym2 V)) : Prop :=
  IsConstruction G w l ∧ l.length = Fintype.card V - 1

end ShortestConnection.Principles


