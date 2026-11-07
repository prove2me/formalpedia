-- Prove2me | Definitions.Def_HalfIndMatch_OnlineAlg
-- name    : HalfIndMatch_OnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:05.649848+00:00
-- url     : https://prove2.me/theorems/efcf6da4-af0a-46c0-b9bb-ac2853ecb0c0
-- title:
--   Online algorithms (Definition 2.2): local decision rules, runs, $A_t(G)$ and $M_{\mathrm{out}}$
-- statement:
--   An **online algorithm** on graphs with vertex set $[n]$ maintains a set $S_t$ of inspected vertices and an induced matching $M_t$ whose edges lie inside $S_t$, starting from $S_0=M_0=\emptyset$. In round $t$ it either terminates, or
--
--   1. selects a vertex $x_t\notin S_{t-1}$ and inspects it, which reveals the adjacencies of $x_t$ to $S_{t-1}$; then $S_t=S_{t-1}\cup\{x_t\}$;
--   2. may accept one edge $\{x_t,u_t\}$ with $u_t\in S_{t-1}\setminus V(M_{t-1})$ a neighbour of $x_t$, provided $M_t=M_{t-1}\cup\{\{x_t,u_t\}\}$ is an induced matching; otherwise $M_t=M_{t-1}$.
--
--   Accepted edges are never removed, the algorithm stops after round $n$ at the latest, and its output $M_{\mathrm{out}}$ is the matching held on termination. Every choice may depend on all previous choices and revealed adjacencies (and on auxiliary randomness independent of the graph), with no limit on memory or computation. $A_t(G)$ is the matching held after round $t$, equal to $M_{\mathrm{out}}$ once the algorithm has terminated; $A_n(G)=M_{\mathrm{out}}$.
--
--   **Formalization Note** A deterministic algorithm is a structure `OnlineAlg n` with a rule `next G S M` (the vertex to inspect, or `none` to terminate) and a rule `accept G S M x` (the proposed partner of the just-inspected vertex $x$, or `none`), where `S` is the list of inspected vertices, most recent first, and `M` the current matching. The fields `next_local` and `accept_local` require that `next` read $G$ only on pairs inside $S$ and `accept` only on pairs inside $S\cup\{x\}$: these are exactly the revealed adjacencies, and the previous choices are recorded in `S` and `M`. The run (`onlineStep`, `onlineRun`) treats a choice of an inspected vertex as termination and an illegal partner as accepting nothing. `At A G t` is $A_t(G)$ and `output A G` is $M_{\mathrm{out}}=A_n(G)$. Randomized algorithms are families of these indexed by a seed (see Theorem 2.3).
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), Definition 2.2 and the paragraph after it, pp.9–10 (PDF pp.11–12); A_t(G), §3.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_HalfIndMatch_IsInducedMatching

open scoped Classical

namespace HalfIndMatch

/-- A deterministic **online algorithm** for building an induced matching in a graph on `Fin n`
(Definition 2.2 with the auxiliary randomness fixed).

* `next G S M` is the vertex to inspect in the next round, or `none` to terminate, when `S` is the
  list of vertices inspected so far (most recent first) and `M` the current matching.
* `accept G S M x` is the proposed partner `u` of the just-inspected vertex `x` (the edge
  `{x, u}` to accept), or `none` to accept no edge in this round.
* `next_local`: the inspection/termination choice depends only on the adjacencies among the
  inspected vertices `S` (the information revealed so far).
* `accept_local`: the acceptance choice depends only on the adjacencies among `x :: S`, i.e. also
  on those revealed by inspecting `x`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs:
Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…),
Definition 2.2 and the paragraph after it, pp.9–10 (PDF pp.11–12).

**Formalization Note** The paper's choices are functions "of all previous choices and revealed
adjacencies". The revealed adjacencies after round `t` are exactly the pairs inside `S_t`, and
the previous choices are recorded by the ordered list `S` and by `M` (each accepted edge contains
the vertex inspected in its round), so a function of `(G, S, M)` that only reads `G` on pairs
inside `S` (resp. `x :: S`) is the general deterministic choice. The decision functions take the
whole graph as an argument; the locality fields are what forbid reading unrevealed pairs. Illegal
moves are handled by the run (`onlineStep`): choosing an inspected vertex terminates, and an
illegal partner accepts nothing. Every algorithm of Definition 2.2 is of this form, and every
structure of this form runs as an algorithm of Definition 2.2. -/
structure OnlineAlg (n : ℕ) where
  next : SimpleGraph (Fin n) → List (Fin n) → Finset (Sym2 (Fin n)) → Option (Fin n)
  accept : SimpleGraph (Fin n) → List (Fin n) → Finset (Sym2 (Fin n)) → Fin n → Option (Fin n)
  next_local : ∀ (G G' : SimpleGraph (Fin n)) (S : List (Fin n)) (M : Finset (Sym2 (Fin n))),
    (∀ u ∈ S, ∀ v ∈ S, (G.Adj u v ↔ G'.Adj u v)) → next G S M = next G' S M
  accept_local : ∀ (G G' : SimpleGraph (Fin n)) (S : List (Fin n)) (M : Finset (Sym2 (Fin n)))
    (x : Fin n), (∀ u ∈ x :: S, ∀ v ∈ x :: S, (G.Adj u v ↔ G'.Adj u v)) →
      accept G S M x = accept G' S M x

/-- The state of an online algorithm after a round: the inspected vertices `S_t` (most recent
first), the induced matching `M_t`, and whether the algorithm has terminated. -/
structure OnlineState (n : ℕ) where
  S : List (Fin n)
  M : Finset (Sym2 (Fin n))
  done : Bool

/-- One round of Definition 2.2. A terminated algorithm stays put. Otherwise, if `next` is `none`
or names an already inspected vertex, the algorithm terminates. Otherwise the chosen vertex `x`
is inspected (`S_t = S_{t−1} ∪ {x}`), and the proposed edge `{x, u}` is accepted exactly when
`u ∈ S_{t−1} \ V(M_{t−1})`, `u` is a neighbour of `x` and `M_{t−1} ∪ {{x, u}}` is an induced
matching; otherwise `M_t = M_{t−1}`. -/
noncomputable def onlineStep {n : ℕ} (A : OnlineAlg n) (G : SimpleGraph (Fin n))
    (st : OnlineState n) : OnlineState n :=
  if st.done then st else
    match A.next G st.S st.M with
    | none => ⟨st.S, st.M, true⟩
    | some x =>
      if x ∈ st.S then ⟨st.S, st.M, true⟩ else
        match A.accept G st.S st.M x with
        | none => ⟨x :: st.S, st.M, false⟩
        | some u =>
          if u ∈ st.S ∧ u ∉ vset st.M ∧ G.Adj x u ∧ IsInducedMatching G (insert s(x, u) st.M) then
            ⟨x :: st.S, insert s(x, u) st.M, false⟩
          else ⟨x :: st.S, st.M, false⟩

/-- The state after `t` rounds; initially `S_0 = M_0 = ∅`. -/
noncomputable def onlineRun {n : ℕ} (A : OnlineAlg n) (G : SimpleGraph (Fin n)) :
    ℕ → OnlineState n
  | 0 => ⟨[], ∅, false⟩
  | t + 1 => onlineStep A G (onlineRun A G t)

/-- `A_t(G)`: the induced matching held after round `t`, equal to `M_out` once the algorithm has
terminated.

Source: arXiv:2610.40369 (held version, sha256 a1b329a1…), §3.2, p.15 (PDF p.17): "Let At(G)
denote the induced matching constructed after the first t vertices have been exposed, with
At(G) := Mout if the algorithm has terminated by round t". -/
noncomputable def At {n : ℕ} (A : OnlineAlg n) (G : SimpleGraph (Fin n)) (t : ℕ) :
    Finset (Sym2 (Fin n)) :=
  (onlineRun A G t).M

/-- The output `M_out = A_n(G)` of the online algorithm `A` on `G`. The algorithm terminates
after round `n` at the latest: after `n` non-terminating rounds every vertex has been inspected.
-/
noncomputable def output {n : ℕ} (A : OnlineAlg n) (G : SimpleGraph (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  At A G n

end HalfIndMatch


