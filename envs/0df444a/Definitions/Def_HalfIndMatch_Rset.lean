-- Prove2me | Definitions.Def_HalfIndMatch_Rset
-- name    : HalfIndMatch_Rset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:10.55906+00:00
-- url     : https://prove2.me/theorems/c1a3f3e8-56c4-4b79-926e-be287a4eeb85
-- title:
--   The set $R_S$, the events $\mathcal A$ (perfect matching on $S$) and $\mathcal B$ ($R_S$ independent), and “$S$ spans a maximal induced matching”
-- statement:
--   For a graph $G$ on $[n]$ and a vertex set $S\subseteq[n]$:
--
--   1. $R_S\subseteq[n]\setminus S$ is the set of vertices outside $S$ with no neighbour in $S$;
--   2. $G[S]$ is a **perfect matching** (the event $\mathcal A$) if every vertex of $S$ has exactly one neighbour in $S$;
--   3. a set $T$ is **independent** if no two of its vertices are adjacent; the event $\mathcal B$ is that $R_S$ is independent;
--   4. $S$ **spans a maximal induced matching** if some maximal induced matching $M$ of $G$ has $V(M)=S$.
--
--   These are the objects of the first-moment computation in the proof of Proposition 3.1, eqs. (3)–(5).
--
--   **Formalization Note** The module declares `Rset`, `IsPerfectOn`, `IsIndep` and `SpansMaximal`.
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), proof of Proposition 3.1, p.13 (PDF p.15), the sentences before eq. (3)

import Mathlib
import Definitions.Def_HalfIndMatch_IsInducedMatching

open scoped Classical

namespace HalfIndMatch

/-- `R_S`: the vertices outside `S` with no neighbour in `S`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs:
Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), proof of
Proposition 3.1, p.13 (PDF p.15): "Let RS ⊆ [n] \ S be the random set of vertices with no
neighbors in S." -/
noncomputable def Rset {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => v ∉ S ∧ ∀ u ∈ S, ¬ G.Adj u v

/-- The event `A` of the proof of Proposition 3.1: `G[S]` is a perfect matching, i.e. every vertex
of `S` has exactly one `G`-neighbour in `S`.

Source: arXiv:2610.40369 (held version, sha256 a1b329a1…), p.13 (PDF p.15): "Let A denote the
event that G[S] is a perfect matching". -/
def IsPerfectOn {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ v ∈ S, ∃! w, w ∈ S ∧ G.Adj v w

/-- A set `T` of vertices is independent in `G`: no two vertices of `T` are adjacent. The event `B`
of the proof of Proposition 3.1 is `IsIndep G (Rset G S)`.

Source: arXiv:2610.40369 (held version, sha256 a1b329a1…), p.13 (PDF p.15): "let B denote the
event that RS is an independent set". -/
def IsIndep {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v

/-- "S spans a maximal induced matching": some maximal induced matching of `G` has endpoint set
exactly `S`.

Source: arXiv:2610.40369 (held version, sha256 a1b329a1…), eq. (3), p.13 (PDF p.15). -/
def SpansMaximal {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∃ M : Finset (Sym2 (Fin n)), IsMaximalInducedMatching G M ∧ vset M = S

end HalfIndMatch


