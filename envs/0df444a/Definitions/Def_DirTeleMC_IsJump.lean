-- Prove2me | Definitions.Def_DirTeleMC_IsJump
-- name    : DirTeleMC_IsJump
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:05.42643+00:00
-- url     : https://prove2.me/theorems/b1f61741-787b-4181-86b0-5b2a557cf34f
-- title:
--   Directed walks, jumps with at most $\theta$ arcs, departures and distance
-- statement:
--   A digraph $G$ on the vertex set $V = \{0, \dots, n-1\}$ is given by its adjacency matrix. A **walk** is a nonempty sequence of vertices $(w_0, \dots, w_m)$ with an arc $(w_{i-1}, w_i)$ for every $i$; it has $m$ arcs, and the one-vertex sequence $(u)$ is the **empty walk** at $u$. A **path** is a walk without repeated vertex.
--
--   A **jump** from $u$ to $w$ with at most $\theta$ arcs is a walk from $u$ to $w$ with at most $\theta$ arcs. For a walk $P$ and a vertex $v$, the number of **departures** $L_P(v)$ is the number of arcs of $P$ that leave $v$, counted with multiplicity. We write $\mathrm{dist}(u,w) \le \theta$ when some walk from $u$ to $w$ has at most $\theta$ arcs, and $\mathrm{dist}(u,w)$ for the least such number.
--
--   These notions underlie the jump arborescences of Definition 4.1 and the unfolding of §B.3.
--
--   **Formalization Note** Walks are vertex lists. The source sets $\mathrm{dist}(u,w)=\infty$ for unreachable $w$; the Lean value is then $0$, and it is only used between vertices joined by a walk.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), §3, p.8 (PDF p.9); Definition 4.1, p.10 (PDF p.11); §B.4, p.21 (PDF p.22)

import Mathlib

namespace DirTeleMC

/-- **Directed walks and jumps with at most `θ` arcs.**
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), §3, p.8 (digraphs, arcs, `dist`) and Definition 4.1, p.10 (jumps: "a directed
walk from u to w with at most θ arcs. When u = w, this is the empty walk").

A digraph on the vertex set `Fin n` is an adjacency matrix `adj : Fin n → Fin n → Bool`; `(u, v)` is an arc
when `adj u v = true`. A walk is a nonempty list of vertices `[w₀, …, w_m]` with an arc from each entry to the
next; it has `m = length − 1` arcs. `IsJump adj θ u w P` says that `P` is a walk from `u` to `w` with at most
`θ` arcs.

**Formalization Note.** Walks are vertex lists; the one-vertex list `[u]` is the empty walk from `u` to `u`.
A path is a walk whose list has no repeated vertex (`List.Nodup`). Loops `adj u u = true` are allowed. -/
def IsJump {n : ℕ} (adj : Fin n → Fin n → Bool) (θ : ℕ) (u w : Fin n) (P : List (Fin n)) : Prop :=
  P.head? = some u ∧ P.getLast? = some w ∧ P.IsChain (fun a b => adj a b = true) ∧ P.length ≤ θ + 1

/-- The number of departures of a walk `P` from the vertex `v`: the number of indices `i < length − 1`
with `P[i] = v`, i.e. the number of arcs of `P` that leave `v`, counted with multiplicity
(Definition 4.1, p.10: "the total number of departures from v along all jumps, counting repeated
traversals"; §B.4, p.21: "L_P(v) be the number of arcs of P that leave v"). -/
def departures {n : ℕ} (P : List (Fin n)) (v : Fin n) : ℕ := P.dropLast.count v

/-- `HopReach adj θ u w`: some walk from `u` to `w` has at most `θ` arcs, i.e. `dist(u, w) ≤ θ`
(§B.3, p.20: the children of a node of the unfolding). -/
def HopReach {n : ℕ} (adj : Fin n → Fin n → Bool) (θ : ℕ) (u w : Fin n) : Prop :=
  ∃ P, IsJump adj θ u w P

/-- `w` is reachable from `u`. -/
def Reach {n : ℕ} (adj : Fin n → Fin n → Bool) (u w : Fin n) : Prop :=
  ∃ θ, HopReach adj θ u w

/-- The distance `dist(u, w)`: the least number of arcs of a walk from `u` to `w` (§3, p.8).

**Formalization Note.** The source sets `dist(u, w) = ∞` when `w` is unreachable; here the value is then `0`.
It is only used between vertices with `Reach adj u w` (terminals, under `Inst.WF`, and vertices of an
arborescence of the digraph rooted at `u`), where it is the source's distance. -/
noncomputable def dist {n : ℕ} (adj : Fin n → Fin n → Bool) (u w : Fin n) : ℕ := by
  classical
  exact if h : Reach adj u w then Nat.find h else 0

end DirTeleMC


