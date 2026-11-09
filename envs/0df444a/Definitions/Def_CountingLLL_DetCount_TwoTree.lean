-- Prove2me | Definitions.Def_CountingLLL_DetCount_TwoTree
-- name    : CountingLLL_DetCount_TwoTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:35.252174+00:00
-- url     : https://prove2.me/theorems/c590b4a6-2b00-4814-8c17-80f2d46679f1
-- title:
--   Square graph, 2-trees and distance to a set
-- statement:
--   For a simple graph $G$ on a vertex type $V$, the **square graph** $G^2$ joins two distinct vertices whenever their shortest-path distance in $G$ is at most $2$. Distances take values in $\mathbb N\cup\{\infty\}$, with distance $\infty$ between different components.
--
--   A **2-tree** (Definition 2.4) is a finite vertex set $T$ that is independent in $G$ and whose induced subgraph $G^2[T]$ is connected; in particular $T$ is nonempty.
--
--   For a vertex $u$ and a finite set $S$, $\mathrm{dist}_G(u,S)=\min_{v\in S}\mathrm{dist}_G(u,v)$, with the convention $\mathrm{dist}_G(u,\emptyset)=\infty$.
--
--   2-trees are the index set of the expansion in §3; Corollary 2.6 counts them.
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Definitions 2.3 and 2.4, §2.3, PDF p. 7 (printed p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

set_option autoImplicit false

namespace CountingLLL.DetCount

/-- The square graph `G²` (Definition 2.3): distinct vertices are adjacent iff their
shortest-path distance in `G` is at most `2`. Distances are extended natural numbers
(`SimpleGraph.edist`), so vertices in different components are at distance `∞`. -/
def square {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ G.edist u v ≤ 2
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [SimpleGraph.edist_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A 2-tree (Definition 2.4): a finite vertex set that is independent in `G` and whose
induced subgraph in the square `G²` is connected (in particular, nonempty). -/
def IsTwoTree {V : Type*} (G : SimpleGraph V) (T : Finset V) : Prop :=
  G.IsIndepSet (T : Set V) ∧ ((square G).induce (T : Set V)).Connected

/-- `dist_G(u, S) = min_{v ∈ S} dist_G(u, v)` (§2.3), with `dist_G(u, ∅) = ∞` and the distance
between different components `∞`. -/
noncomputable def distSet {V : Type*} (G : SimpleGraph V) (u : V) (S : Finset V) : ℕ∞ :=
  S.inf (fun v => G.edist u v)

end CountingLLL.DetCount


