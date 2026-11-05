-- Prove2me | Definitions.Def_TenChallenges_Sidorenko
-- name    : TenChallenges_Sidorenko
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:39:21.858651+00:00
-- url     : https://prove2.me/theorems/32fb9635-3637-4230-9721-3dcc94976013
-- title:
--   Homomorphism density, Sidorenko's inequality, bipartite graphs with bounded sides
-- statement:
--   The definitions behind Challenge 4 of the Ten Challenges benchmark, for simple graphs $H$ on a finite vertex type $W$ and $G$ on a finite vertex type $V$.
--
--   1. **Homomorphism density.** $t(H,G)$ is the number of maps $f\colon W\to V$ such that $f(a)f(b)$ is an edge of $G$ whenever $ab$ is an edge of $H$, divided by $|V|^{|W|}$, as a real number.
--   2. **Sidorenko's inequality** for $H$ in $G$:
--   $$t(H,G)\ \ge\ t(K_2,G)^{\,e(H)},$$
--   where $K_2$ is the complete graph on two vertices, so that $t(K_2,G)$ is the edge density $2e(G)/|V|^2$, and $e(H)$ is the number of edges of $H$.
--   3. **Bipartite with sides bounded by $k$.** $H$ admits sets $X,Y$ of vertices with $X\cup Y=W$, $X$ and $Y$ disjoint, every edge of $H$ joining $X$ to $Y$, $|X|\le k$ and $|Y|\le k$.
--
--   These definitions express Sidorenko's conjecture and its restriction to bipartite graphs of bounded size; the density $t(H,G)$ is reusable for any subgraph-counting statement.
--
--   **Formalization Note.** The count of homomorphisms is `Nat.card` of a subtype of functions; the bipartition uses Mathlib's `IsBipartiteWith` and the sizes are `Set.ncard`. When $|V|=0$ the density is $0$ by the convention for division by zero.
-- source:
--   Ten Challenges repository, file Defs_and_Lems/Sidorenko.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Defs_and_Lems/Sidorenko.lean; conjecture as in A. F. Sidorenko, A correlation inequality for bipartite graphs, Graphs Combin. 9 (1993).

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Real.Basic

open SimpleGraph

variable {W V : Type*} [Fintype W] [Fintype V]

/-- The homomorphism density `t(H, G)`: the number of
graph homomorphisms `H → G`, divided by `|V(G)| ^ |V(H)|`. -/
noncomputable def homDensity (H : SimpleGraph W) (G : SimpleGraph V) : ℝ :=
  (Nat.card {f : W → V // ∀ ⦃a b : W⦄, H.Adj a b → G.Adj (f a) (f b)} : ℝ) /
    (Fintype.card V : ℝ) ^ Fintype.card W

/-- Sidorenko's inequality for a graph `H` over `G`,
in normalized homomorphism-density form: `t(H, G) ≥ t(K₂, G) ^ e(H)`. -/
def SidorenkoFor (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ Nat.card H.edgeSet

/-- `H` is *bipartite with sides bounded by `k`*: it admits
a bipartition `V(H) = X ∪ Y`, with `|X| ≤ k` and `|Y| ≤ k`. -/
def BipartiteBoundedBy (H : SimpleGraph W) (k : ℕ) : Prop :=
  ∃ X Y : Set W,
    H.IsBipartiteWith X Y ∧ X ∪ Y = Set.univ ∧ X.ncard ≤ k ∧ Y.ncard ≤ k


