-- Prove2me | Definitions.Def_SingleMachinePrec_Biclique_SG
-- name    : SingleMachinePrec_Biclique_SG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:04:44.670565+00:00
-- url     : https://prove2.me/theorems/221f4be1-222f-4c0d-80ad-cb208ca65bfd
-- title:
--   Maximum edge biclique (Definition 9.1) and the bipartite scheduling instance S_G (§9)
-- statement:
--   Let $G=(U,V,E)$ be a bipartite graph with vertex classes $U$, $V$ and edge set $E\subseteq U\times V$.
--
--   1. An **edge biclique** of $G$ is a pair $A\subseteq U$, $B\subseteq V$ with $A\times B\subseteq E$, i.e. a complete $|A|$-by-$|B|$ subgraph; its **value** is $|A|\cdot|B|$. The **maximum edge biclique problem** (Definition 9.1, p. 665) asks for an edge biclique of largest value; $\mathrm{MEB}(G)$ denotes that largest value (the empty biclique, of value $0$, is allowed).
--   2. The **bipartite scheduling instance** $S_G$ (§9, p. 665) has job set $U\cup V$ and precedence constraints
--   $$P=(U\times V)\setminus E,$$
--   so a job $u\in U$ must precede a job $v\in V$ exactly when $\{u,v\}$ is not an edge. The jobs of $U$ have processing time $1$ and weight $0$; the jobs of $V$ have processing time $0$ and weight $1$. Hence the value of a schedule is $\sum_{v\in V}C_v$, where $C_v$ is the number of jobs of $U$ scheduled before $v$.
--   3. For a schedule $\sigma$ of $S_G$ and $i\ge 1$, $\sigma(i)$ (p. 666) is the number of jobs of $V$ scheduled before $i$ jobs of $U$ have been scheduled, that is, the number of $v\in V$ preceded in $\sigma$ by fewer than $i$ jobs of $U$.
--   4. For $A\subseteq U$, $B\subseteq V$, a schedule is **in the block order** $U\setminus A\to B\to A\to V\setminus B$ (p. 666) if every job of an earlier block precedes every job of a later block; the order inside a block is arbitrary.
--
--   These objects are the vocabulary of Lemma 9.1, which ties the optimal value of $S_G$ to $\mathrm{MEB}(G)$.
--
--   **Formalization Note** $U$ and $V$ are finite types, $E$ is a relation `U → V → Prop`, and the job set is the disjoint union `U ⊕ V` (all of it, `Finset.univ`). Precedence in a schedule compares list positions. The block order is encoded by the ranks $0,1,2,3$ on $U\setminus A$, $B$, $A$, $V\setminus B$, the list being sorted by rank. The paper's $P$ is the strict relation $(U\times V)\setminus E$; its reflexive closure is the partial order of §1, and feasibility only constrains distinct jobs, so both readings give the same feasible schedules.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 665, Definition 9.1 and the definition of S_G; p. 666, notation σ*(i) and the order U\A → B → A → V\B in the proof of Lemma 9.1

import Mathlib
import Definitions.Def_SingleMachinePrec_Biclique_WeightedCompletion

namespace SingleMachinePrec.Biclique

variable {U V : Type*}

/-- An edge biclique of the bipartite graph `G = (U, V, E)` (Definition 9.1, p. 665): sets
`A ⊆ U`, `B ⊆ V` with every pair of `A × B` an edge, i.e. a complete `|A|`-by-`|B|` subgraph.
Its value is `|A| · |B|`. -/
def IsEdgeBiclique (E : U → V → Prop) (A : Finset U) (B : Finset V) : Prop :=
  ∀ u ∈ A, ∀ v ∈ B, E u v

/-- The value `k_1 · k_2` of a maximum edge biclique of `G = (U, V, E)` (Definition 9.1, p. 665):
the maximum of `|A| · |B|` over all edge bicliques `(A, B)`, the empty ones (value `0`) included. -/
noncomputable def maxBicliqueValue [Fintype U] [Fintype V] (E : U → V → Prop) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset U × Finset V)).filter
    (fun AB => IsEdgeBiclique E AB.1 AB.2)).sup (fun AB => AB.1.card * AB.2.card)

/-- The precedence constraints of the bipartite scheduling instance `S_G` (§9, p. 665): the jobs
are `U ∪ V` (here the disjoint union `U ⊕ V`) and `P = (U × V) \ E`, i.e. `u ∈ U` must precede
`v ∈ V` exactly when `(u, v)` is not an edge; there are no other constraints. -/
def precSG (E : U → V → Prop) : U ⊕ V → U ⊕ V → Prop
  | Sum.inl u, Sum.inr v => ¬ E u v
  | _, _ => False

/-- Processing times of `S_G` (§9, p. 665): `1` for the jobs of `U`, `0` for the jobs of `V`. -/
def procSG : U ⊕ V → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => 0

/-- Weights of `S_G` (§9, p. 665): `0` for the jobs of `U`, `1` for the jobs of `V`. -/
def weightSG : U ⊕ V → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- The value `val(σ) = Σ_j w_j C_j` of a sequence `l` of all the jobs `U ∪ V` of `S_G`. -/
noncomputable def valSG [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (l : List (U ⊕ V)) : ℝ :=
  weightedCompletion procSG weightSG Finset.univ l

/-- `l` is an optimal schedule `σ*` of `S_G`: a sequence of all the jobs `U ∪ V` that observes
`P = (U × V) \ E` and minimizes `Σ_j w_j C_j` among all such sequences. -/
def IsOptimalSG [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (E : U → V → Prop) (l : List (U ⊕ V)) : Prop :=
  IsOptimalSchedule (precSG E) procSG weightSG Finset.univ l

/-- `σ(i)` (§9, p. 666): the number of jobs of `V` scheduled in `l` before `i` jobs of `U` have
been scheduled, i.e. the jobs `v ∈ V` preceded in `l` by fewer than `i` jobs of `U`.
"Precedes" compares positions in the list (`List.idxOf`). -/
def vBefore [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (l : List (U ⊕ V)) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun v : V =>
    (Finset.univ.filter (fun u : U => l.idxOf (Sum.inl u) < l.idxOf (Sum.inr v))).card < i)).card

/-- The block order `U \ A → B → A → V \ B` of §9, p. 666, as a rank: `0` on `U \ A`, `1` on
`B`, `2` on `A`, `3` on `V \ B`. -/
def blockRank [DecidableEq U] [DecidableEq V] (A : Finset U) (B : Finset V) : U ⊕ V → ℕ
  | Sum.inl u => if u ∈ A then 2 else 0
  | Sum.inr v => if v ∈ B then 1 else 3

/-- `l` schedules all the jobs of `S_G` in the order `U \ A → B → A → V \ B` (§9, p. 666): it is a
sequence of `U ∪ V` whose blocks appear in that order (the order inside a block is arbitrary). -/
def InBlockOrder [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (A : Finset U) (B : Finset V) (l : List (U ⊕ V)) : Prop :=
  MooreLateJobs.Shared.IsSchedule Finset.univ l ∧
    l.Pairwise (fun x y => blockRank A B x ≤ blockRank A B y)

end SingleMachinePrec.Biclique


