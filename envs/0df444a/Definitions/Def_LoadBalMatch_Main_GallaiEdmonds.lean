-- Prove2me | Definitions.Def_LoadBalMatch_Main_GallaiEdmonds
-- name    : LoadBalMatch_Main_GallaiEdmonds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:32:23.829669+00:00
-- url     : https://prove2.me/theorems/9b322ca8-2796-44e6-9b72-757106b8c95e
-- title:
--   The Gallai–Edmonds decomposition $(D,A,C)$, the components of $H[D]$, factor-critical graphs (Definition 6.6)
-- statement:
--   Let $H$ be a graph on $V$. Its **Gallai–Edmonds decomposition** (Definition 6.6) is
--   $$D=\{v:\ \text{some maximum matching of } H \text{ misses } v\},\qquad A=N_H(D)\setminus D,\qquad C=V\setminus(D\cup A),$$
--   and $D_1,\dots,D_r$ are the connected components of the induced subgraph $H[D]$. For a vertex set $S$, $H[S]$ is the graph of the edges of $H$ with both ends in $S$. A matching $M$ of $H$ is a **perfect matching of** $H[W]$ if all its edges lie inside $W$ and it covers every vertex of $W$. A vertex set $S$ induces a **factor-critical** graph if $|S|$ is odd and, for every $v\in S$, $H[S\setminus\{v\}]$ has a perfect matching. The average load of a fractional matching $x$ on a set $S$ is $\frac1{|S|}\sum_{v\in S}x_v$, which equals the common value $x_i$ on a component $D_i$ on which $x$ is constant (Lemma 6.8).
--
--   The decomposition organises every maximum matching of $H$ (Lemma 6.7) and the loads of every balanced fractional matching (Lemma 6.8).
--
--   **Formalization Note.** `gD`, `gA`, `gC` are sets of vertices; `restrictTo K S` is $K[S]$ as a graph on $V$ (vertices outside $S$ isolated); `SameDComp H u v` says $u,v\in D$ lie in the same component of $H[D]$; `dComp H u` is that component and `dComps H` the finite set $\{D_1,\dots,D_r\}$. `compLoad (load x) S` is the average load on `S`. `restrictEdges M S` is the set of edges of `M` with both ends in `S`.
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 28, §6.2, Definition 6.6; p. 28, Lemma 6.7 (factor-critical)

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching

/-!
# The Gallai–Edmonds decomposition (Definition 6.6), its components, factor-critical sets

Assadi, Bernstein, Wrzos-Kaminska, STOC 2027 submission (sha256 7cd28a8b…), §6.2 p. 28,
Definition 6.6: "Given a graph H, let D = {v : there exists a maximum matching in H missing v},
A = N_H(D) \ D, C = V \ (D ∪ A). Write D₁, …, D_r for the connected components of H[D]."

Conventions.
* `restrictTo K S` keeps the edges of `K` with both ends in `S` (the vertices outside `S` become
  isolated), so for `u, v ∈ S`, `(restrictTo K S).Reachable u v` is connectivity in `K[S]`.
* `SameDComp H u v`: `u, v ∈ D` lie in the same connected component of `H[D]`; `dComp H u` is the
  component of `u` and `dComps H` the finite set `{D₁, …, D_r}` of components.
* `compLoad x S` is the average load of `x` on `S`; on a component `Dᵢ` on which `x` is constant
  (Lemma 6.8, item 2) it is the common value `xᵢ`.
* `IsPerfectMatchingOf H M W`: `M` is a matching of `H` whose edges lie inside `W` and cover every
  vertex of `W`, i.e. a perfect matching of `H[W]`.
* `IsFactorCritical H S`: `|S|` is odd and for every `v ∈ S` the graph `H[S \ {v}]` has a perfect
  matching.
* `restrictEdges M S` is the set of edges of `M` with both ends in `S`.
-/

namespace LoadBalMatch.Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `K[S]` as a graph on `V`: the edges of `K` with both ends in `S`. -/
def restrictTo (K : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := u ∈ S ∧ v ∈ S ∧ K.Adj u v
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun v h => K.loopless.irrefl v h.2.2⟩

/-- `D = {v : there exists a maximum matching in H missing v}`. -/
def gD (H : SimpleGraph V) : Set V :=
  {v | ∃ M, IsMaximumMatching H M ∧ ¬ Covers M v}

/-- `A = N_H(D) \ D`. -/
def gA (H : SimpleGraph V) : Set V :=
  {v | v ∉ gD H ∧ ∃ u ∈ gD H, H.Adj v u}

/-- `C = V \ (D ∪ A)`. -/
def gC (H : SimpleGraph V) : Set V :=
  {v | v ∉ gD H ∧ v ∉ gA H}

/-- `u` and `v` are vertices of `D` in the same connected component of `H[D]`. -/
def SameDComp (H : SimpleGraph V) (u v : V) : Prop :=
  u ∈ gD H ∧ v ∈ gD H ∧ (restrictTo H (gD H)).Reachable u v

/-- The connected component of `H[D]` containing `u` (empty if `u ∉ D`). -/
noncomputable def dComp (H : SimpleGraph V) (u : V) : Finset V := by
  classical
  exact Finset.univ.filter (SameDComp H u)

/-- The components `D₁, …, D_r` of `H[D]`. -/
noncomputable def dComps (H : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact (Finset.univ.filter (· ∈ gD H)).image (dComp H)

/-- The average load `(Σ_{v∈S} x_v)/|S|` of `x` on `S`; equal to `xᵢ` on a component `Dᵢ` on
which `x` is constant. -/
noncomputable def compLoad (load : V → ℝ) (S : Finset V) : ℝ :=
  (∑ v ∈ S, load v) / S.card

/-- `M` is a perfect matching of `H[W]`. -/
def IsPerfectMatchingOf (H : SimpleGraph V) (M : Finset (Sym2 V)) (W : Set V) : Prop :=
  IsMatchingIn H M ∧ (∀ e ∈ M, ∀ v ∈ e, v ∈ W) ∧ ∀ v ∈ W, Covers M v

/-- `H[S]` is factor-critical: `|S|` is odd and `H[S \ {v}]` has a perfect matching for every
`v ∈ S`. -/
def IsFactorCritical (H : SimpleGraph V) (S : Finset V) : Prop :=
  Odd S.card ∧ ∀ v ∈ S, ∃ M, IsPerfectMatchingOf H M (↑S \ {v})

/-- The edges of `M` with both ends in `S`. -/
noncomputable def restrictEdges (M : Finset (Sym2 V)) (S : Set V) : Finset (Sym2 V) := by
  classical
  exact M.filter (fun e => ∀ v ∈ e, v ∈ S)

end LoadBalMatch.Main


