-- Prove2me | Definitions.Def_MSTCuts2027_Parallel_CutModel
-- name    : MSTCuts2027_Parallel_CutModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:42.564392+00:00
-- url     : https://prove2.me/theorems/12b53484-b90b-4dc6-bd70-8970e3201d89
-- title:
--   Symmetric real cut functions, $(u,v)$-mincuts, $\lambda_1$ and the capacities of $G_1$
-- statement:
--   Let $V$ be a finite vertex set. A **cut** is a nonempty proper subset $C\subsetneq V$. A **cut function** is any $F$ assigning a real number to each cut with
--   $$F(C)=F(V\setminus C).$$
--   Nothing else is assumed: $F$ may be negative and need not be submodular. A cut **separates** $u,v$ when exactly one of them lies in it, and a **$(u,v)$-mincut** is a cut separating them that has the least $F$-value among all cuts of $V$ separating them. Its value is $\lambda_1(u,v)$.
--
--   The graph $G_1$ is the complete simple graph on $V$ in which the edge $\{u,v\}$ has capacity $\lambda_1(u,v)$. For $S\subseteq V$, $G_1[S]$ is its induced subgraph. An **MST** in this paper is a spanning tree of maximum total capacity.
--
--   These objects are shared by every statement of the mission. The value $\lambda_1(u,v)$ is computed from $F$, not supplied as data.
--
--   **Formalization Note** $F$ is a total function on `Finset V`, and only its symmetry on cuts is required; its values on $\emptyset$ and $V$ are never read, because those sets separate no pair. $\lambda_1(u,v)$ is a real infimum over the separating cuts: for $u\ne v$ that set of cuts is finite and nonempty, so the infimum is attained; for $u=v$ it is empty and the value is the junk $0$, which no statement reads. Maximum spanning trees are the published `IsMaximalSpanningSubtree`, which allows all real capacities. A tree is connected, hence nonempty, so an MST of $G_1[S]$ exists only for nonempty $S$.
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, §1 and §2 (cut functions, G1), printed p. 1 and 5, PDF p. 3 and 7

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree

/-!
# Arbitrary symmetric cut functions, minimum cuts and the graph `G₁`

Surender Baswana, Anupam Roy, *Using MSTs to Compute All-Pairs Mincuts and Beyond ...*,
STOC 2027 submission #21, §1 (printed p. 1, PDF p. 3) and §2 (printed p. 5, PDF p. 7).
-/

namespace MSTCuts2027.Parallel

open FlowsNetworks.MultiTerminal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A cut function in the sense of the paper (printed p. 1): a finite real value on subsets with
`F C = F (V \ C)` on every cut, i.e. on every nonempty proper subset `C` of `V`. Nothing else is
assumed: `F` may be negative and need not be submodular. The values of `F` on `∅` and `V` are
junk that no statement of the mission reads, since neither set separates a pair. -/
def IsSymmetricCutFunction (F : Finset V → ℝ) : Prop :=
  ∀ C : Finset V, C.Nonempty → C ≠ Finset.univ → F Cᶜ = F C

/-- The cut `C` separates `u` and `v`: exactly one of them lies in `C`. Since the paper's cut
`(C, V \ C)` is unoriented, either orientation counts. -/
def Separates (C : Finset V) (u v : V) : Prop :=
  (u ∈ C ∧ v ∉ C) ∨ (u ∉ C ∧ v ∈ C)

/-- `C` is a `(u, v)`-mincut: a `(u, v)`-cut of least `F`-value among all `(u, v)`-cuts of `V`. -/
def IsMincut (F : Finset V → ℝ) (u v : V) (C : Finset V) : Prop :=
  Separates C u v ∧ ∀ C' : Finset V, Separates C' u v → F C ≤ F C'

/-- `lam F u v` is the paper's `λ₁(u, v)`, the value of a `(u, v)`-mincut. For `u ≠ v` the set of
`(u, v)`-cuts is finite and nonempty (it contains `{u}`), so this infimum is attained. For `u = v`
the set is empty and the value is the junk `0`; only distinct pairs are ever used. -/
noncomputable def lam (F : Finset V → ℝ) (u v : V) : ℝ :=
  sInf (F '' {C : Finset V | Separates C u v})

omit [Fintype V] in
theorem separates_comm (C : Finset V) (u v : V) : Separates C u v ↔ Separates C v u := by
  unfold Separates
  tauto

omit [Fintype V] in
theorem lam_comm (F : Finset V → ℝ) (u v : V) : lam F u v = lam F v u := by
  unfold lam
  congr 2
  ext C
  exact separates_comm C u v

/-- The edge capacities of `G₁` (paper, §2): the complete graph on `V` whose edge `{u, v}` has
capacity `λ₁(u, v)`. The value on a diagonal element of `Sym2 V` is junk: the complete simple graph
has no loops. -/
noncomputable def capacity (F : Finset V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨lam F, lam_comm F⟩

/-- The edge capacities of the induced subgraph `G₁[S]`, on the vertex type of `S`. -/
noncomputable def capacityOn (F : Finset V → ℝ) (S : Finset V) : Sym2 {y // y ∈ S} → ℝ :=
  fun e => capacity F (e.map Subtype.val)

/-- `T` is a maximum spanning tree of `G₁[S]` ("MST" always means maximum total capacity in this
paper). A tree is connected, hence nonempty, so this forces `S` to be nonempty. -/
def IsMSTOn (F : Finset V → ℝ) (S : Finset V) (T : SimpleGraph {y // y ∈ S}) : Prop :=
  IsMaximalSpanningSubtree ⊤ T (capacityOn F S)

end MSTCuts2027.Parallel


