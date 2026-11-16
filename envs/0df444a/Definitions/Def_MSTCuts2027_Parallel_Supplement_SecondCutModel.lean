-- Prove2me | Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondCutModel
-- name    : MSTCuts2027_Parallel_Supplement_SecondCutModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:36:35.217233+00:00
-- url     : https://prove2.me/theorems/a05899bf-ce96-463e-907e-754948938bdf
-- title:
--   Second $(u,v)$-mincuts, $\lambda_2$, the existence assumption and the capacities of $G_2$
-- statement:
--   Let $V$ be a finite vertex set and $F$ a real cut function with $F(C)=F(V\setminus C)$, as in the published cut model of the mission. Write $\lambda_1(u,v)$ for the value of a $(u,v)$-mincut.
--
--   A **second $(u,v)$-mincut** is a cut $C$ separating $u$ and $v$ with $F(C)>\lambda_1(u,v)$ whose value is least among all cuts with these two properties:
--   $$F(C)=\min\{F(C') : C' \text{ separates } u,v,\ F(C')>\lambda_1(u,v)\}.$$
--   Its value is $\lambda_2(u,v)$. A second mincut need not exist (for instance when $F$ is constant); the paper assumes from §2 on that one exists for every pair of distinct vertices, and that assumption is the predicate recorded here.
--
--   The graph $G_2$ is the complete simple graph on $V$ in which the edge $\{u,v\}$ has capacity $\lambda_2(u,v)$; $G_2[S]$ is its induced subgraph on $S\subseteq V$, and an MST of $G_2[S]$ is a spanning tree of maximum total capacity.
--
--   These are the objects of §5 of the paper, shared by every statement of this supplement. The symmetry lemma $\lambda_2(u,v)=\lambda_2(v,u)$ is included because the capacities of $G_2$ are defined on unordered pairs.
--
--   **Formalization Note** $\lambda_2(u,v)$ is a real infimum over the finite set of separating cuts of value above $\lambda_1(u,v)$; it is attained when that set is nonempty and is the junk value $0$ otherwise. Every statement that reads $\lambda_2$ either assumes existence of second mincuts or provides a cut in the set. MSTs use the published `IsMaximalSpanningSubtree` with arbitrary real capacities, as for $G_1$ in the base mission.
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, §2 Preliminaries (second (s,t)-mincut, λ2, G2, standing assumption), printed p. 5, PDF p. 7

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel

/-!
# Second mincuts, `λ₂` and the graph `G₂`

Surender Baswana, Anupam Roy, *Using MSTs to Compute All-Pairs Mincuts and Beyond ...*,
STOC 2027 submission #21, §2 (printed p. 5, PDF p. 7) and §1.3 (printed p. 4, PDF p. 6).
Built on the published cut model `MSTCuts2027.Parallel` (cut functions, separation, mincuts, `λ₁`).
-/

namespace MSTCuts2027.Parallel.Supplement

open FlowsNetworks.MultiTerminal MSTCuts2027.Parallel

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `C` is a second `(u, v)`-mincut (paper, §2): a `(u, v)`-cut of minimum value among the
`(u, v)`-cuts whose value is strictly greater than `λ₁(u, v)`. -/
def IsSecondMincut (F : Finset V → ℝ) (u v : V) (C : Finset V) : Prop :=
  Separates C u v ∧ lam F u v < F C ∧
    ∀ C' : Finset V, Separates C' u v → lam F u v < F C' → F C ≤ F C'

/-- `lam2 F u v` is the paper's `λ₂(u, v)`, the value of a second `(u, v)`-mincut: the least value
of a `(u, v)`-cut whose value exceeds `λ₁(u, v)`. The set of such cuts is finite, so when it is
nonempty the infimum is attained; when no second mincut exists the value is the junk `0`. -/
noncomputable def lam2 (F : Finset V → ℝ) (u v : V) : ℝ :=
  sInf (F '' {C : Finset V | Separates C u v ∧ lam F u v < F C})

/-- The standing assumption of the paper from §2 on (printed p. 5): a second mincut exists for every
pair of distinct vertices, i.e. some `(u, v)`-cut has value strictly above `λ₁(u, v)`. -/
def SecondMincutsExist (F : Finset V → ℝ) : Prop :=
  ∀ u v : V, u ≠ v → ∃ C : Finset V, Separates C u v ∧ lam F u v < F C

omit [Fintype V] in
theorem lam2_comm (F : Finset V → ℝ) (u v : V) : lam2 F u v = lam2 F v u := by
  unfold lam2
  congr 2
  ext C
  simp only [Set.mem_ofPred_eq, separates_comm C u v, lam_comm F u v]

/-- The edge capacities of `G₂` (paper, §2): the complete graph on `V` whose edge `{u, v}` has
capacity `λ₂(u, v)`. The value on a diagonal element of `Sym2 V` is junk: the complete simple graph
has no loops. -/
noncomputable def capacity2 (F : Finset V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨lam2 F, lam2_comm F⟩

/-- The edge capacities of the induced subgraph `G₂[S]`, on the vertex type of `S`. -/
noncomputable def capacity2On (F : Finset V → ℝ) (S : Finset V) : Sym2 {y // y ∈ S} → ℝ :=
  fun e => capacity2 F (e.map Subtype.val)

/-- `T` is a maximum spanning tree of `G₂[S]` ("MST" means maximum total capacity in the paper).
A tree is connected, hence nonempty, so this forces `S` to be nonempty. -/
def IsMST2On (F : Finset V → ℝ) (S : Finset V) (T : SimpleGraph {y // y ∈ S}) : Prop :=
  IsMaximalSpanningSubtree ⊤ T (capacity2On F S)

end MSTCuts2027.Parallel.Supplement


