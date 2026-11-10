-- Prove2me | Definitions.Def_LocalLemmaHierarchy_Completeness_Graph
-- name    : LocalLemmaHierarchy_Completeness_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:19:56.998634+00:00
-- url     : https://prove2.me/theorems/839ec47a-41fd-4ba7-bd4d-a84bf6d10084
-- title:
--   Independence and matching polynomials, the independent-set and matching representations, $\lambda_c$ and $\lambda_q$
-- statement:
--   Let $G=(V,E)$ be a locally finite simple graph and $U$ a finite set of vertices. The multivariate **independence polynomial** of $G[U]$ is $\mathrm{Ind}_{G[U]}(z)=\sum_{I\subseteq U\text{ independent}}\prod_{v\in I}z_v$ (E.1), and the **matching polynomial** is $\mathrm{Match}_{G[U]}(z)=\sum_{M\text{ matching of }G[U]}\prod_{e\in M}z_e$ (E.7).
--
--   A fixed choice of **neighbor orders** is a total order $\prec_v$ on $N_G(v)$ for every $v$. The **independent-set representation** $\mathcal R^{\mathrm{ind},\prec}$ has one option per vertex with $A_v=\{v\}$, $D_v=N_G[v]$, $c_v=1$, $\tau(v)=v$ and the order $\prec_v$; a step $v\to u$ deletes $\{v\}\cup\{w\in N_G(v):w\prec_v u\}$ (E.3). The **matching representation** has one option per incident edge $e=\{v,u\}$ with $A_{v,e}=D_{v,e}=e$, $c=1$, $\tau=e$ (one factor, so the local order is trivial).
--
--   The **uniform Shearer threshold** (1.1) is $\lambda_c(G)=\inf_{U\Subset V(G)}\lambda_c(G[U])$, where $\lambda_c(G[U])=\sup\{t\ge0: Z_{G[W]}(-t\mathbf 1)>0\text{ for every }W\subseteq U\}$. The **memory-$q$ threshold** is $\lambda_q(G,\prec)=R_q(\mathcal R^{\mathrm{ind},\prec})$. `indState v` is the one-site history $(v)$, the memory-zero state at $v$.
--
--   **Formalization Note.** Neighbor orders are ranks `rank v : V → ℕ` injective on $N(v)$. $C_n$ is Mathlib's `SimpleGraph.cycleGraph n` on `Fin n`. Thresholds are in `ℝ≥0∞` (for $V=\emptyset$ both are $+\infty$).
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), §1 and (1.1), printed p. 1 (PDF p. 3); App. E.1 (E.1)–(E.4), printed p. 31 (PDF p. 33); App. E.2 (E.7)–(E.9), printed p. 32 (PDF p. 34)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

variable {V : Type}

open Classical in
/-- The multivariate **independence polynomial** of the induced subgraph `G[U]` of a finite region
`U` (§1 and (E.1)): `Ind_{G[U]}(z) = ∑_{I ⊆ U independent} ∏_{v ∈ I} z_v` (the empty set counts). -/
noncomputable def indepPoly (G : SimpleGraph V) (U : Finset V) : MvPolynomial V ℝ :=
  ∑ I ∈ U.powerset.filter (fun I : Finset V => G.IsIndepSet (I : Set V)), ∏ v ∈ I, MvPolynomial.X v

open Classical in
/-- The edges of the induced subgraph `G[U]`, as unordered pairs. -/
noncomputable def edgesIn (G : SimpleGraph V) (U : Finset V) : Finset (Sym2 V) :=
  ((U ×ˢ U).image (fun x => s(x.1, x.2))).filter (fun e => e ∈ G.edgeSet)

/-- A set of edges is a **matching**: distinct edges share no vertex. -/
def IsMatchingSet (M : Finset (Sym2 V)) : Prop :=
  ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → ∀ x : V, x ∈ e → x ∉ e'

open Classical in
/-- The multivariate **matching polynomial** of `G[U]` (E.7):
`Match_{G[U]}(z) = ∑_{M matching of G[U]} ∏_{e ∈ M} z_e`. -/
noncomputable def matchPoly (G : SimpleGraph V) (U : Finset V) : MvPolynomial (Sym2 V) ℝ :=
  ∑ M ∈ (edgesIn G U).powerset.filter IsMatchingSet, ∏ e ∈ M, MvPolynomial.X e

/-- A fixed choice of **neighbor orders** (§1, (E.3)): a total order `≺_v` on the neighborhood
`N(v)` of every vertex, encoded by a rank `rank v : V → ℕ` injective on `N(v)`
(`w ≺_v u ↔ rank v w < rank v u`). -/
structure NeighborOrders (G : SimpleGraph V) where
  rank : V → V → ℕ
  rank_injOn : ∀ v, Set.InjOn (rank v) (G.neighborSet v)

/-- The **independent-set representation** `R^{ind,≺}` (App. E.1): one option per vertex, with
`A_v = {v}`, `D_v = N_G[v]`, `c_v = 1`, `τ(v) = v`, and the neighbor order `≺_v` on
`D_v \ {v} = N_G(v)`. -/
noncomputable def indRep (G : SimpleGraph V) [G.LocallyFinite] (o : NeighborOrders G) :
    PosLocalDeletionRep V V where
  Opt := fun _ => Unit
  optFintype := fun _ => inferInstance
  A := fun v _ => {v}
  D := fun v _ => by classical exact insert v (G.neighborFinset v)
  self_mem_A := fun v _ => Finset.mem_singleton_self v
  A_subset_D := fun v _ => by
    classical
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
  c := fun _ _ => 1
  c_pos := fun _ _ => one_pos
  cstar_pos := ⟨1, one_pos, fun _ _ => le_rfl⟩
  label := fun v _ => v
  rank := fun v _ => o.rank v
  rank_injOn := fun v _ => by
    classical
    refine (o.rank_injOn v).mono ?_
    intro w hw
    simp only [Set.mem_sdiff, Finset.mem_coe, Finset.mem_insert, Set.mem_singleton_iff] at hw
    rcases hw with ⟨h1 | h1, h2⟩
    · exact absurd h1 h2
    · simpa using h1

/-- The **matching representation** (App. E.2): the options at `v` are the incident edges
`e = {v, u}`, with `A_{v,e} = D_{v,e} = e`, `c_{v,e} = 1`, `τ(v,e) = e`. Each option has one factor,
so its local order is trivial (constant rank). -/
noncomputable def matchRep (G : SimpleGraph V) [G.LocallyFinite] :
    PosLocalDeletionRep V (Sym2 V) where
  Opt := fun v => G.neighborFinset v
  optFintype := fun _ => inferInstance
  A := fun v u => by classical exact {v, (u : V)}
  D := fun v u => by classical exact {v, (u : V)}
  self_mem_A := fun v _ => by classical exact Finset.mem_insert_self _ _
  A_subset_D := fun _ _ => le_rfl
  c := fun _ _ => 1
  c_pos := fun _ _ => one_pos
  cstar_pos := ⟨1, one_pos, fun _ _ => le_rfl⟩
  label := fun v u => s(v, (u : V))
  rank := fun _ _ _ => 0
  rank_injOn := fun v u => by
    classical
    intro w hw w' hw' _
    simp only [Set.mem_sdiff, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton,
      Set.mem_singleton_iff] at hw hw'
    rcases hw with ⟨h1 | h1, h2⟩
    · exact absurd h1 h2
    rcases hw' with ⟨h1' | h1', h2'⟩
    · exact absurd h1' h2'
    rw [h1, h1']

/-- The **uniform Shearer threshold** (1.1): `λ_c(G) = inf_{U ⋐ V(G)} λ_c(G[U])`, where for a finite
region `λ_c(G[U]) = sup{t ≥ 0 : Z_{G[W]}(−t·1) > 0 for every W ⊆ U}` (Shearer's condition on
`G[U]` at the common probability `t`), in `[0, ∞]`. -/
noncomputable def shearerThreshold (G : SimpleGraph V) : ℝ≥0∞ :=
  ⨅ U : Finset V, ⨆ (t : ℝ≥0) (_ : ∀ W ⊆ U,
      0 < MvPolynomial.eval (fun _ => -(t : ℝ)) (indepPoly G W)), (t : ℝ≥0∞)

/-- The memory-`q` threshold of a graph with fixed neighbor orders:
`λ_q(G, ≺) = R_q(R^{ind,≺})` (App. E.1). -/
noncomputable def lambdaQ (G : SimpleGraph V) [G.LocallyFinite] (o : NeighborOrders G) (q : ℕ) :
    ℝ≥0∞ :=
  memRadius (indRep G o) q

/-- The one-site history `(v)` of the independent-set representation: the memory-zero state at `v`. -/
def indState (G : SimpleGraph V) [G.LocallyFinite] (o : NeighborOrders G) (v : V) :
    Hist (indRep G o) :=
  ⟨v, []⟩

end LocalLemmaHierarchy.Completeness


