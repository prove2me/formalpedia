-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
-- name    : OAI_Combinatorics_GraphThreshold_GraphCopies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:17:16.171418+00:00
-- url     : https://prove2.me/theorems/aad23e0a-48ee-4dc8-8213-1bba02884a17
-- title:
--   Permutation orbits of an edge set correspond to unlabelled copies in $K_n$
-- statement:
--   Let $[n]=\{0,\dots,n-1\}$, let $K_n$ be the complete graph on $[n]$, and let $E_n$ be its set of edges (unordered pairs of distinct vertices). The symmetric group $S_n$ acts on subsets of $E_n$ by $\sigma\cdot S=\{\{\sigma(u),\sigma(v)\}:\ \{u,v\}\in S\}$. For $S\subseteq E_n$ let $K_S$ be the subgraph of $K_n$ with edge set $S$ and vertex set the endpoints of the edges of $S$, and let $\Gamma_S$ be $K_S$ regarded as a graph on its own vertex set; it has no isolated vertices.
--
--   1. **Orbit criterion.** For $S,T\subseteq E_n$,
--
--      $$T\in\{\sigma\cdot S:\ \sigma\in S_n\}\iff \Gamma_S\cong\Gamma_T .$$
--
--   2. **Orbits are unlabelled copies.** The map $T\mapsto K_T$ is a bijection from the orbit $\{\sigma\cdot S:\ \sigma\in S_n\}$ (a set of distinct edge sets) onto the set of subgraphs $K$ of $K_n$ such that $\Gamma_S\cong K$, with $K$ regarded as a graph on its own vertex set. The inverse sends $K$ to its edge set. This includes $S=\emptyset$, whose orbit is $\{\emptyset\}$ and whose only copy is the subgraph with no vertices.
--
--   Consequently the number of distinct edge sets in the $S_n$-orbit of $S$ equals the number of unlabelled copies of $\Gamma_S$ in $K_n$. This identifies the orbit counts of the general group-action framework (copies of a finite set under a finite group) with unlabelled copy counts, in $K_n$, of graphs without isolated vertices, and so connects the abstract argument about spread families of sets to copies of graphs in the random graph $G(n,p)$.
--
--   **Formalization Note** Item 1 is `mem_copyOrbit_iff_edgeSupportGraph_iso`, with the orbit `copyOrbit (Equiv.Perm (Fin n)) S`; item 2 is `orbitSubgraphEquiv S`, whose target is the subtype of `(⊤ : SimpleGraph (Fin n)).Subgraph` with `Nonempty (edgeSupportGraph S ≃g K.coe)`; there `edgeSupportGraph S` is $\Gamma_S$ and $K_T$ is `edgeSubgraph T`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/GraphCopies.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/GraphCopies.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SecondKahnKalai mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies

namespace OAI

noncomputable section

open scoped Pointwise

namespace LeanBlast.SecondKahnKalai

variable {n : ℕ}

theorem mem_copyOrbit_iff_edgeSupportGraph_iso {S T : Finset (Edge n)} :
    T ∈ copyOrbit (Equiv.Perm (Fin n)) S ↔
      Nonempty (edgeSupportGraph S ≃g edgeSupportGraph T) := by
  rw [mem_copyOrbit_iff]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨edgeSupportGraph_smulIso σ S⟩
  · rintro ⟨e⟩
    exact exists_smul_eq_of_edgeSupportGraph_iso e

/-- Distinct edge orbits correspond bijectively to actual unlabelled subgraphs.
The target has no isolated vertices, so its image subgraph is uniquely determined
by its edges. This also covers the empty graph, with its empty vertex set. -/
def orbitSubgraphEquiv (S : Finset (Edge n)) :
    OrbitCopy (Equiv.Perm (Fin n)) S ≃
      {K : (⊤ : SimpleGraph (Fin n)).Subgraph //
        Nonempty (edgeSupportGraph S ≃g K.coe)} where
  toFun T := ⟨edgeSubgraph T.val, mem_copyOrbit_iff_edgeSupportGraph_iso.mp T.property⟩
  invFun K := ⟨graphEdges K.val.spanningCoe, by
    apply mem_copyOrbit_iff_edgeSupportGraph_iso.mpr
    obtain ⟨e⟩ := K.property
    have hK := subgraph_eq_edgeSubgraph_of_iso K.val e
    change Nonempty (edgeSupportGraph S ≃g (edgeSubgraph _).coe)
    rw [← hK]
    exact ⟨e⟩⟩
  left_inv T := by
    apply Subtype.ext
    exact graphEdges_graphOfEdges T.val
  right_inv K := by
    apply Subtype.ext
    exact (subgraph_eq_edgeSubgraph_of_iso K.val K.property.some).symm

end LeanBlast.SecondKahnKalai

end

end OAI


