-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction
-- name    : OAI_Combinatorics_MatchingEntropy_Contraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:30:20.749023+00:00
-- url     : https://prove2.me/theorems/d3b3a0a3-0669-4faa-89a1-dac16cfb2a25
-- title:
--   Collapsing the complement of a vertex set to one new vertex
-- statement:
--   Let $V$ be a finite set and $S\subseteq V$. Form the set $S^\star=S\sqcup\{\star\}$ obtained from $S$ by adding one new point $\star$, which stands for the whole complement $V\setminus S$.
--
--   1. *Side map.* $\sigma_S:V\to S^\star$ sends a vertex of $S$ to itself and every other vertex to $\star$:
--   $$
--   \sigma_S(v)=\begin{cases}v,& v\in S,\\ \star,& v\notin S.\end{cases}
--   $$
--   In particular $\sigma_S(v)=v$ for every $v\in S$.
--   2. *Lifting vertex sets.* For $T\subseteq S^\star$, the lift of $T$ is its preimage
--   $$
--   \sigma_S^{-1}(T)=\{v\in V:\ \sigma_S(v)\in T\}\subseteq V,
--   $$
--   so $v$ belongs to the lift if and only if $\sigma_S(v)\in T$. Explicitly, the lift is $T$ itself when $\star\notin T$, and $(T\setminus\{\star\})\cup(V\setminus S)$ when $\star\in T$.
--
--   These are the vertex-level ingredients for shrinking one side $V\setminus S$ of a cut of a graph to a single vertex, a standard operation in cut-based arguments about matchings and matching polytopes. The lift translates a vertex set of the shrunken graph back into a vertex set of the original graph, so that cut conditions can be transferred between the two.
--
--   **Formalization Note** The side map is `sideMap S v : Option {v // v ∈ S}`, with `none` playing the role of $\star$, and the lift is `liftVertices S T : Finset V`; the simp lemmas `mem_liftVertices` and `sideMap_some` record the two displayed properties.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/Contraction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/Contraction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangleFace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def sideMap (S : Finset V) (v : V) : Option {v // v ∈ S} :=
  if h : v ∈ S then some ⟨v,h⟩ else none

def liftVertices (S : Finset V) (T : Finset (Option {v // v ∈ S})) : Finset V :=
  Finset.univ.filter (fun v => sideMap S v ∈ T)

@[simp] theorem mem_liftVertices (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (v : V) :
    v ∈ liftVertices S T ↔ sideMap S v ∈ T := by simp [liftVertices]

omit [Fintype V] in
@[simp] theorem sideMap_some (S : Finset V) (v : {v // v ∈ S}) :
    sideMap S v.val = some v := by
  simp [sideMap, v.property]

end MatchingEntropyBounds.LooplessGraph

end

end OAI


