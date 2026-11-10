-- Prove2me | Definitions.Def_GreedyColoringLCA969_LowerBound_Representation
-- name    : GreedyColoringLCA969_LowerBound_Representation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T09:43:20.628453+00:00
-- url     : https://prove2.me/theorems/d8b56a50-8839-46a3-83fb-349b1933c79a
-- title:
--   Finite represented graphs with arbitrary adjacency-list orders
-- statement:
--   A represented input is a finite simple graph $G$ on $n$ vertex identifiers together with an arbitrary ordering $L_v$ of each vertex's neighbors. Each $L_v$ lists exactly $N_G(v)$, with no repetitions:
--
--   $$L_v\text{ is a permutation of the finite neighbor set }N_G(v).$$
--
--   The general list structure is reused from the published definition bundle LocalProbeMIS871_Greedy_Model; only its unrestricted AdjacencyLists structure is used. Its rank-based MIS execution does not enter this model. An input consists of a size $n$, a graph, and these lists. All sizes and all list permutations are included, with the discrete measurable structure.
--
--   This countable input space permits arbitrary probability distributions, including distributions with infinite support or varying graph sizes. Empty inputs and isolated vertices are included. The structural countability instance is an injection into the finite family of lists at each size.
--
--   Differences from the source:
--   - encoding: vertex identifiers [n] and positive integer colors → Fin n with zero-based identifiers and positive-integer color type; reason: adding one is a bijection on vertex identifiers; colors remain exactly positive integers
--   - encoding: an input graph and its arbitrary ordered adjacency lists → a graph/list sigma type using a published permutation structure; reason: the reused structure carries no rank, degree, or algorithmic assumption
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), Definition 2.5, p.8 (PDF 9); Lemma 3.4 and Appendix A.2, pp.11,36–37 (PDF 12,37–38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/969.pdf

import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics
import Definitions.Def_LocalProbeMIS871_Greedy_Model

open scoped ENNReal
open MeasureTheory
open Classical

namespace GreedyColoringLCA969.LowerBound

/-- Definition 2.5: reuse the published unrestricted adjacency-list structure.
Only AdjacencyLists is used; none of the rank-based MIS execution is imported into our model. -/
abbrev Representation (n : ℕ) :=
  Σ G : SimpleGraph (Fin n), LocalProbeMIS871.Greedy.AdjacencyLists G

def Representation.graph {n : ℕ} (R : Representation n) : SimpleGraph (Fin n) := R.1

def Representation.val {n : ℕ} (R : Representation n) : Fin n → List (Fin n) := R.2.lists

instance adjacencyLists_countable {n : ℕ} (G : SimpleGraph (Fin n)) :
    Countable (LocalProbeMIS871.Greedy.AdjacencyLists G) :=
  Function.Injective.countable (f := fun L : LocalProbeMIS871.Greedy.AdjacencyLists G => L.lists) (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)

instance representation_countable (n : ℕ) : Countable (Representation n) := by
  unfold Representation
  infer_instance

/-- The countable input space includes all sizes and all list orders. -/
abbrev Input := Σ n : ℕ, Representation n

instance : MeasurableSpace Input := ⊤
instance : MeasurableSingletonClass Input := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

end GreedyColoringLCA969.LowerBound


