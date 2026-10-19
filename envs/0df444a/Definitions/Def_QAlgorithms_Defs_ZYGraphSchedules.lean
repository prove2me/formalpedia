-- Prove2me | Definitions.Def_QAlgorithms_Defs_ZYGraphSchedules
-- name    : QAlgorithms_Defs_ZYGraphSchedules
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:42:19.199982+00:00
-- url     : https://prove2.me/theorems/998cffec-a360-4a22-bbc9-5e3a4a3b6434
-- title:
--   ZYGraphSchedules
-- statement:
--   ZYGraphSchedules
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ZYGraphSchedules.lean

import Definitions.Def_QAlgorithms_Defs_QAOA
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.ZY

/-- Assign exactly one direction to each edge of a finite simple graph, with no extra directed edges. Arbitrary orientations form the competitor class. Acyclicity is separate, e.g. existence of an injective vertex rank strictly ordered along each arrow. Source: arxiv-2504.12896v4 PDF p.3. -/
structure Orientation {N : ℕ} (G : SimpleGraph (Fin N)) where
  arrow : Fin N → Fin N → Bool
  faithful : ∀ i j, G.Adj i j ↔ arrow i j = true ∨ arrow j i = true
  exclusive : ∀ i j, ¬ (arrow i j = true ∧ arrow j i = true)

/-- Implementation helper; source: arxiv-2504.12896v4 PDF p.3. -/
def directedEdges {N : ℕ} {G : SimpleGraph (Fin N)} (O : Orientation G) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun e => O.arrow e.1 e.2 = true

/-- Permutation/enumeration of every oriented graph edge exactly once, in chronological circuit order; left/right positions come from this list. It depends on the known graph, not the optimizing angle. Source: arxiv-2504.12896v4 PDF p.3. -/
structure GateSequence {N : ℕ} {G : SimpleGraph (Fin N)} (O : Orientation G) where
  edges : List (Fin N × Fin N)
  nodup : edges.Nodup
  exhaustive : edges.toFinset = directedEdges O

/-- Cardinality of vertices u whose unique edge orientation is u->v; computed from Orientation. Source: arxiv-2504.12896v4 PDF p.3. -/
def inDegree {N : ℕ} {G : SimpleGraph (Fin N)} (O : Orientation G) (v : Fin N) : ℕ :=
  (Finset.univ.filter fun u => O.arrow u v = true).card

/-- Cardinality of vertices u whose unique edge orientation is v->u; computed from Orientation. Source: arxiv-2504.12896v4 PDF p.3. -/
def outDegree {N : ℕ} {G : SimpleGraph (Fin N)} (O : Orientation G) (v : Fin N) : ℕ :=
  (Finset.univ.filter fun u => O.arrow v u = true).card

/-- NPlus=cardinality {v : inDegree(v)=0}, computed from Orientation. Source: arxiv-2504.12896v4 PDF p.3. -/
def sourceCount {N : ℕ} {G : SimpleGraph (Fin N)} (O : Orientation G) : ℕ :=
  (Finset.univ.filter fun v => inDegree O v = 0).card

/-- NMinus=cardinality {v : outDegree(v)=0}, computed from Orientation. Source: arxiv-2504.12896v4 PDF p.3. -/
def sinkCount {N : ℕ} {G : SimpleGraph (Fin N)} (O : Orientation G) : ℕ :=
  (Finset.univ.filter fun v => outDegree O v = 0).card

/-- Attained finite maximum of frozen cutValue G z over all bit strings z:Qubits N. This assignment set is always nonempty. The selected connected nonempty cubic graphs have C_max>0. Keep C_max distinct from M. Source: arxiv-2504.12896v4 PDF p.4. -/
def maximumCut {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (cutValue G)

example : maximumCut (⊤ : SimpleGraph (Fin 2)) = 1 := by decide

end QAlgorithms.ZY


