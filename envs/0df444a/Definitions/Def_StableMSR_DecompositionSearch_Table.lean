-- Prove2me | Definitions.Def_StableMSR_DecompositionSearch_Table
-- name    : StableMSR_DecompositionSearch_Table
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-14T18:04:46.231392+00:00
-- url     : https://prove2.me/theorems/f82ba3cb-7724-4a43-8d29-c980d59d1c46
-- title:
--   Finite tight-block state tables and size-ordered evaluation
-- statement:
--   For a finite graph $G$ and width bound $w$, enumerate boundary sets of cardinality at most $w$, their nonempty components with exact external boundary, and candidate bags of cardinality at most $w+1$ that introduce at least one interior vertex. A synchronous table tests each state against the preceding table. A size-ordered table instead processes states with $m+1$ interior vertices in layer $m$, retaining earlier accepted states. Recognition tests all initial graph components at the final size threshold $n=|V(G)|$. The enumeration tally counts one visit per state, one eligibility test per bounded bag, and one table probe per child of an eligible bag. It excludes component construction, boundary computation, indexing, and arithmetic costs.
-- source:
--   Finite search recurrence supporting the Exact Sum-of-Radii Clustering under Any Constant Stability mission; follows the proved finite_decomposition_search theorem d4f2a14a-b18f-44f7-966a-d1411797cf17.

import Definitions.Def_StableMSR_DecompositionSearch_Recurrence
open scoped Classical BigOperators
namespace StableMSR.Recovery.DecompositionSearch
variable {V : Type} [Fintype V] [DecidableEq V]
noncomputable def smallSets (w : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun S => S.card ≤ w)


noncomputable def searchStates (G : SimpleGraph V) (w : ℕ) : Finset (Finset V × Finset V) :=
  (smallSets w).biUnion (fun S =>
    ((PartialDecompositions.components G S).filter (fun C => boundary G C = S)).image
      (fun C => (S,C)))


noncomputable def candidateBags (w : ℕ) (S C : Finset V) : Finset (Finset V) :=
  (smallSets (w+1)).filter (fun B => S ⊆ B ∧ B ⊆ S ∪ C ∧ (B ∩ C).Nonempty)


noncomputable def tableStep (G : SimpleGraph V) (w : ℕ)
    (table : Finset (Finset V × Finset V)) : Finset (Finset V × Finset V) :=
  (searchStates G w).filter (fun p => ∃ B ∈ candidateBags w p.1 p.2,
    ∀ D ∈ children G B p.2,
      (boundary G D).card ≤ w ∧ (boundary G D,D) ∈ table)


noncomputable def tabulate (G : SimpleGraph V) (w : ℕ) :
    ℕ → Finset (Finset V × Finset V)
  | 0 => ∅
  | m+1 => tableStep G w (tabulate G w m)


noncomputable def tableRecognizes (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∀ C ∈ PartialDecompositions.components G ∅,
    (∅,C) ∈ tabulate G w (Fintype.card V)


noncomputable def layerStates (G : SimpleGraph V) (w m : ℕ) :
    Finset (Finset V × Finset V) :=
  (searchStates G w).filter (fun p => p.2.card = m+1)


noncomputable def sizeTable (G : SimpleGraph V) (w : ℕ) :
    ℕ → Finset (Finset V × Finset V)
  | 0 => ∅
  | m+1 => sizeTable G w m ∪
      (layerStates G w m).filter (fun p => ∃ B ∈ candidateBags w p.1 p.2,
        ∀ D ∈ children G B p.2,
          (boundary G D).card ≤ w ∧ (boundary G D,D) ∈ sizeTable G w m)


noncomputable def sizeTableRecognizes (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∀ C ∈ PartialDecompositions.components G ∅,
    (∅,C) ∈ sizeTable G w (Fintype.card V)


noncomputable def enumerationVisits (G : SimpleGraph V) (w : ℕ) : ℕ :=
  ∑ p ∈ searchStates G w,
    (1 + (smallSets (V := V) (w+1)).card +
      ∑ B ∈ candidateBags w p.1 p.2, (children G B p.2).card)

end StableMSR.Recovery.DecompositionSearch


