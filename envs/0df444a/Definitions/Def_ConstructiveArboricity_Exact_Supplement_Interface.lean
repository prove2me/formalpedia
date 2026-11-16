-- Prove2me | Definitions.Def_ConstructiveArboricity_Exact_Supplement_Interface
-- name    : ConstructiveArboricity_Exact_Supplement_Interface
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:12:13.450947+00:00
-- url     : https://prove2.me/theorems/1c895806-fe02-46c2-ab00-03228dfaad6c
-- title:
--   Supplied orientation and star inputs; global partition outputs
-- statement:
--   A finite simple graph uses the published edge identities and retains isolated vertices. An orientation input consists of the graph's endpoint list, a bound $k$, and one tail vertex per edge. A star input specifies a vertex $r$ and a color for every edge outside the star at $r$; exactly the star edges have color $-1$. Every old color fiber is a forest. Empty color classes are implicit.
--
--   A decision output is either $[0]$, which certifies nonexistence of any $k$-forest partition, or $[1,k,c_0,\ldots,c_{m-1}]$, where the colors partition all edges into forests. The number $Z$ counts cyclic components once in each supplied pseudoforest. These interfaces share the published graph and RAM definitions.
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. §§2–5 and Appendix A, definition interface, PDF/printed p.7.

import Definitions.Def_ConstructiveArboricity_Exact_Machine

/-! Supplied inputs and outputs for §§3–5 of Gholami et al., STOC 2027 submission
#1476 (October 2026), pp.7–8, 14, 27–29. No execution or complexity assumption
is part of an input. Forest classes with no edges require no storage. -/
namespace ConstructiveArboricity.Exact.Supplement

noncomputable section
open Classical

def orientationInput (G : Graph) (k : ℕ) (tail : Fin G.m → Fin G.n) : List ℤ :=
  G.input ++ [(k : ℤ)] ++ List.ofFn (fun e => ((tail e).val : ℤ))

def coloringInput (G : Graph) (k : ℕ) (c : Fin G.m → Fin k) : List ℤ :=
  G.input ++ [(k : ℤ)] ++ List.ofFn (fun e => ((c e).val : ℤ))

def totalCycles (G : Graph) {k : ℕ} (c : Fin G.m → Fin k) : ℕ :=
  ∑ i, G.cycleCount {e | c e = i}

def starEdges (G : Graph) (r : Fin G.n) : Finset (Fin G.m) :=
  Finset.univ.filter fun e => (G.ends e).1 = r ∨ (G.ends e).2 = r

/-- The old partition, including exactly the uncolored star edges. -/
structure StarInput (G : Graph) (k : ℕ) (r : Fin G.n) where
  color : Fin G.m → Option (Fin k)
  uncolored : ∀ e, color e = none ↔ e ∈ starEdges G r
  forests : ∀ i, G.IsForest {e | color e = some i}

def starInput (G : Graph) (k : ℕ) (r : Fin G.n) (a : StarInput G k r) : List ℤ :=
  G.input ++ [(k : ℤ), (r.val : ℤ)] ++ List.ofFn (fun e =>
    match a.color e with | none => -1 | some i => (i.val : ℤ))

/-- A global decision: rejection excludes every possible recoloring. -/
def decisionOutput (G : Graph) (k : ℕ) (out : List ℤ) : Prop :=
  (out = [0] ∧ ¬ G.Feasible k) ∨
  ∃ c, G.ForestPartition k c ∧ out = 1 :: G.partitionOutput k c

end
end ConstructiveArboricity.Exact.Supplement


