-- Prove2me | Definitions.Def_HypercliqueCircuits_Circuits_Supplement_Counting
-- name    : HypercliqueCircuits_Circuits_Supplement_Counting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:10:10.022401+00:00
-- url     : https://prove2.me/theorems/cd271392-0315-437a-96c5-37d215b21cd1
-- title:
--   Unordered hyperclique counts and dense hypergraph inputs
-- statement:
--   Let $H$ be an $h$-uniform hypergraph on $[n]$, using the published hypergraph and hyperclique predicates. Define
--
--   $$\operatorname{cliqueCount}(H,k)=\#\{S\subseteq[n]: |S|=k,\ \forall T\subseteq S,\ |T|=h\Rightarrow T\in E(H)\}.$$
--
--   This counts vertex sets, including a single copy of each clique. The input is $n$ followed by the indicator of the hyperedge set on all tuples in $[n]^h$, in mixed-radix order. Repeated coordinates have indicator zero because their image has fewer than $h$ elements. The hypergraph definitions are reused without changing their carrier, uniformity convention, or subset predicate. This interface distinguishes the desired count from the ordered-tuple evaluation, which is $k!$ times larger when $h=k-1\ge2$.
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, p.2, Theorem 2 (PDF 3); §4.1 proof p.24 (PDF 25)

import Definitions.Def_HypercliqueCircuits_Circuits_Supplement_Encoding
import Definitions.Def_HypercliqueFalse_Hypergraph
import Definitions.Def_HypercliqueFalse_IsHyperclique
import Definitions.Def_HypercliqueFalse_edgeIndicator

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits.Supplement

/-- Counts vertex SETS, not the ordered tuples counted by the polynomial.
Alman et al., Theorem 2, printed pp.2,24 / PDF pp.3,25. -/
noncomputable def cliqueCount {n h : ℕ} (H : HypercliqueFalse.Hypergraph n h)
    (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (HypercliqueFalse.IsHyperclique H k)).card

/-- Dense h-tuple indicator; repeated coordinates have indicator zero.
No copy of the answer, circuit, or reduction is part of the input. -/
def countingInput {n h : ℕ} (H : HypercliqueFalse.Hypergraph n h) : List (Cell Empty) :=
  words (n :: (tuples h n).map (fun y => (HypercliqueFalse.edgeIndicator H y).toNat))

end HypercliqueCircuits.Circuits.Supplement


