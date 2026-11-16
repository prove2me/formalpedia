-- Prove2me | Definitions.Def_KoanaKPaths_Main_Supplement_Packings
-- name    : KoanaKPaths_Main_Supplement_Packings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:30:01.797972+00:00
-- url     : https://prove2.me/theorems/c649c06c-14a3-4a17-8db2-0df4cf0be626
-- title:
--   Finite uniform set families, packing count and binary input
-- statement:
--   A **uniform set family** is given as a list $E=(E_0,\ldots,E_{m-1})$ of distinct finite sets, each with exactly $d$ elements, where $d,k\ge1$ and $m\ge k$. Its **packing count** is
--   $$
--   \operatorname{packingCount}(E,k)=\left|\left\{I\subseteq\{0,\ldots,m-1\}: |I|=k,\ E_i\cap E_j=\varnothing\text{ for all distinct }i,j\in I\right\}\right|.
--   $$
--   It counts unordered subfamilies, including a zero count. Natural labels represent an arbitrary finite ground union injectively; no bound on the original universe is imposed. Distinct subfamilies remain distinct even if they have the same union.
--
--   The block word of a set lists its labels increasingly. The family code writes its list length and each increasing block with its length, using the published self-delimiting binary natural-number code. The compiler input is $d,k,E$; the counting input appends the finite controls $a=\lceil\log_2(1/\varepsilon)\rceil$ and $b=\lceil\log_2(1/\delta)\rceil$. The polynomial input-size factor uses only the family code length $L$, excluding both controls. Every binary label length is charged. These objects supply the instance and count for the set-packing reduction.
-- source:
--   Tomohiro Koana, STOC 2027 submission #953 (October 2026), p. 10 (PDF p. 11), Section 4.2, definition of k-packing and proof of Theorem 3; binary encoding convention as in the published Inputs/Machine interfaces

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_KoanaKPaths_Main_Inputs

open HypergraphUnreliability.FPRAS
open scoped Classical

namespace KoanaKPaths.Main.Supplement

/-- The explicit source input: distinct sets of the same positive cardinality, with at least
`k ≥ 1` members. Natural labels encode an arbitrary finite ground union injectively. -/
def ValidFamily (E : List (Finset ℕ)) (d k : ℕ) : Prop :=
  1 ≤ d ∧ 1 ≤ k ∧ k ≤ E.length ∧ E.Nodup ∧ ∀ S ∈ E, S.card = d

/-- Unordered index subfamilies. Equal unions do not identify different subfamilies. -/
noncomputable def packingCount (E : List (Finset ℕ)) (k : ℕ) : ℕ :=
  (((Finset.range E.length).powersetCard k).filter fun I =>
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (E.getD i ∅) (E.getD j ∅)).card

/-- The chosen order within a block is increasing ground-element order. -/
def blockWord (S : Finset ℕ) : List ℕ := S.sort (· ≤ ·)

/-- The family alone, with every length and every binary label charged. -/
def familyCode (E : List (Finset ℕ)) : List Bool :=
  listCode (fun S => listCode natCode (blockWord S)) E

/-- Deterministic compiler input; neither tolerance control occurs here. -/
def packingData (E : List (Finset ℕ)) (d k : ℕ) : List Bool :=
  natCode d ++ natCode k ++ familyCode E

/-- Finite input with arbitrary natural controls, in self-delimiting order. -/
def packingControlInput (E : List (Finset ℕ)) (d k a b : ℕ) : List Bool :=
  packingData E d k ++ natCode a ++ natCode b

/-- All real tolerances are specified via the same published ceiling controls. -/
noncomputable def packingInput (E : List (Finset ℕ)) (d k : ℕ) (ε δ : ℝ) : List Bool :=
  packingControlInput E d k (ctrl ε) (ctrl δ)

end KoanaKPaths.Main.Supplement


