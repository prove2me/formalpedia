-- Prove2me | Definitions.Def_SwitchingStable_Universal_Transport
-- name    : SwitchingStable_Universal_Transport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:20.482858+00:00
-- url     : https://prove2.me/theorems/7615d162-2476-4575-a20d-6c739bf755ee
-- title:
--   Tail groups, transported layers, missing-layer counts and non-reuse
-- statement:
--   A group consists of a tail and the one- and two-swap predecessors whose prescribed maps reach that tail. Witnesses are chosen by the fixed ordering of the men before priorities are sampled. Actual changed edges determine the disjoint second- and third-boundary cases. Type $i$ and depth $r$ select the layer set
--   $$\{i,i+1,\ldots,i+r-1\}.$$
--   The file transports suppliers on unchanged edges, assigns the paper's depths, computes missing-layer counts, and defines a valid allocation. Its paid contributions and reserves are nonnegative integrable random variables satisfying
--   $$\text{selected elementary terms}+\text{paid contribution}+\text{reserve}\le\text{actual directional saving}$$
--   on every successful run. Existence of an allocation and its budgets is the conclusion of Lemma 17.
--
--   This representation makes the no-reuse condition explicit without assuming any desired saving bound.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), pp. 9–11, 24–28, PDF pp. 10–12, 25–29, Sections 4–5 and Appendices D–E

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Reveal
import Definitions.Def_SwitchingStable_Universal_Counts

namespace SwitchingStable.Universal
open StableMatching MeasureTheory
variable {n : ℕ}

/-- Fixed ordering for additional witnesses, before any priority is sampled. -/
noncomputable def chooseWitness (I : Instance n) (μ : Matching n) (ε : Direction)
    (u : Fin n) (k : ℕ) : Fin n := by
  classical
  let candidates := Finset.univ.filter fun h => Additional I μ ε u h k
  exact if h : candidates.Nonempty then candidates.min' h else u
noncomputable def realCut (k : ℕ) (h : Fin n) : Cut n := ⟨k, .inl h⟩
noncomputable def endpointCut (ε : Direction) (k : ℕ) : Cut n :=
  ⟨k, .inr (auxiliaryIndex ε k true)⟩
/-- Tail second row: retain h unless h is the second owner, then choose an outside witness. -/
noncomputable def secondCut (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Cut n := by
  classical
  let h := next I μ ε (next I μ ε u)
  exact if distance I μ u ε < 2 then endpointCut ε 2
    else realCut 2 (if owner I μ ε u 2 ≠ h then h else chooseWitness I μ ε u 2)
noncomputable def thirdCut (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Cut n :=
  if distance I μ u ε < 3 then endpointCut ε 3 else realCut 3 (chooseWitness I μ ε u 3)
noncomputable def HasE (I : Instance n) (ν : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  ∃ μ : Matching n, I.IsStable μ ∧ E I μ ε u ∧ ¬ Eadj I μ ε u ∧ swap I μ ε u = ν
noncomputable def HasW (I : Instance n) (ν : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  ∃ μ : Matching n, I.IsStable μ ∧ W I μ ε u ∧ swapTwice I μ ε u = ν
noncomputable def changedMen (I : Instance n) (ν : Matching n) (ε : Direction) (u : Fin n) : Finset (Fin n) := by
  classical
  exact (if HasE I ν ε u then {owner I ν ε.reverse u 1} else ∅) ∪
    (if HasW I ν ε u then {owner I ν ε.reverse u 2} else ∅)
noncomputable def ChangedSecond (I : Instance n) (ν : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  T0 I ν ε u ∧ ∃ h : Fin n, (secondCut I ν ε u).supplier = .inl h ∧ h ∈ changedMen I ν ε u
noncomputable def ChangedThird (I : Instance n) (ν : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  T0 I ν ε u ∧ ¬ ChangedSecond I ν ε u ∧ ¬ Failure I ν ε u ∧
    ∃ h : Fin n, (thirdCut I ν ε u).supplier = .inl h ∧ h ∈ changedMen I ν ε u
noncomputable def tailOf (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Matching n := by
  classical
  exact if E I μ ε u ∧ ¬ Eadj I μ ε u then swap I μ ε u
    else if W I μ ε u then swapTwice I μ ε u else μ
noncomputable def InGroup (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Prop :=
  (T0 I μ ε u ∨ (E I μ ε u ∧ ¬ Eadj I μ ε u) ∨ W I μ ε u) ∧
    T0 I (tailOf I μ ε u) ε u
noncomputable def depth (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : ℕ := by
  classical
  let ν := tailOf I μ ε u
  exact if occurrenceType I μ ε u = 0 then 0 else
    if InGroup I μ ε u then
      if ChangedSecond I ν ε u then 1 else if ChangedThird I ν ε u ∨ Failure I ν ε u then 2 else 3
    else if C0 I μ ε u ∧ ¬ Exceptional I μ ε u then 2 else 1
noncomputable def layers (i r : ℕ) : Finset ℕ := (Finset.range r).image (fun a => i + a)
noncomputable def selectedLayers (I : Instance n) (μ : Matching n) (ε : Direction)
    (u : Fin n) : Finset ℕ := layers (occurrenceType I μ ε u) (depth I μ ε u)
/-- Suppliers are transported on unchanged edges; the source layer number is shifted. -/
noncomputable def layerCut (I : Instance n) (μ : Matching n) (ε : Direction)
    (u : Fin n) (k : ℕ) : Cut n := by
  classical
  let i := occurrenceType I μ ε u
  let ν := tailOf I μ ε u
  let h := next I ν ε (next I ν ε u)
  exact if InGroup I μ ε u then
    if k = i then realCut k h
    else if k = i + 1 then ⟨k, (secondCut I ν ε u).supplier⟩
    else ⟨k, (thirdCut I ν ε u).supplier⟩
  else if distance I μ u ε < k then endpointCut ε k
  else if k = 1 then realCut k (next I μ ε (next I μ ε u))
  else if E I μ ε u then realCut k (next I μ ε (owner I μ ε u 2))
  else if W I μ ε u then realCut k (next I μ ε (owner I μ ε u 3))
  else realCut k (chooseWitness I μ ε u k)
noncomputable def selectedCuts (I : Instance n) (μ : Matching n) (ε : Direction)
    (u : Fin n) : Finset (Cut n) := by
  classical
  exact (selectedLayers I μ ε u).image (layerCut I μ ε u)
noncomputable def allocatedCuts (I : Instance n) (μ : Matching n) (ε : Direction)
    (u : Fin n) : Finset (Cut n) :=
  allCuts I μ u ε ∪ selectedCuts I μ ε u
noncomputable def layerSum (I : Instance n) (μ : Matching n) (u : Fin n) (ε : Direction)
    (cs : Finset (Cut n)) (t : Sample n) : ℝ := ∑ c ∈ cs, eventTerm I μ u ε c t
noncomputable def layerCost (i r : ℕ) : ℝ := ∑ a ∈ Finset.range r, delta (i+a)
noncomputable def selectedCost (I : Instance n) (μ : Matching n) (ε : Direction)
    (u : Fin n) : ℝ := layerCost (occurrenceType I μ ε u) (depth I μ ε u)
noncomputable def missingCount (I : Instance n) (ε : Direction) (row : ℕ) : ℕ :=
  count I (fun μ u => occurrenceType I μ ε u ≠ 0 ∧ depth I μ ε u < row)

/-- A verifiable allocation of actual saving. Paid contributions and reserves are nonnegative
and integrable, and their sum with actual selected terms is dominated pointwise. -/
def IsAllocation (I : Instance n) (ε : Direction)
    (paid reserve : Occurrence I → Sample n → ℝ) : Prop :=
  ∀ o : Occurrence I,
    Integrable (paid o) (revealLaw n) ∧ Integrable (reserve o) (revealLaw n) ∧
    (∀ t, 0 ≤ paid o t ∧ 0 ≤ reserve o t) ∧
    (∀ t, Good I o.1.val o.2 t →
      layerSum I o.1.val o.2 ε (selectedCuts I o.1.val ε o.2) t + paid o t + reserve o t ≤
        saving I o.1.val o.2 ε (allocatedCuts I o.1.val ε o.2) t)

end SwitchingStable.Universal


