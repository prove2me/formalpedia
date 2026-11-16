-- Prove2me | Definitions.Def_LowDiameterNashWilliams_Main_Supplement_SetCover
-- name    : LowDiameterNashWilliams_Main_Supplement_SetCover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:33:26.066836+00:00
-- url     : https://prove2.me/theorems/f2d954f1-95d3-4209-947a-aae7a5bbe173
-- title:
--   Set Cover validity, multiplicity, LP and replication
-- statement:
--   Reuse the published finite Set Cover instance: a universe of $u$ labelled points and an indexed list $S_1,\ldots,S_m$ of subsets, with repetitions permitted. Validity requires $u>0$, every listed set nonempty, and the union equal to the universe. Covers retain the published definition. Define the frequency $f(a)$ and attained optimum $\tau$ by
--   $$f(a)=|\{j:a\in S_j\}|,\qquad \tau=\min\{|J|:J\text{ covers the universe}\}.$$
--   The invalid no-cover fallback for the finite minimum is $m+1$; none of the theorem promises uses it. Bounded instances have set size and element frequency at most $B$. Frequent instances have $u\le m$ and element frequency at least $D$.
--
--   LP (4) is the feasibility condition $0\le x_j\le1$, $\sum_{j:a\in S_j}x_j\ge1$ for every point, and $\sum_jx_j\le\beta$. Define $r_j=\lceil Dx_j\rceil+1$, $M=D\beta+2m$, and the list containing $r_j$ copies of each set, padded to $M$ using the first set. Natural ceilings equal ordinary ceilings on the feasible domain. The infeasible-branch fixed instance has $q$ the largest even integer at most $\log_2D$, universe all $q/2$-subsets of $[q]$, and $\lceil2D/q\rceil$ copies of each incidence set $A_j=\{X:j\in X\}$.
--
--   The binary encoder lists the two dimensions and the full incidence matrix. Threshold inputs append the self-delimiting binary integer $\beta$, including zero. Validity, LP feasibility and all gaps are separate predicates; no hardness or replication inequality is stored as data.
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Section 7.2, p. 28 (PDF p. 29); Appendix A, LP (4) and Claims 6.1–6.3, pp. 33–35 (PDF pp. 34–36)

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Instance
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_GraphEncoding

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical

namespace LowDiameterNashWilliams.Main.Supplement

abbrev SCInstance := SetCoverThreshold.SetCover.SCInstance

/-- Section 7.2's precise validity conditions; repeated indexed sets remain allowed. -/
def ValidCover (I : SCInstance) : Prop :=
  0 < I.n ∧ (∀ S ∈ I.sets, S.Nonempty) ∧ I.Coverable

def frequency (I : SCInstance) (u : Fin I.n) : ℕ :=
  (Finset.univ.filter fun j : Fin I.sets.length => u ∈ I.sets.get j).card

/-- Finite attained minimum on coverable inputs; the invalid no-cover case is len+1. -/
noncomputable def coverNumber (I : SCInstance) : ℕ :=
  let cs := (Finset.univ : Finset (Fin I.sets.length)).powerset.filter I.IsCover
  let vals := cs.image Finset.card
  if h : vals.Nonempty then vals.min' h else I.sets.length + 1

def coverEncode (I : SCInstance) : List Bool :=
  natCode I.n ++ natCode I.sets.length ++
    I.sets.flatMap fun S => List.ofFn fun u : Fin I.n => decide (u ∈ S)

def BoundedCover (I : SCInstance) (B : ℕ) : Prop :=
  ValidCover I ∧ (∀ S ∈ I.sets, S.card ≤ B) ∧ ∀ u, frequency I u ≤ B

def FrequentCover (I : SCInstance) (D : ℕ) : Prop :=
  ValidCover I ∧ I.n ≤ I.sets.length ∧ ∀ u, D ≤ frequency I u

/-- The exact feasible LP (4), with real coordinates; no optimality or computational premise. -/
def FeasibleLP (I : SCInstance) (β : ℕ) (x : Fin I.sets.length → ℝ) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
  (∀ u, 1 ≤ ∑ j : Fin I.sets.length, if u ∈ I.sets.get j then x j else 0) ∧
  (∑ j : Fin I.sets.length, x j) ≤ β

noncomputable def replicationCount (D : ℕ) (x : ℝ) : ℕ := ⌈(D : ℝ) * x⌉₊ + 1

def replicationSize (I : SCInstance) (D β : ℕ) : ℕ := D * β + 2 * I.sets.length

/-- The feasible-branch output: retain the prescribed copies and pad by copies of the first set.
The fallback first set on an empty raw list is irrelevant on ValidCover inputs. -/
noncomputable def replicateCover (I : SCInstance) (D β : ℕ)
    (x : Fin I.sets.length → ℝ) : SCInstance :=
  let copies := (List.ofFn fun j : Fin I.sets.length =>
    List.replicate (replicationCount D (x j)) (I.sets.get j)).flatten
  ⟨I.n, copies ++ List.replicate (replicationSize I D β - copies.length) (I.sets.headD ∅)⟩

/-- Largest even integer at most log₂ D (on D>0). -/
def halfParameter (D : ℕ) : ℕ := 2 * (Nat.log 2 D / 2)

def halfSets (q : ℕ) : Finset (Finset (Fin q)) :=
  (Finset.univ : Finset (Fin q)).powersetCard (q / 2)

noncomputable def halfPoint (q : ℕ) (u : Fin (halfSets q).card) : Finset (Fin q) :=
  ((halfSets q).equivFin.symm u).val

/-- Exactly q blocks of r indexed copies of A_j={X : j∈X}; no validity or gap is asserted here. -/
noncomputable def fixedNoCover (D : ℕ) : SCInstance :=
  let q := halfParameter D
  let r := (2 * D + q - 1) / q
  ⟨(halfSets q).card, (List.ofFn fun j : Fin q =>
    List.replicate r (Finset.univ.filter fun u => j ∈ halfPoint q u)).flatten⟩

/-- Binary threshold is ordinary input data; beta=0 is retained. -/
structure ThresholdInput where
  cover : SCInstance
  beta : ℕ

def ThresholdInput.encode (I : ThresholdInput) : List Bool := coverEncode I.cover ++ natCode I.beta

end LowDiameterNashWilliams.Main.Supplement


