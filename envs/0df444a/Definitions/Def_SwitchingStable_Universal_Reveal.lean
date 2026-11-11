-- Prove2me | Definitions.Def_SwitchingStable_Universal_Reveal
-- name    : SwitchingStable_Universal_Reveal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:31.081992+00:00
-- url     : https://prove2.me/theorems/25f4ecbe-1543-4c08-9738-60a326ce1324
-- title:
--   Independent reveal priorities, geometric extensions and logarithmic savings
-- statement:
--   For a fixed stable matching and coordinate $u$, sample independent uniform priorities on $[0,1]$ for the men and a separate countable supply of auxiliary marks. A mark is present if its priority is below $T_u$. Distances $A,B$ to the first marks extend the finite stable lists independently. Genuine endpoints and marked unchanged-edge witnesses reduce those distances to $a,b$. Define
--   $$S_R=\log\frac{A+B-1}{A+b-1},\quad S_L=\log\frac{A+B-1}{a+B-1},\quad S=\log\frac{A+B-1}{a+b-1},\quad J=S-S_R-S_L.$$
--   For a cut at layer $k$, its elementary term is $F_k=\mathbf1_{E_k}\log((A+k)/(A+k-1))$, where its witness is marked and the first $k$ directional positions are unmarked. The left counterpart exchanges the two sides. Auxiliary endpoint witnesses use distinct marks and impose no new matching condition.
--
--   The same file defines conditional coordinate supports, revealed predecessors, and the exact bounds $L,R$. Expectations are integrals under the actual product law. Infinite runs use a total default only on the null complement of the explicitly defined successful-run event.
--
--   A genuine supplier for layer $k$ must witness an actual positive boundary $j\le k$. This permits the source’s reuse of a closer cap for a later elementary layer; an endpoint auxiliary instead requires the finite endpoint to supply that layer’s cap.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), pp. 2–4, 7–9, 15, 20–24, PDF pp. 3–5, 8–10, 16, 21–25, Sections 2, 4 and Appendices B, D

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Model
import Definitions.Def_SwitchingStable_Universal_Constants

namespace SwitchingStable.Universal

open MeasureTheory StableMatching
variable {n : ℕ}

/-- Independent continuous priorities, also used to generate all auxiliary marks. -/
noncomputable def unitLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)
instance unitLaw_probability : IsProbabilityMeasure unitLaw := ⟨by simp [unitLaw]⟩
abbrev Sample (n : ℕ) := (Fin n ⊕ ℕ) → ℝ
noncomputable def revealLaw (n : ℕ) : Measure (Sample n) :=
  Measure.infinitePi (fun _ => unitLaw)
def auxiliaryIndex (ε : Direction) (k : ℕ) (witness : Bool) : ℕ :=
  4 * k + (if ε = .right then 0 else 2) + (if witness then 1 else 0)
noncomputable def positionLabel (I : Instance n) (μ : Matching n) (u : Fin n)
    (ε : Direction) (k : ℕ) : Fin n ⊕ ℕ :=
  if k ≤ distance I μ u ε then Sum.inl (owner I μ ε u k)
  else Sum.inr (auxiliaryIndex ε k false)
def marked (u : Fin n) (t : Sample n) (label : Fin n ⊕ ℕ) : Prop :=
  t label < t (Sum.inl u)
/-- The default on an infinite run is excluded by Good and shown null in theorems. -/
noncomputable def firstMark (I : Instance n) (μ : Matching n) (u : Fin n)
    (ε : Direction) (t : Sample n) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, marked u t (positionLabel I μ u ε (k + 1))
    then Nat.find h + 1 else 1
noncomputable def Good (I : Instance n) (μ : Matching n) (u : Fin n) (t : Sample n) : Prop :=
  (∃ k : ℕ, marked u t (positionLabel I μ u .right (k + 1))) ∧
  (∃ k : ℕ, marked u t (positionLabel I μ u .left (k + 1)))
/-- Cuts are real unchanged-edge witnesses or fresh auxiliary endpoint witnesses. -/
structure Cut (n : ℕ) where
  layer : ℕ
  supplier : Fin n ⊕ ℕ
  deriving DecidableEq
noncomputable def ValidCut (I : Instance n) (μ : Matching n) (u : Fin n)
    (ε : Direction) (c : Cut n) : Prop :=
  1 ≤ c.layer ∧ match c.supplier with
  | .inl h => ∃ j : ℕ, j ≤ c.layer ∧ Witness I μ ε u h j
  | .inr a => distance I μ u ε < c.layer ∧
      ∀ (s : Direction) (j : ℕ), a ≠ auxiliaryIndex s j false
noncomputable def cap (I : Instance n) (μ : Matching n) (u : Fin n) (ε : Direction)
    (cuts : Finset (Cut n)) (t : Sample n) : ℕ := by
  classical
  let caps := insert (distance I μ u ε + 1)
    ((cuts.filter fun c => marked u t c.supplier).image Cut.layer)
  exact min (firstMark I μ u ε t) (caps.min' (by simp [caps]))

noncomputable def saving (I : Instance n) (μ : Matching n) (u : Fin n) (ε : Direction)
    (cuts : Finset (Cut n)) (t : Sample n) : ℝ :=
  let A : ℝ := firstMark I μ u ε.reverse t
  let B : ℝ := firstMark I μ u ε t
  let b : ℝ := cap I μ u ε cuts t
  Real.log ((A + B - 1) / (A + b - 1))
noncomputable def jointSaving (I : Instance n) (μ : Matching n) (u : Fin n)
    (right left : Finset (Cut n)) (t : Sample n) : ℝ :=
  Real.log (((firstMark I μ u .right t : ℝ) + firstMark I μ u .left t - 1) /
    ((cap I μ u .right right t : ℝ) + cap I μ u .left left t - 1))
noncomputable def interaction (I : Instance n) (μ : Matching n) (u : Fin n)
    (right left : Finset (Cut n)) (t : Sample n) : ℝ :=
  jointSaving I μ u right left t - saving I μ u .right right t - saving I μ u .left left t
noncomputable def eventTerm (I : Instance n) (μ : Matching n) (u : Fin n)
    (ε : Direction) (c : Cut n) (t : Sample n) : ℝ := by
  classical
  exact if marked u t c.supplier ∧
    ∀ k ∈ Finset.Icc 1 c.layer, ¬ marked u t (positionLabel I μ u ε k) then
    Real.log (((firstMark I μ u ε.reverse t : ℝ) + c.layer) /
      ((firstMark I μ u ε.reverse t : ℝ) + c.layer - 1)) else 0
noncomputable def expected (f : Sample n → ℝ) : ℝ := ∫ t, f t ∂revealLaw n
noncomputable def legalCuts (I : Instance n) (μ : Matching n) (u : Fin n)
    (ε : Direction) (cuts : Finset (Cut n)) : Prop :=
  ∀ c ∈ cuts, ValidCut I μ u ε c
/-- A layer witness is distinct from every position mark in its elementary event.
Auxiliary witnesses use the separate odd mark stream. -/
noncomputable def Elementary (I : Instance n) (μ : Matching n) (u : Fin n)
    (ε : Direction) (c : Cut n) : Prop :=
  ValidCut I μ u ε c ∧
    c.supplier ≠ Sum.inl u ∧
    (∀ k ∈ Finset.Icc 1 c.layer, c.supplier ≠ positionLabel I μ u ε k)
/-- All genuine witness cuts, so local estimates use actual unchanged-edge implications. -/
noncomputable def allCuts (I : Instance n) (μ : Matching n) (u : Fin n)
    (ε : Direction) : Finset (Cut n) := by
  classical
  exact (Finset.Icc 1 (degree I u)).biUnion fun j =>
    ((Finset.univ.filter fun h => Additional I μ ε u h j).image fun h =>
      (⟨j, .inl h⟩ : Cut n))


/-- Coordinate supports for arbitrary finite vector families; no algorithm-output restriction. -/
noncomputable def coordinateSupport {U V : Type} [Fintype U] [DecidableEq U] [DecidableEq V]
    (S : Finset (U → V)) (z : U → V) (P : Finset U) (u : U) : Finset V := by
  classical
  exact (S.filter fun y => ∀ p ∈ P, y p = z p).image fun y => y u
noncomputable def predecessors (u : Fin n) (t : Sample n) : Finset (Fin n) :=
  Finset.univ.filter fun p => t (.inl p) < t (.inl u)
noncomputable def supportSize (I : Instance n) (μ : Matching n) (u : Fin n)
    (P : Finset (Fin n)) : ℕ := by
  classical
  exact ((Finset.univ.filter fun ν : Matching n => I.IsStable ν ∧ ∀ p ∈ P, ν p = μ p).image
    fun ν => ν u).card
noncomputable def leftBoundary (I : Instance n) (μ : Matching n) (u : Fin n)
    (P : Finset (Fin n)) : ℤ :=
  let lower : Finset ℕ := (Finset.range (idx I μ u)).filter
    fun r : ℕ => μ.symm (atPartner I μ u (Int.ofNat r)) ∈ P
  ((lower.sup (fun r : ℕ => r + 1) : ℕ) : ℤ) - 1
noncomputable def rightBoundary (I : Instance n) (μ : Matching n) (u : Fin n)
    (P : Finset (Fin n)) : ℤ :=
  let upper : Finset ℤ := ((Finset.range (degree I u)).filter
    fun r : ℕ => idx I μ u < r ∧ μ.symm (atPartner I μ u (Int.ofNat r)) ∈ P).image Int.ofNat
  (insert (degree I u : ℤ) upper).min' (by simp)

end SwitchingStable.Universal


