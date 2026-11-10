-- Prove2me | Definitions.Def_BMPV1173_Verification_Access
-- name    : BMPV1173_Verification_Access
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:06:42.175698+00:00
-- url     : https://prove2.me/theorems/89731d78-23b9-40f0-9f4b-ec2925997128
-- title:
--   Known sampled rows, record decoding and implicit-class states
-- statement:
--   The known side information contains only fully read sampled rows. A canonical completion is used to decode sampled-row membership, never as the unknown full input. Record comparisons determine covered and heavy membership and the right list. Conditional input domains require precisely these known rows and the simultaneous preprocessing and label events. Maintained data on a subset have no entries outside that subset. Setup and coherent replacement states sum over the actual implicit size class, with the actual record and left list for each stored index.
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, §4.2, equations (4.18)–(4.26), printed pp.29–32 = PDF pp.29–32.

import Definitions.Def_BMPV1173_Verification_SearchTasks

/-! Known side information consists exactly of the sampled rows and, when
specified, the maintained data on I. Values outside these sets are not supplied. -/
namespace BMPV1173.Verification

noncomputable section
open scoped BigOperators

abbrev SampleValues (n s d : ℕ) := (Fin s ⊕ Fin d) × Fin n → Bool
abbrev Record (n s d : ℕ) := (Fin s ⊕ Fin d) → Fin (n+2)
abbrev Maintained (n s d : ℕ) := Record n s d × Finset (Fin n)
abbrev SubsetData (n s d : ℕ) := Fin n → Option (Maintained n s d)

def sampleValues {n s d : ℕ} (x : VectorInput n) (p : Fin s → Fin n) (g : Fin d → Fin n) :
    SampleValues n s d := fun z => x (z.1.elim p g,z.2)

/-- A canonical completion of the fully read sampled rows, used only to
compute covered membership of degree-sample rows from known sample data. -/
def sampleCompletion {n s d : ℕ} (p : Fin s → Fin n) (g : Fin d → Fin n)
    (v : SampleValues n s d) : VectorInput n := fun z =>
  (((List.finRange s).map (Sum.inl : Fin s → Fin s ⊕ Fin d) ++
    (List.finRange d).map (Sum.inr : Fin d → Fin s ⊕ Fin d)).find?
    (fun h => h.elim p g = z.1)).elim false (fun h => v (h,z.2))

def coveredFromRecord {n s d : ℕ} (v : SampleValues n s d) (R : Record n s d)
    (k : Fin n) : Prop := ∃ h : Fin s, v (.inl h,k) = true ∧ k.val+1 ≤ (R (.inl h)).val

def heavyFromRecord {n s d : ℕ} (p : Fin s → Fin n) (g : Fin d → Fin n)
    (v : SampleValues n s d) (R : Record n s d) (t : ℕ) (k : Fin n) : Prop :=
  (2*t : ℝ) < (n : ℝ)/d *
    ((Finset.univ.filter fun h : Fin d => k.val+1 ≤ (R (.inr h)).val ∧
      g h ∉ covered (sampleCompletion p g v) p k).card : ℝ)

def rightFromRecord {n s d : ℕ} (R : Record n s d) : Finset (Fin n) :=
  Finset.univ.filter fun k => ∃ h : Fin s, (R (.inl h)).val = k.val+1

def compatibleSamples {n s d : ℕ} (p : Fin s → Fin n) (g : Fin d → Fin n)
    (v : SampleValues n s d) : Set (VectorInput n) := {x | sampleValues x p g = v}

def goodInputs {n s d m : ℕ} (p : Fin s → Fin n) (g : Fin d → Fin n)
    (v : SampleValues n s d) (s₀ t : ℕ) (K : Fin m → Fin n) : Set (VectorInput n) :=
  {x | x ∈ compatibleSamples p g v ∧ preprocessingGood x p g t ∧
    sizeGood (left x p g t) s₀ t K}

def hasPartner {n : ℕ} (I : Finset (Fin n)) (x : VectorInput n) : Bool := by
  classical
  exact decide (∃ i ∈ I, ∃ j : Fin n, i ≠ j ∧ ∀ k : Fin n,
    ¬ (x (i,k) = true ∧ x (j,k) = true))

def subsetData {n s d : ℕ} (x : VectorInput n) (p : Fin s → Fin n) (g : Fin d → Fin n)
    (t : ℕ) (I : Finset (Fin n)) : SubsetData n s d :=
  fun i => if i ∈ I then some (maintainedData x p g t i) else none

def classSubsets {n s d m : ℕ} (x : VectorInput n) (p : Fin s → Fin n)
    (g : Fin d → Fin n) (t : ℕ) (K : Fin m → Fin n) (a r : ℕ) : Finset (Finset (Fin n)) :=
  ((sizeClass (left x p g t) t K a).powerset).filter fun I => I.card = r

def classSetup {n s d m : ℕ} (x : VectorInput n) (p : Fin s → Fin n)
    (g : Fin d → Fin n) (t : ℕ) (K : Fin m → Fin n) (a r : ℕ) :
    EuclideanSpace ℂ (WalkRegister n (SubsetData n s d)) :=
  ((Real.sqrt ((classSubsets x p g t K a r).card : ℝ))⁻¹ : ℂ) •
    ∑ I ∈ classSubsets x p g t K a r, QAlgorithms.ket (I,I,subsetData x p g t I)

/-- A coherent replacement includes selecting a uniform neighbor from the implicit
class, rather than receiving that neighbor for free. -/
def classNeighbor {n s d m : ℕ} (x : VectorInput n) (p : Fin s → Fin n)
    (g : Fin d → Fin n) (t : ℕ) (K : Fin m → Fin n) (a r : ℕ) (I : Finset (Fin n)) :
    EuclideanSpace ℂ (WalkRegister n (SubsetData n s d)) :=
  let Jset := (classSubsets x p g t K a r).filter fun J =>
    J.card = r ∧ (I \ J).card = 1 ∧ (J \ I).card = 1
  ((Real.sqrt (Jset.card : ℝ))⁻¹ : ℂ) •
    ∑ J ∈ Jset, QAlgorithms.ket (I,J,subsetData x p g t J)

end
end BMPV1173.Verification


