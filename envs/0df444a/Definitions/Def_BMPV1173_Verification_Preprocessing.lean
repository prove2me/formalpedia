-- Prove2me | Definitions.Def_BMPV1173_Verification_Preprocessing
-- name    : BMPV1173_Verification_Preprocessing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:03:30.714945+00:00
-- url     : https://prove2.me/theorems/f2698231-b224-446f-8f55-9f56ad1f346d
-- title:
--   Sampled first intersections, test sets, size labels, records and prefix work
-- statement:
--   Defines the first common-one coordinate with source sentinels 0 for self and n+1 for a distinct orthogonal pair. Ordered independent draws preserve multiplicity. Covered and heavy sets, left and right lists, remaining coordinates, rounded power-of-two labels and classes are computed from the input and samples. Records retain every sampled occurrence; pair work counts only the prefix through the first common one and includes the end sentinel. Uniform finite probability is the fraction of draw tuples satisfying an event. Sample lengths are ceilings of c(n/t)(1+log n), an explicit realization of the source sampling scale for positive dimensions.
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, §4.2, equations (4.12)–(4.23); (4.4)–(4.6), printed pp.27–30 = PDF pp.27–30, with labels also on pp.23–24.

import Definitions.Def_BMPV1173_Verification_Problems

/-! Source §4.2, (4.12)–(4.23), pp.27–30. Samples are ordered draws:
repeated draws remain separate occurrences. Coordinates of Fin n encode source coordinates k+1. -/
namespace BMPV1173.Verification

noncomputable section
open scoped BigOperators

/-- Zero for self; k+1 for the least common coordinate; n+1 for an orthogonal pair. -/
def first {n : ℕ} (x : VectorInput n) (i j : Fin n) : ℕ :=
  if i = j then 0 else
    ((List.finRange n).find? (fun k => x (i,k) && x (j,k))).elim (n+1) (fun k => k.val+1)

def neighbors {n : ℕ} (x : VectorInput n) (k i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => k.val+1 ≤ first x i j

def covered {n s : ℕ} (x : VectorInput n) (p : Fin s → Fin n) (k : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => ∃ h, x (p h,k) = true ∧ j ∈ neighbors x k (p h)

def heavy {n s d : ℕ} (x : VectorInput n) (p : Fin s → Fin n)
    (g : Fin d → Fin n) (t : ℕ) (k : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (2*t : ℝ) < (n : ℝ) / d *
    ((Finset.univ.filter fun h => g h ∈ neighbors x k i ∧ g h ∉ covered x p k).card : ℝ)

def leftFor {n : ℕ} (x : VectorInput n) (H : Fin n → Finset (Fin n)) (i : Fin n) :=
  Finset.univ.filter fun k => x (i,k) = true ∧ i ∈ H k

def rightFor {n : ℕ} (x : VectorInput n) (C : Fin n → Finset (Fin n)) (j : Fin n) :=
  Finset.univ.filter fun k => x (j,k) = true ∧ j ∈ C k

def remainingFor {n : ℕ} (C H : Fin n → Finset (Fin n)) (i j : Fin n) :=
  Finset.univ.filter fun k => i ∉ H k ∧ j ∉ C k

def coordsFor {n : ℕ} (x : VectorInput n) (C H : Fin n → Finset (Fin n)) (i j : Fin n) :=
  leftFor x H i ∪ rightFor x C j ∪ remainingFor C H i j

def left {n s d : ℕ} (x : VectorInput n) (p : Fin s → Fin n) (g : Fin d → Fin n)
    (t : ℕ) := leftFor x (heavy x p g t)

def right {n s : ℕ} (x : VectorInput n) (p : Fin s → Fin n) := rightFor x (covered x p)

def coords {n s d : ℕ} (x : VectorInput n) (p : Fin s → Fin n) (g : Fin d → Fin n)
    (t : ℕ) := coordsFor x (covered x p) (heavy x p g t)

/-- Ceiling of c (n/t)(1+log n). For n≥2 this is the source's sufficiently
large absolute constant in Theta((n/t) log n), and always gives a positive length when c>0. -/
def sampleCount (c n t : ℕ) : ℕ := Nat.ceil ((c : ℝ) * ((n : ℝ) / t) * (1+Real.log n))

/-- Uniform product probability on a finite sample space: independent sampling with replacement. -/
def uniformProbability {Ω : Type} [Fintype Ω] (E : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter fun z => E z).card : ℝ) / Fintype.card Ω

def preprocessingGood {n s d : ℕ} (x : VectorInput n) (p : Fin s → Fin n)
    (g : Fin d → Fin n) (t : ℕ) : Prop :=
  (∀ i k, i ∈ heavy x p g t k → t < (neighbors x k i \ covered x p k).card) ∧
  (∀ i k, i ∉ heavy x p g t k → (neighbors x k i \ covered x p k).card ≤ 4*t) ∧
  ((∑ i : Fin n, ((left x p g t i).card : ℝ)) ≤ 100*(n : ℝ)^3/((s : ℝ)*t)) ∧
  (∀ j, (right x p j).card ≤ s) ∧
  ∀ i, (∑ j ∈ Finset.univ.erase i,
    ((remainingFor (covered x p) (heavy x p g t) i j).filter
      (fun k => k.val+1 ≤ first x i j)).card) ≤ 4*n*t

/-- The actual rounded estimator (4.19), not a free label table. -/
def sizeLabel {n m : ℕ} (L : Fin n → Finset (Fin n)) (t : ℕ)
    (K : Fin m → Fin n) (i : Fin n) : ℕ :=
  2 ^ Nat.clog 2 (max (2*t) (Nat.ceil ((2*(n : ℝ)/m) *
    ((Finset.univ.filter fun h => K h ∈ L i).card : ℝ))))

def sizeClass {n m : ℕ} (L : Fin n → Finset (Fin n)) (t : ℕ)
    (K : Fin m → Fin n) (a : ℕ) :=
  Finset.univ.filter fun i => sizeLabel L t K i = a

def classLabels {n m : ℕ} (L : Fin n → Finset (Fin n)) (t : ℕ)
    (K : Fin m → Fin n) : Finset ℕ := Finset.univ.image (sizeLabel L t K)

def sizeGood {n m : ℕ} (L : Fin n → Finset (Fin n)) (s t : ℕ)
    (K : Fin m → Fin n) : Prop :=
  (∀ i, (L i).card ≤ sizeLabel L t K i ∧ sizeLabel L t K i ≤ 8*((L i).card+t)) ∧
  (∀ a, a * (sizeClass L t K a).card ≤ ∑ i, sizeLabel L t K i) ∧
  ((∑ i : Fin n, (sizeLabel L t K i : ℝ)) ≤ 8*(n : ℝ)*t + 800*(n : ℝ)^3/((s : ℝ)*t))

/-- Record entries indexed by the disjoint union of occurrences, including duplicates. -/
def record {n s d : ℕ} (x : VectorInput n) (p : Fin s → Fin n) (g : Fin d → Fin n)
    (i : Fin n) : (Fin s ⊕ Fin d) → Fin (n+2) :=
  fun h => ⟨first x i (h.elim p g), by
    unfold first
    split
    · omega
    · cases hfind : (List.finRange n).find? (fun k => x (i,k) && x (h.elim p g,k)) with
      | none => simp
      | some k => simp⟩

def maintainedData {n s d : ℕ} (x : VectorInput n) (p : Fin s → Fin n) (g : Fin d → Fin n)
    (t : ℕ) (i : Fin n) := (record x p g i, left x p g t i)

/-- Includes n+1 even when the pair is orthogonal; self work is never summed. -/
def pairWork {n s d : ℕ} (x : VectorInput n) (p : Fin s → Fin n) (g : Fin d → Fin n)
    (t : ℕ) (i j : Fin n) : ℕ :=
  (((coords x p g t i j).image (fun k => k.val+1) ∪ {n+1}).filter
    fun k => k ≤ first x i j).card

def partnerWork {n s d : ℕ} (x : VectorInput n) (p : Fin s → Fin n) (g : Fin d → Fin n)
    (t : ℕ) (I : Finset (Fin n)) (j : Fin n) : ℕ :=
  ∑ i ∈ I.erase j, pairWork x p g t i j

end
end BMPV1173.Verification


