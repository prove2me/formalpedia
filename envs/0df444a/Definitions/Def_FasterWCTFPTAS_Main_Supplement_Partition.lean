-- Prove2me | Definitions.Def_FasterWCTFPTAS_Main_Supplement_Partition
-- name    : FasterWCTFPTAS_Main_Supplement_Partition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:07:27.198951+00:00
-- url     : https://prove2.me/theorems/ebc3244e-269d-4d1a-8cd6-cfe46c759bea
-- title:
--   Grouped set partition and multiset weak partition with targets
-- statement:
--   Fix $k\ge2$. Array data have $q$ rows of $ks$ natural-valued positions, upper bound $W$, and $n=ksq$ total positions. Their common range condition is
--
--   $$a_{ij}\le W,\qquad n^{10}(W-a_{ij})\le W.$$
--
--   For $n>0$ this is exactly $a_{ij}\in[W(1-1/n^{10}),W]$. Grouped $k$-way Partition requires $s,q,W>0$, positive values and injectivity within each row. A Yes instance partitions every row into $k$ bins with exactly $s$ items per bin and $k$ times each bin's total sum, across all rows, equal to the total sum of all items. Its No predicate is the negation of Yes. Values may coincide in different rows.
--
--   The multiset problem retains natural $s,q,W$, allows repeated values within rows, and supplies targets $t_1,\ldots,t_{k-1}$. Selections are disjoint sets of positions in each row. Yes requires exactly $s$ positions per row and bin and load $t_\ell$ for each bin. No means that there is no disjoint selection satisfying all three relaxed conditions: every bin's first $i$ rows contain at most $is$ selected positions, the total number selected over all rows and bins is at least $(k-1)qs$, and every target is met. No is not the complement of Yes. Nothing is required of a solver outside the two promise sets. The division-free range handles the zero cases without deleting them. These definitions preserve the full promises used by both partition lower bounds.
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, A Faster FPTAS for Weighted Completion Time Scheduling, STOC 2027 submission #1072 (October 2026), p.20 (PDF p.21), the two problem boxes.

import Mathlib

set_option autoImplicit false

namespace FasterWCTFPTAS.Main.Supplement

open Finset

/-- Grouped array data, before imposing the set or multiset problem's validity conditions.
There are `q` rows, each with `k*s` positions. Different rows may share values. -/
structure PartitionData (k : ℕ) where
  s : ℕ
  q : ℕ
  W : ℕ
  a : Fin q → Fin (k * s) → ℕ

def PartitionData.n {k : ℕ} (I : PartitionData k) : ℕ := k * I.s * I.q

/-- The range `[W(1-1/n^10),W]`, division free. With `a ≤ W`, natural subtraction
is exact. If `n=0` there are no item positions, so no undefined interval is evaluated. -/
def PartitionData.InRange {k : ℕ} (I : PartitionData k) : Prop :=
  ∀ i j, I.a i j ≤ I.W ∧ I.n ^ 10 * (I.W - I.a i j) ≤ I.W

/-- The set problem has strictly positive s,q,W, positive items and injective rows.
Source: printed p.20 (PDF 21). -/
def GroupedValid {k : ℕ} (I : PartitionData k) : Prop :=
  0 < I.s ∧ 0 < I.q ∧ 0 < I.W ∧ I.InRange ∧
  (∀ i j, 0 < I.a i j) ∧ (∀ i, Function.Injective (I.a i))

/-- A label for every item partitions each row into k bins. Every bin has s items per row;
the equal-sum requirement is across ALL rows together. Multiplication by k avoids division. -/
def GroupedYes {k : ℕ} (I : PartitionData k) : Prop :=
  ∃ label : Fin I.q → Fin (k * I.s) → Fin k,
    (∀ i ℓ, (univ.filter (fun j => label i j = ℓ)).card = I.s) ∧
    ∀ ℓ, k * (∑ i, ∑ j ∈ univ.filter (fun j => label i j = ℓ), I.a i j) =
      ∑ i, ∑ j, I.a i j

def GroupedNo {k : ℕ} (I : PartitionData k) : Prop := ¬ GroupedYes I

/-- The multiset problem retains the complete natural domain and k-1 target values. -/
structure WeakInstance (k : ℕ) where
  data : PartitionData k
  target : Fin (k - 1) → ℕ

/-- Selections are sets of positions, so equal-valued occurrences remain distinct. -/
abbrev Selections {k : ℕ} (I : PartitionData k) :=
  Fin I.q → Fin (k - 1) → Finset (Fin (k * I.s))

def DisjointSelections {k : ℕ} {I : PartitionData k} (S : Selections I) : Prop :=
  ∀ i ℓ ℓ', ℓ ≠ ℓ' → Disjoint (S i ℓ) (S i ℓ')

def TargetLoads {k : ℕ} (I : WeakInstance k) (S : Selections I.data) : Prop :=
  ∀ ℓ, (∑ i, ∑ j ∈ S i ℓ, I.data.a i j) = I.target ℓ

/-- Yes: disjoint selections, exactly s per group and bin, and every target met. -/
def WeakYes {k : ℕ} (I : WeakInstance k) : Prop :=
  ∃ S : Selections I.data, DisjointSelections S ∧
    (∀ i ℓ, (S i ℓ).card = I.data.s) ∧ TargetLoads I S

/-- The complete relaxed witness excluded by the printed No case: each bin's every prefix
has at most i*s positions, the total number of selected positions is at least (k-1)*q*s,
and every target is met. Fin indices are zero based, hence prefix length i.val+1. -/
def WeakRelaxedWitness {k : ℕ} (I : WeakInstance k) (S : Selections I.data) : Prop :=
  DisjointSelections S ∧
  (∀ i ℓ, (∑ b ∈ univ.filter (fun b : Fin I.data.q => b ≤ i), (S b ℓ).card) ≤
    (i.val + 1) * I.data.s) ∧
  (k - 1) * I.data.q * I.data.s ≤ (∑ i, ∑ ℓ, (S i ℓ).card) ∧
  TargetLoads I S

/-- No is the negation of existence of the entire relaxed witness, not the negation of Yes. -/
def WeakNo {k : ℕ} (I : WeakInstance k) : Prop :=
  ¬ ∃ S : Selections I.data, WeakRelaxedWitness I S

def WeakValid {k : ℕ} (I : WeakInstance k) : Prop := I.data.InRange

end FasterWCTFPTAS.Main.Supplement


