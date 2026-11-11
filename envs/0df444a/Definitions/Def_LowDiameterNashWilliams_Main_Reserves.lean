-- Prove2me | Definitions.Def_LowDiameterNashWilliams_Main_Reserves
-- name    : LowDiameterNashWilliams_Main_Reserves
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:48.020243+00:00
-- url     : https://prove2.me/theorems/650628f5-e062-4489-b3d7-330a322d2df4
-- title:
--   Owner reserves and exact exchange partitions
-- statement:
--   For each vertex $v$, an owner reserve $R_v$ consists of edges incident with $v$, and reserves of different owners are disjoint. An exchange partition on a receiving index class $I$ consists of disjoint spanning trees $(U_i)_{i\in I}$ and disjoint owner reserves, with no tree-reserve overlap and exact union equal to the specified available edge set $P$:
--
--   $$P=\bigcup_{i\in I}E(U_i)\;\dot\cup\;\bigcup_{v\in V}R_v.$$
--
--   The number of reserved neighbors in $A$ counts edges whose other endpoint belongs to $A$. The shortening output predicate records the exact new tree partition, both receiving-tree bounds, both additive supplying-tree bounds, an exceptional superset $S'\supseteq S$, its size bound, and strictly fewer than $k/8$ internal receiving-tree occurrences outside $S'$. No restoration or existence assertion is built into an owner reserve or an exchange partition. These predicates expose the invariants shared by Lemmas 4.1 and 4.3 and Theorem 4.
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Sections 4.1–4.3, pp. 12–18 (PDF pp. 13–19)

import Definitions.Def_LowDiameterNashWilliams_Main_Geometry

set_option autoImplicit false
open scoped ENNReal NNReal
open Classical
open NashWilliams61.TreePacking

namespace LowDiameterNashWilliams.Main

/-! Owner reserves and exact exchange partitions, Sections 4.1–4.3 (PDF 13–19).
These definitions assert only incidence, disjointness and coverage, not restoreability. -/
def OwnerReserves {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) (R : Fin n → Edges m) : Prop :=
  (∀ v e, e ∈ R v → v ∈ ends e) ∧ ∀ v w, v ≠ w → Disjoint (R v) (R w)

def ExchangePartition {n m k : ℕ} (ends : Fin m → Sym2 (Fin n)) (I : Finset (Fin k))
    (U : Trees k m) (R : Fin n → Edges m) (P : Edges m) : Prop :=
  (∀ i ∈ I, IsSpanningTree ends (U i)) ∧
  (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (U i) (U j)) ∧
  OwnerReserves ends R ∧ (∀ i ∈ I, ∀ v, Disjoint (U i) (R v)) ∧
  I.biUnion U ∪ Finset.univ.biUnion R = P

noncomputable def reserveNeighbors {n m : ℕ} (ends : Fin m → Sym2 (Fin n))
    (R : Fin n → Edges m) (v : Fin n) (A : Finset (Fin n)) : ℕ :=
  ((R v).filter fun e => ∃ u ∈ A, u ≠ v ∧ ends e = s(v, u)).card

/-- Exact output requirements of Theorem 4, apart from its computational clause. -/
noncomputable def Shortened {n m k : ℕ} (ends : Fin m → Sym2 (Fin n))
    (C : ℝ) (T U : Trees k m) (I J : Finset (Fin k)) (S S' : Finset (Fin n)) : Prop :=
  TreePartition ends U ∧
  (∀ i ∈ I, diameter ends (U i) ≤ ENNReal.ofReal (C * (S.card + (n : ℝ) / k)) ∧
    ((internal ends (U i)).card : ℝ) ≤ C * (S.card + (n : ℝ) / k * Real.log k)) ∧
  (∀ j ∈ J, diameter ends (U j) ≤ diameter ends (T j) + 2 ∧
    ((internal ends (U j)).card : ℝ) ≤ (internal ends (T j)).card + C * ((n : ℝ) / k * Real.log k)) ∧
  S ⊆ S' ∧ (S'.card : ℝ) ≤ C * (S.card + (n : ℝ) / k) ∧
  ∀ v, v ∉ S' → (internalCount ends U I v : ℝ) < (k : ℝ) / 8

end LowDiameterNashWilliams.Main


