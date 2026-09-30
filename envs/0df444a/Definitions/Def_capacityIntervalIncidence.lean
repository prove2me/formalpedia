-- Prove2me | Definitions.Def_capacityIntervalIncidence
-- name    : capacityIntervalIncidence
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-07T18:04:47.355619+00:00
-- url     : https://prove2.me/theorems/f19d2336-169f-447e-ade0-6960aa2feb44
-- title:
--   Interval partitions and their block-incidence map
-- statement:
--   For a natural number $n$, a nonempty interval of the ordered labels $1,\ldots,n$ is specified by endpoints $i\leq j$. An interval partition is a genuine partition in which every block is such an interval. Extend rational interval coefficients by zero on subsets that are not endpoint intervals, and define
--
--   $$T_{\rm int}:\mathbb Q^{\mathcal I_n}\longrightarrow\mathbb Q^{\Pi_n^{\rm int}},\qquad (T_{\rm int}c)(P)=\sum_{I\in P}c_I.$$
--
--   Here $\mathcal I_n$ is the set of all nonempty intervals and $\Pi_n^{\rm int}$ the set of interval partitions. The bundle includes the elementary linearity proofs required to construct this map, but not its substantive kernel characterization or rank theorem. The definitions permit $n=0$; the separate rank theorem assumes $n>0$. Endpoint certificates constrain the blocks of actual partitions, rather than replacing partitions by unrestricted collections of intervals.
-- source:
--   The four-label correlation threshold, Theorem 2.2 and equations (2.8)–(2.9). Unpublished research note (2026), N4_BLOCK_CORRELATION_NOTE.md, SHA-256 a9b67c132ca0e0af807fb917ca2322833b84e162c45a4da7329ee88fbe4f1c83. Exact formal source: formal_capacity/FormalCapacity/Finite/IntervalRank.lean, source-file SHA-256 5c52374871945aee752877ecf9e185074359f7d10cb473513e967665879afb4d. Local source archive; no public repository URL or commit is asserted. Upload checked with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_capacityFinitePartitions

set_option autoImplicit false

/-!
# Exact rank for interval partitions

Rows are nonempty intervals of Fin n, represented by their ordered
endpoints. Columns are genuine Finpartitions all of whose blocks carry an
endpoint certificate. This realizes compositions without choosing a cut-set
encoding.
-/

namespace FormalCapacity.Finite

open scoped BigOperators
open Finset Module Set

/-- A nonempty interval is represented by ordered endpoints. -/
abbrev IntervalEndpoint (n : ℕ) := Σ i : Fin n, Set.Ici i

/-- The finite set of labels in an endpoint interval. -/
def IntervalEndpoint.toFinset {n : ℕ} (I : IntervalEndpoint n) : Finset (Fin n) :=
  Finset.Icc I.1 I.2.1













/-- A composition, represented as a finite partition whose every block is a
certified endpoint interval. -/
structure IntervalPartition (n : ℕ) where
  partition : Finpartition (univ : Finset (Fin n))
  interval : ∀ B ∈ partition.parts, ∃ I : IntervalEndpoint n, I.toFinset = B









/-- Extend endpoint coefficients by zero away from endpoint intervals. -/
noncomputable def extendIntervalCoeff {n : ℕ}
    (c : IntervalEndpoint n → ℚ) (B : Finset (Fin n)) : ℚ :=
  if hB : ∃ I : IntervalEndpoint n, I.toFinset = B
  then c (Classical.choose hB)
  else 0





theorem extendIntervalCoeff_add {n : ℕ}
    (c d : IntervalEndpoint n → ℚ) (B : Finset (Fin n)) :
    extendIntervalCoeff (c + d) B =
      extendIntervalCoeff c B + extendIntervalCoeff d B := by
  classical
  by_cases hB : ∃ I : IntervalEndpoint n, I.toFinset = B <;>
    simp [extendIntervalCoeff, hB]

theorem extendIntervalCoeff_smul {n : ℕ}
    (r : ℚ) (c : IntervalEndpoint n → ℚ) (B : Finset (Fin n)) :
    extendIntervalCoeff (r • c) B = r * extendIntervalCoeff c B := by
  classical
  by_cases hB : ∃ I : IntervalEndpoint n, I.toFinset = B <;>
    simp [extendIntervalCoeff, hB]

/-- Transpose of interval-block incidence: evaluate interval-row
coefficients on every composition. -/
noncomputable def intervalBlockIncidenceTranspose (n : ℕ) :
    (IntervalEndpoint n → ℚ) →ₗ[ℚ] (IntervalPartition n → ℚ) where
  toFun c P := blockRowSum (extendIntervalCoeff c) P.partition
  map_add' c d := by
    funext P
    simp [blockRowSum, extendIntervalCoeff_add, Finset.sum_add_distrib]
  map_smul' r c := by
    funext P
    simp [blockRowSum, extendIntervalCoeff_smul, Finset.mul_sum]

















end FormalCapacity.Finite


