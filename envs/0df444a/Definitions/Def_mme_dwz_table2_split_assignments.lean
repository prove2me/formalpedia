-- Prove2me | Definitions.Def_mme_dwz_table2_split_assignments
-- name    : mme_dwz_table2_split_assignments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T13:27:32.941354+00:00
-- url     : https://prove2.me/theorems/20aa6937-f301-4758-93d6-80aff48cf734
-- title:
--   DWZ Table-2 independent split-assignment space
-- statement:
--   This module defines the exact finite assignment space used by the numerator
--   of DWZ Equation (23), specialized to the integral Table-2 data.
--
--   The region type is the disjoint sum of the boundary components satisfying
--   $x=0$ or $y=0$ and the five interior regions $(+,+,k)$.  Each tagged region
--   has its exact scaled size and its exact three-label `split` or `plusSplit`
--   histogram.  A local assignment is a directly evaluable word whose three
--   fibers have those prescribed cardinalities, and `SplitAssignments(m)` is the
--   dependent product of the local assignment types over all regions.
--
--   The module also records the coarse $Z$-degree carried by each region.  These
--   definitions make the disjoint numerator choices countable independently and
--   allow a later theorem to glue them into a global fine-pair word.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173, Lemma 6.7 and Equation (23), printed pp. 54–56.

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts

set_option autoImplicit false

namespace MME.DWZTable2Cardinality

/-- Table-2 components governed by condition (a) before DWZ Equation (23). -/
abbrev BoundaryShape :=
  {s : Fin 15 // MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0}

/-- The disjoint numerator regions: boundary components and the five
interior `(+,+,k)` regions from condition (c). -/
abbrev SplitRegion := BoundaryShape ⊕ Fin 5

/-- Coarse Z-degree carried by one numerator region. -/
def coarseDegree : SplitRegion → Fin 5
  | Sum.inl s => MME.DWZSquare.shapeZ s.1
  | Sum.inr k => k

/-- Exact integral size of one numerator region at multiplier `m`. -/
def regionSize (m : ℕ) : SplitRegion → ℕ
  | Sum.inl s => MME.DWZTable2Counts.component s.1 * m
  | Sum.inr k => MME.DWZTable2Counts.plusMass k * m

/-- Exact multiplicity of one left-split label in one numerator region. -/
def cellCount (m : ℕ) : SplitRegion → Fin 3 → ℕ
  | Sum.inl s, r => MME.DWZTable2Counts.split s.1 r * m
  | Sum.inr k, r => MME.DWZTable2Counts.plusSplit k r * m

/-- A tagged position type for one disjoint numerator region. -/
abbrev RegionPosition (m : ℕ) (r : SplitRegion) := Fin (regionSize m r)

/-- A directly evaluable split word on one tagged numerator region, with the
exact three-cell Table-2 histogram. -/
abbrev LocalSplitAssignment (m : ℕ) (r : SplitRegion) :=
  {f : RegionPosition m r → Fin 3 //
    ∀ i, Fintype.card {t : RegionPosition m r // f t = i} = cellCount m r i}

/-- The literal independent split assignments in conditions (a) and (c)
preceding DWZ Equation (23).  An element gives a directly evaluable local
split word on every tagged region. -/
def SplitAssignments (m : ℕ) :=
  ∀ r : SplitRegion, LocalSplitAssignment m r

end MME.DWZTable2Cardinality


