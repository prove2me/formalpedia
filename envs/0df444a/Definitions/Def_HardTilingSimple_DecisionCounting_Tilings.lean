-- Prove2me | Definitions.Def_HardTilingSimple_DecisionCounting_Tilings
-- name    : HardTilingSimple_DecisionCounting_Tilings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T00:31:33.111649+00:00
-- url     : https://prove2.me/theorems/1c551e55-aec6-469c-a3c3-edb97f4cd2f2
-- title:
--   Unordered geometric tilings and their finite count
-- statement:
--   Fix any finite set of finite square-lattice shapes and any finite region R. The legal footprints are all nonempty translated quarter-turns of these shapes contained in R. A geometric tiling is an unordered finite set of legal footprints, pairwise disjoint, whose union is exactly R. Its count is the cardinality of the finite collection of all such tilings.
--
--   The footprint enumeration aligns each cell of each rotated shape with each cell of R, then discards footprints leaving R. Finite sets remove duplicate presentations of a footprint, so rotation labels, placement order and labels on identical copies never multiply the count. Tilings related by a global symmetry remain distinct unless their sets of footprints are identical. The empty region has one tiling, the empty family. Empty shapes contribute no legal footprints. This general definition is specialized to the paper's fixed two-shape set in the Tiles item.
-- source:
--   Moore and Robson, Hard Tiling Problems with Simple Tiles, Discrete & Computational Geometry 26, 573–590 (2001), published DOI https://doi.org/10.1007/s00454-001-0047-6, §2, p. 574 (PDF 2), existence and counting problems; finite enumeration is a formalization convention.

import Definitions.Def_HardTilingSimple_DecisionCounting_Geometry

namespace HardTilingSimple.DecisionCounting

/-- Enumerate footprints by aligning a shape cell with a region cell.
This includes every nonempty translated rotation contained in the region. -/
def legalFootprints (shapes : Finset Region) (R : Region) : Finset Region :=
  (R.biUnion fun q => shapes.biUnion fun S =>
    (Finset.univ : Finset (Fin 4)).biUnion fun k =>
      S.image fun p =>
        placement S k (q.1 - (rotate k p).1, q.2 - (rotate k p).2)).filter
    (fun P => P.Nonempty ∧ P ⊆ R)

/-- Unordered geometric tilings: disjoint legal footprints with exact coverage. -/
def geometricTilings (shapes : Finset Region) (R : Region) : Finset (Finset Region) :=
  (legalFootprints shapes R).powerset.filter fun T =>
    (∀ P ∈ T, ∀ Q ∈ T, P ≠ Q → Disjoint P Q) ∧ T.biUnion id = R

/-- A genuinely finite cardinality, including the empty tiling of the empty region. -/
def geometricCount (shapes : Finset Region) (R : Region) : ℕ :=
  (geometricTilings shapes R).card

end HardTilingSimple.DecisionCounting


