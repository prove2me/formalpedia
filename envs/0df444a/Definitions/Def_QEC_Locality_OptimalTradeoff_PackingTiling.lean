-- Prove2me | Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
-- name    : QEC_Locality_OptimalTradeoff_PackingTiling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:46:21.503454+00:00
-- url     : https://prove2.me/theorems/d6ef1215-37aa-4801-8181-3b81cdee88ec
-- title:
--   Packing Tiling
-- statement:
--   Definitions and structural lemmas for Packing Tiling, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/PackingTiling.lean

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
namespace QEC.Locality
local instance instClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
abbrev GridTranslation (w : ℝ) := AddCircle w × AddCircle w
def phase (w : ℝ) (p : ℝ × ℝ) : AddCircle w × AddCircle w :=
  ((p.1 : AddCircle w), (p.2 : AddCircle w))
noncomputable def gridOrigin (w : ℝ) (t : GridTranslation w) : ℝ × ℝ :=
  (Quotient.out t.1, Quotient.out t.2)
def gridCellIndex (w : ℝ) (origin point : ℝ × ℝ) : ℤ × ℤ :=
  (⌊(point.1 - origin.1) / w⌋, ⌊(point.2 - origin.2) / w⌋)
def gridCellLower (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) : ℝ × ℝ :=
  (origin.1 + cell.1 * w, origin.2 + cell.2 * w)
def gridCellUpper (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) : ℝ × ℝ :=
  (origin.1 + (cell.1 + 1) * w, origin.2 + (cell.2 + 1) * w)
def UnitSeparatedEmbedding2D.gridCellQubits {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) (cell : ℤ × ℤ) : Finset ι :=
  Finset.univ.filter fun q => gridCellIndex w origin (embedding.point q) = cell
def UnitSeparatedEmbedding2D.gridOccupiedCells {ι : Type*} [Fintype ι]
    [DecidableEq ι] (embedding : UnitSeparatedEmbedding2D ι)
    (w : ℝ) (origin : ℝ × ℝ) : Finset (ℤ × ℤ) :=
  Finset.univ.image fun q => gridCellIndex w origin (embedding.point q)
def periodicInfinityDistance (w : ℝ) (t : GridTranslation w) (p : ℝ × ℝ) : ℝ :=
  max (dist t.1 (phase w p).1) (dist t.2 (phase w p).2)
def periodicEdgeDistance (w : ℝ) (t : GridTranslation w) (p : ℝ × ℝ) : ℝ :=
  min (dist t.1 (phase w p).1) (dist t.2 (phase w p).2)
def vertexBad (w r : ℝ) (t : AddCircle w × AddCircle w) (p : ℝ × ℝ) : Prop :=
  dist t.1 (phase w p).1 ≤ r ∧ dist t.2 (phase w p).2 ≤ r
def edgeBad (w r : ℝ) (t : AddCircle w × AddCircle w) (p : ℝ × ℝ) : Prop :=
  dist t.1 (phase w p).1 ≤ r ∨ dist t.2 (phase w p).2 ≤ r
def vertexScore {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) : ℝ :=
  ∑ i : a, if vertexBad w r t (points i) then 1 else 0
def edgeScore {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) : ℝ :=
  ∑ i : a, if edgeBad w r t (points i) then 1 else 0
def vertexBadCount {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) : ℕ :=
  (Finset.univ.filter fun i => vertexBad w r t (points i)).card
def edgeBadCount {a : Type*} [Fintype a] (w r : ℝ)
    (points : a → ℝ × ℝ) (t : AddCircle w × AddCircle w) : ℕ :=
  (Finset.univ.filter fun i => edgeBad w r t (points i)).card
def rectangle (lower upper : ℝ × ℝ) : Set (ℝ × ℝ) :=
  Set.Icc lower.1 upper.1 ×ˢ Set.Icc lower.2 upper.2
def packingRadius : ℝ := Real.sqrt 2 / 4
def packingBox (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  Set.Ioo (p.1 - packingRadius) (p.1 + packingRadius) ×ˢ
    Set.Ioo (p.2 - packingRadius) (p.2 + packingRadius)
def expandedRectangle (lower upper : ℝ × ℝ) : Set (ℝ × ℝ) :=
  Set.Ioo (lower.1 - packingRadius) (upper.1 + packingRadius) ×ˢ
    Set.Ioo (lower.2 - packingRadius) (upper.2 + packingRadius)
def UnitSeparatedEmbedding2D.qubitsInRectangle
    {i : Type*} [Fintype i] [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (lower upper : ℝ × ℝ) : Finset i :=
  Finset.univ.filter fun p => embedding.point p ∈ rectangle lower upper
end QEC.Locality
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {i : Type u} [Fintype i] [DecidableEq i]
variable {kappa : Type v} [Fintype kappa]
abbrev daiLiLongIncidenceIndex
    (P : BinaryStabilizerPresentation (ι := i) (κ := kappa))
    (embedding : Locality.UnitSeparatedEmbedding2D i) (threshold : ℝ) :=
  Σ q : i, Fin (P.daiLiInteractionCounter embedding threshold q)
def daiLiLongIncidencePoint
    (P : BinaryStabilizerPresentation (ι := i) (κ := kappa))
    (embedding : Locality.UnitSeparatedEmbedding2D i) (threshold : ℝ) :
    P.daiLiLongIncidenceIndex embedding threshold → ℝ × ℝ :=
  fun incidence => embedding.point incidence.1
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation


