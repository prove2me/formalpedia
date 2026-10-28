-- Prove2me | Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductActiveReduction
-- name    : MarkovProcess_FiniteTime_CoordinateProductActiveReduction
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:42:09.903624+00:00
-- url     : https://prove2.me/theorems/d39060ca-4665-4a2d-bf99-70d00c53e0ee
-- title:
--   MarkovProcess definitions: FiniteTime.CoordinateProductActiveReduction
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.FiniteTime.CoordinateProductActiveReduction`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/CoordinateProductActiveReduction.lean#L1-L106

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductNormalization
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductStoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-!
# Restricting normalized coordinate products to active coordinates

This file enumerates the active coordinates of a normalized `CoordinateProductTerm`, extracts
their genuine `C₀` factors, and proves that evaluation factors through the corresponding
coordinate restriction.  The restricting function is definitionally the same path operation as
`FiniteOrderedTimes.restrictPath (activeOrderEmbedding factors)` when that finite-time API is in
scope.

If there are no active coordinates, the reduced index type is `Fin 0` and the empty scalar
product is one.  No constant-one element of `C₀` is constructed.  This is purely algebraic
finite-product infrastructure: it involves no measure and no kernel.
-/

open scoped CompactlySupported ZeroAtInfty BigOperators

namespace MarkovProcess.PiContinuousMap

variable {n : ℕ} {alpha : Type*} [TopologicalSpace alpha]

/-- The increasing enumeration of the coordinates carrying normalized factors. -/
def activeOrderEmbedding (factors : List (Fin n × C₀(alpha, ℝ))) :
    Fin (activeCoordinates factors).card ↪o Fin n :=
  (activeCoordinates factors).orderEmbOfFin rfl

/-- The genuine `C₀` factor at an active coordinate, indexed in increasing order. -/
def activeNormalizedFactor (factors : List (Fin n × C₀(alpha, ℝ)))
    (j : Fin (activeCoordinates factors).card) : C₀(alpha, ℝ) :=
  (normalizedCoordinateFactors factors (activeOrderEmbedding factors j)).get (by
    apply (mem_activeCoordinates_iff factors _).mp
    exact Finset.orderEmbOfFin_mem (activeCoordinates factors) rfl j)





/-- Scalar evaluation of a normalized term on only its active coordinates.  For an empty active
set this is the coefficient times the empty scalar product, hence just the coefficient. -/
def CoordinateProductTerm.activeEvaluation
    (t : CoordinateProductTerm (Fin n) alpha)
    (y : Fin (activeCoordinates t.factors).card → alpha) : ℝ :=
  t.coefficient * ∏ j, activeNormalizedFactor t.factors j (y j)



end MarkovProcess.PiContinuousMap


