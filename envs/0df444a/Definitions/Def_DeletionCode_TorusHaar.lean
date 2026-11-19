-- Prove2me | Definitions.Def_DeletionCode_TorusHaar
-- name    : DeletionCode_TorusHaar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:32:57.704404+00:00
-- url     : https://prove2.me/theorems/7562bdee-1d6e-405c-8abc-e79e7d01c26e
-- title:
--   Torus Haar
-- statement:
--   Definitions and structural lemmas for Torus Haar, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TorusHaar.lean

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Probability.Independence.Basic
set_option autoImplicit true
namespace DeletionCode.TorusHaar
open MeasureTheory ProbabilityTheory
open scoped BigOperators
local instance _p2m_local_instance_196a2ea6bd_18 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩
variable {I J : Type*} [Fintype I] [Fintype J]
end DeletionCode.TorusHaar


