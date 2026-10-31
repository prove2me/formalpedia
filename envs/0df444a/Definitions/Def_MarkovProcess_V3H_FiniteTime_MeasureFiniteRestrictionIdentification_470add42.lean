-- Prove2me | Definitions.Def_MarkovProcess_V3H_FiniteTime_MeasureFiniteRestrictionIdentification_470add42
-- name    : MarkovProcess_V3H_FiniteTime_MeasureFiniteRestrictionIdentification_470add42
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:14:18.980069+00:00
-- url     : https://prove2.me/theorems/e6ed0798-08b3-4b26-9dad-76ebe90f18a1
-- title:
--   MarkovProcess: MarkovProcess_V3H_FiniteTime_MeasureFiniteRestrictionIdentification_470add42
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.MeasureTheory.Constructions.Projective

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying measures from finite-coordinate restrictions

A finite measure on a product space is determined by all of its finite-coordinate pushforwards.
The empty coordinate set is part of the family and therefore records the total mass; measures of
unequal mass cannot satisfy the hypothesis.

This is generic measure-theoretic infrastructure and requires no topology.
-/

open MeasureTheory

namespace MarkovProcess
namespace Measure

noncomputable section

variable {index alpha : Type*} [MeasurableSpace alpha]

/-- Two measures on a product space agree if all their finite-coordinate pushforwards agree. -/
theorem p2m_embedded_b1456b20928f753b
    (mu nu : Measure (index → alpha)) [IsFiniteMeasure mu]
    (h : ∀ I : Finset index, mu.map I.restrict = nu.map I.restrict) :
    mu = nu := by
  let family : (I : Finset index) → Measure (I → alpha) :=
    fun I ↦ mu.map I.restrict
  have hmu : IsProjectiveLimit mu family := by
    intro I
    rfl
  have hnu : IsProjectiveLimit nu family := by
    intro I
    exact (h I).symm
  let (I : Finset index) : IsFiniteMeasure (family I) := by
    dsimp only [family]
    infer_instance
  exact hmu.unique hnu

end
end Measure
end MarkovProcess


