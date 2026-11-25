-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixCoord
-- name    : GroundTheory_AutomorphicForms_GL2_GJMatrixCoord
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:32.478744+00:00
-- url     : https://prove2.me/theorems/bd4cd4d0-0a18-48d5-b693-a1b2d98bee5f
-- title:
--   GJMatrix Coord
-- statement:
--   Definitions and structural lemmas for GJMatrix Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixCoord.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.GJMatrix
open MeasureTheory Matrix
noncomputable section
instance measurableSpace_matrix {m n X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Matrix m n X) :=
  inferInstanceAs (MeasurableSpace (m → n → X))
instance borelSpace_matrix {m n X : Type*} [Countable m] [Countable n] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] :
    BorelSpace (Matrix m n X) :=
  inferInstanceAs (BorelSpace (m → n → X))
variable {n X : Type*} [Fintype n]
def matrixMeasure [MeasurableSpace X] (μ : Measure X) : Measure (Matrix n n X) :=
  Measure.pi fun _ : n ↦ Measure.pi fun _ : n ↦ μ
def matrixCoord (x : Matrix n n X) : n × n → X :=
  fun p ↦ x p.1 p.2
def matrixCoordT (x : Matrix n n X) : n × n → X :=
  fun p ↦ x p.2 p.1
variable (n X) in

def matrixCoordHomeomorph [TopologicalSpace X] : Matrix n n X ≃ₜ (n × n → X) where
  toFun := matrixCoord
  invFun z := Matrix.of fun i j ↦ z (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun p ↦ (continuous_apply p.2).comp (continuous_apply p.1)
  continuous_invFun := continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_apply (i, j)
variable (n X) in

def matrixCoordTHomeomorph [TopologicalSpace X] : Matrix n n X ≃ₜ (n × n → X) where
  toFun := matrixCoordT
  invFun z := Matrix.of fun i j ↦ z (j, i)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun p ↦ (continuous_apply p.1).comp (continuous_apply p.2)
  continuous_invFun := continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_apply (j, i)
end
end GroundTheory.Automorphic.GJMatrix


