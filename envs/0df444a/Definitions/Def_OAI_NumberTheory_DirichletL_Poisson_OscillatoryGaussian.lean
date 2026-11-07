-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
-- name    : OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:24:34.298355+00:00
-- url     : https://prove2.me/theorems/2abdbf76-22ed-4eb6-9f04-48818234b5f5
-- title:
--   Oscillatory Gaussian
-- statement:
--   Definitions and structural lemmas for Oscillatory Gaussian, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLatticeCount_coords_eval
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
namespace OscSpecial
noncomputable def r (η a b : ℝ) : ℝ := 1 + 3 * q a b * η ^ 2 / 16
end OscSpecial
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
open EisensteinEmbedding ConcreteTraceCRT Complex
def dualFrequencyEquiv : (ℤ × ℤ) ≃ O where
  toFun p := ActualEisensteinCoordinates.eval (p.1 + p.2) p.1
  invFun y := ((ActualEisensteinCoordinates.coords y).2,
    (ActualEisensteinCoordinates.coords y).1 -
      (ActualEisensteinCoordinates.coords y).2)
  left_inv p := by
    rcases p with ⟨k,l⟩
    simp only [  ShortDraftLatticeCount.coords_eval]
    ext <;> ring
  right_inv y := by
    change ActualEisensteinCoordinates.eval
      ((ActualEisensteinCoordinates.coords y).2 +
        ((ActualEisensteinCoordinates.coords y).1 -
          (ActualEisensteinCoordinates.coords y).2))
      (ActualEisensteinCoordinates.coords y).2 = y
    convert ActualEisensteinCoordinates.eval_coords y using 1 ; ring_nf
end ActualEisensteinCubic
namespace GaussianMoment
open scoped Topology
open Filter
noncomputable def realGauss (t : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * t * RankTwoPoisson.eisQ z)
end GaussianMoment
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace OscSpecial
open scoped Topology
open Filter
end OscSpecial
namespace GaussianMoment
open scoped Topology
open Filter
end GaussianMoment
end
end OAI


