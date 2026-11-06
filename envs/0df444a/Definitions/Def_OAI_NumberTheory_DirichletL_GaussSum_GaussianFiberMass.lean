-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
-- name    : OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:45:07.093227+00:00
-- url     : https://prove2.me/theorems/30d3ce8c-356c-4947-ae02-624323435bd9
-- title:
--   Gaussian Fiber Mass
-- statement:
--   Definitions and structural lemmas for Gaussian Fiber Mass, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/GaussianFiberMass.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
import Theorems.Thm_OAI_ShortDraftLatticeCount_coords_eval

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
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace SqrtBranch
open Complex
end SqrtBranch
namespace PowerExtraction
end PowerExtraction
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace EisensteinAbelFiber
open scoped Topology
open Filter
end EisensteinAbelFiber
namespace ActualEisensteinCubic
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open EisensteinEmbedding ConcreteTraceCRT Complex
def latticeCoordEquiv : O ≃ ℤ × ℤ where
  toFun := ActualEisensteinCoordinates.coords
  invFun z := ActualEisensteinCoordinates.eval z.1 z.2
  left_inv := ActualEisensteinCoordinates.eval_coords
  right_inv z := ShortDraftLatticeCount.coords_eval z.1 z.2
end
end ActualEisensteinCubic
namespace GaussianPhasePointwise
end GaussianPhasePointwise
namespace ActualEisensteinCubic
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
end
end OAI


