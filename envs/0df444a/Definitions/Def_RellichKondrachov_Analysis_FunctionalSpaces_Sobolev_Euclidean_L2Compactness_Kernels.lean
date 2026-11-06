-- Prove2me | Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
-- name    : RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:34:17.324033+00:00
-- url     : https://prove2.me/theorems/83c36474-9538-4372-b5fb-bab5725ed221
-- title:
--   Kernels
-- statement:
--   Definitions and structural lemmas for Kernels, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support
set_option autoImplicit true
namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
section Volume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance instMeasurableSpaceEL2CompactnessKernels : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessKernels : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessKernels : OpensMeasurableSpace E := by
  infer_instance
end Volume
end
end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov


