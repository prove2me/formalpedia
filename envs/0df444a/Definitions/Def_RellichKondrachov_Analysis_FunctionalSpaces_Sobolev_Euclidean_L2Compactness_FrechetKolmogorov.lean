-- Prove2me | Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
-- name    : RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:41:50.870772+00:00
-- url     : https://prove2.me/theorems/e568a5da-4e58-45c6-ba62-96bc3df075b7
-- title:
--   Frechet Kolmogorov
-- statement:
--   Definitions and structural lemmas for Frechet Kolmogorov, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer
import Mathlib.Topology.UniformSpace.Cauchy
set_option autoImplicit true
namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
namespace L2Compactness
open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set
noncomputable section
section Volume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance instMeasurableSpaceEL2CompactnessFrechetKolmogorov : MeasurableSpace E := borel E
local instance instBorelSpaceEL2CompactnessFrechetKolmogorov : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceEL2CompactnessFrechetKolmogorov :
    OpensMeasurableSpace E := by infer_instance
local instance instMeasurableAddEL2CompactnessFrechetKolmogorov : MeasurableAdd E := by
  infer_instance
local instance instMeasurableNegEL2CompactnessFrechetKolmogorov : MeasurableNeg E := by
  infer_instance
variable {K : Set E} {ψ : E → ℝ}
end Volume
end
end L2Compactness
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov


