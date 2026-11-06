-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedGermUnits
-- name    : QEC_Coding_AlgebraicGeometry_Places_NormalizedGermUnits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:51:59.537045+00:00
-- url     : https://prove2.me/theorems/aa4473aa-ba14-4aad-82c6-fe1efb142508
-- title:
--   Normalized Germ Units
-- statement:
--   Definitions and structural lemmas for Normalized Germ Units, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/NormalizedGermUnits.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) ω M]
end
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms


