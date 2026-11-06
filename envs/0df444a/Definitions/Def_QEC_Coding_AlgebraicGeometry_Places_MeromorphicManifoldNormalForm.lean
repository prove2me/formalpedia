-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
-- name    : QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:51:38.288646+00:00
-- url     : https://prove2.me/theorems/69403f2f-fcbf-4a22-b70c-c1ce86036c4a
-- title:
--   Meromorphic Manifold Normal Form
-- statement:
--   Definitions and structural lemmas for Meromorphic Manifold Normal Form, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean

import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
end
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) ω M]
def chartNormalizedMeromorphicFunction (F : M → ℂ) (x : M) : ℂ :=
  toMeromorphicNFAt (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) (chartAt ℂ x x)
end
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms


