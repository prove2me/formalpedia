-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalDifferentialFiniteness
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalGlobalDifferentialFiniteness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:11:09.732228+00:00
-- url     : https://prove2.me/theorems/9429f852-c767-4ce9-9084-961221f8a9d0
-- title:
--   LPSOriginal Global Differential Finiteness
-- statement:
--   Definitions and structural lemmas for LPSOriginal Global Differential Finiteness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGlobalDifferentialFiniteness.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRegularDifferentialFiniteness
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry MatrixGroups UpperHalfPlane ModularForm Modular Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] originalNativeGlobalComplexModule
include hpos hN
end
end QEC.Coding.TannerLiftedProduct


