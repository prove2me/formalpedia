-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SphericalFunctionInvarianceProperties
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_SphericalFunctionInvarianceProperties
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:13.060312+00:00
-- url     : https://prove2.me/theorems/582da8c0-d488-4289-b717-e265f54de6a4
-- title:
--   Spherical Function Invariance Properties
-- statement:
--   Definitions and structural lemmas for Spherical Function Invariance Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SphericalFunctionInvarianceProperties.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IwasawaDecompositionUpperTriangularStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
namespace GlobalTheory.CompanionTheory.QL.SphLaw
noncomputable def wt {F : Type} [Field F] (nrm : AbsoluteValue F ℝ) {c : ℕ} (χ : Fin c → F → ℂ)
    (b : Matrix (Fin c) (Fin c) F) : ℂ :=
  ∏ i : Fin c, χ i (b i i) * ((nrm (b i i) ^ (((c : ℝ) - 1) / 2 - (i : ℕ)) : ℝ) : ℂ)
end GlobalTheory.CompanionTheory.QL.SphLaw


