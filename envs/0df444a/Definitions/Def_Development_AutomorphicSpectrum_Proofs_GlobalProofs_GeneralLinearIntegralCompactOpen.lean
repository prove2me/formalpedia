-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpen
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:42.191165+00:00
-- url     : https://prove2.me/theorems/8e64ae5f-72d7-4c47-b4ac-c9f9c0f0bac9
-- title:
--   General Linear Integral Compact Open
-- statement:
--   Definitions and structural lemmas for General Linear Integral Compact Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearIntegralCompactOpen.lean

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
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
noncomputable section
namespace GlobalTheory.CompanionTheory.QLTop
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
def intSet (O : Subring F) (n : ℕ) : Set (Matrix (Fin n) (Fin n) F) := {M | IsInt O M}
end GlobalTheory.CompanionTheory.QLTop


