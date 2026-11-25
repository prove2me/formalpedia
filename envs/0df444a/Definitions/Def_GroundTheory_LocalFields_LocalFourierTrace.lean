-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
-- name    : GroundTheory_LocalFields_LocalFourierTrace
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:48.514037+00:00
-- url     : https://prove2.me/theorems/8a390580-4c26-5b61-96dc-53f1a8cc6496
-- title:
--   Local Fourier Trace
-- statement:
--   Definitions and structural lemmas for Local Fourier Trace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel
open scoped nonZeroDivisors
attribute [local instance high] FaithfulSMul.to_isTorsionFree
section Dual
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
end Dual
section TraceChar
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (L) in

def traceChar (ψ : AddChar K Circle) : AddChar L Circle :=
  ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom
variable [ValuativeRel K] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]
variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1
variable [Algebra.IsSeparable K L]
end TraceChar
end GroundTheory.LocalField


