-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenPi
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenPi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:07.828829+00:00
-- url     : https://prove2.me/theorems/9e0934dd-c41e-4be6-b986-bb23f8a6db66
-- title:
--   Quaternion Norm One Trace Open Pi
-- statement:
--   Definitions and structural lemmas for Quaternion Norm One Trace Open Pi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenPi.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace GlobalTheory.QSA
namespace TraceOpenPi
variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] {a b : ∀ i, R i}
def comp (i : ι) (x : ℍ[∀ i, R i, a, b]) : ℍ[R i, a i, b i] :=
  ⟨x.re i, x.imI i, x.imJ i, x.imK i⟩
def glue (u : ∀ i, ℍ[R i, a i, b i]) : ℍ[∀ i, R i, a, b] :=
  ⟨fun i => (u i).re, fun i => (u i).imI, fun i => (u i).imJ, fun i => (u i).imK⟩
end TraceOpenPi
end GlobalTheory.QSA


