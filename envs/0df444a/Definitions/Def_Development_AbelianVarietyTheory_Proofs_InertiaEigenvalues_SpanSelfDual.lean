-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpanSelfDual
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpanSelfDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:51.913346+00:00
-- url     : https://prove2.me/theorems/937ec58c-5712-4177-9e2f-4f287ceca718
-- title:
--   Span Self Dual
-- statement:
--   Definitions and structural lemmas for Span Self Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanSelfDual.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
namespace GlobalTheory.UnitLemma.OrthoSelfDual
noncomputable def hermLeft {K : UQ} (B : InvAlg K) (x z : B.A) : B.A →ₗ[K.E] K.E where
  toFun y := B.herm x y z
  map_add' a b := by
    unfold InvAlg.herm
    rw [mul_add, add_mul, map_add]
  map_smul' e y := by
    unfold InvAlg.herm
    rw [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply]
end GlobalTheory.UnitLemma.OrthoSelfDual


