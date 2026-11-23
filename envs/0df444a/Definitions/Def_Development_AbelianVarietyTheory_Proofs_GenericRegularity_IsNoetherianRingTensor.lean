-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsNoetherianRingTensor
-- name    : Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsNoetherianRingTensor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:33:00.149796+00:00
-- url     : https://prove2.me/theorems/60e152e0-2f5b-4270-a7d3-a8d06d18746f
-- title:
--   Is Noetherian Ring Tensor
-- statement:
--   Definitions and structural lemmas for Is Noetherian Ring Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsNoetherianRingTensor.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory.BaseChangeComponents
variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
noncomputable def incl (R : Subalgebra K Ω) : F ⊗[K] R →+* F ⊗[K] Ω :=
  (Algebra.TensorProduct.map (AlgHom.id K F) R.val).toRingHom
noncomputable def denoms (R : Subalgebra K Ω) : Submonoid (F ⊗[K] R) :=
  (nonZeroDivisors R).map (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := R))
end GlobalTheory.BaseChangeComponents


