-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:08.660662+00:00
-- url     : https://prove2.me/theorems/afd2be48-9834-4ee1-b551-77fe6e3e06b1
-- title:
--   Is SMul Regular Coker Dual Map Of Exact Fibres
-- statement:
--   Definitions and structural lemmas for Is SMul Regular Coker Dual Map Of Exact Fibres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
namespace GlobalTheory
namespace DualCokernel
variable {R : Type} [CommRing R]
section Depth
variable [IsLocalRing R]
abbrev ExtZero (M : Type) [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R M) n)
variable [IsNoetherianRing R]
end Depth
section Complex
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)
end Complex
end DualCokernel
end GlobalTheory


