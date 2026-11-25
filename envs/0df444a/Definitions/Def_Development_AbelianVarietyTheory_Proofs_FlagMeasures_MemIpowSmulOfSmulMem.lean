-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:03:29.389574+00:00
-- url     : https://prove2.me/theorems/ec81dba2-8555-56f0-b925-41585d777cbf
-- title:
--   Mem Ipow Smul Of Smul Mem
-- statement:
--   Definitions and structural lemmas for Mem Ipow Smul Of Smul Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIpowSmulOfSmulMem.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.DegCnt
open scoped Pointwise nonZeroDivisors
namespace GlobalTheory.RowStab
section Gen
variable {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
def gen (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) : V →ₗ[K] V :=
  LinearMap.id + ∑ b ∈ J, ((H.B.flip (e b)).smulRight (ρ b) - (H.B.flip (ρ b)).smulRight (e b) +
    ∑ a ∈ J, (c a b • H.B.flip (e b)).smulRight (e a))
end Gen
section Ideal
variable {K : Type} [Field K] [NumberField K]
end Ideal
section Smul
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end Smul
section Star
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Star
end GlobalTheory.RowStab


