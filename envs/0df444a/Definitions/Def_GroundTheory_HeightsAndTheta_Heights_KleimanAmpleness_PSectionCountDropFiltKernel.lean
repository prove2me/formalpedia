-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropFiltKernel
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropFiltKernel
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:22:27.891464+00:00
-- url     : https://prove2.me/theorems/c6e29712-e19f-5e4c-bfdb-e4bd7ef9f9de
-- title:
--   PSection Count Drop Filt Kernel
-- statement:
--   Definitions and structural lemmas for PSection Count Drop Filt Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropFiltKernel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltKernelSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
namespace SectionCount.Drop.Filt.Kernel
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
def ratioPow (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (j : Fin (N + 1)) (b : ℕ) :
    chartRing S x I :=
  ⟨x j ^ b / x i ^ b, X j ^ b, X i ^ b, b, pow_mem (X_mem_monos hi) b, isHomogeneous_X_pow _ _,
    isHomogeneous_X_pow _ _, by simp⟩
end SectionCount.Drop.Filt.Kernel
end
end GroundTheory.Heights₂.Heights.Kleiman


