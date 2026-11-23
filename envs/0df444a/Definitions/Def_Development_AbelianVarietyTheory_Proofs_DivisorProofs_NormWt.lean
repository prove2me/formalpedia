-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:55.267489+00:00
-- url     : https://prove2.me/theorems/a69b0866-0897-49fc-932c-ecd3c5d729c9
-- title:
--   Norm Wt
-- statement:
--   Definitions and structural lemmas for Norm Wt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormWt.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace GlobalTheory.HeckeStrip
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
def wt (φ : I → K →+* ℂ) (n : I → ℤ) (α : K) : ℂ :=
  ∏ i, (φ i α / ((‖φ i α‖ : ℝ) : ℂ)) ^ (-n i)
def pval (F : 𝓞 K → ℂ) (φ : I → K →+* ℂ) (n : I → ℤ) (J : Ideal (𝓞 K)) [J.IsPrincipal] : ℂ :=
  F (Submodule.IsPrincipal.generator J) * wt φ n ((Submodule.IsPrincipal.generator J : 𝓞 K) : K)
def pSeries (F : 𝓞 K → ℂ) (φ : I → K →+* ℂ) (n : I → ℤ) (s : ℂ) : ℂ :=
  ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal},
    (haveI := J.2.2; pval F φ n J.1) * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)
end GlobalTheory.HeckeStrip


