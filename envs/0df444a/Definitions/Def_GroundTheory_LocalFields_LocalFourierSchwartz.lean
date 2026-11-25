-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
-- name    : GroundTheory_LocalFields_LocalFourierSchwartz
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T05:55:01.756969+00:00
-- url     : https://prove2.me/theorems/d8dd5f0c-ccc2-4b7c-99b8-002b3efd8efd
-- title:
--   Local Fourier Schwartz
-- statement:
--   Definitions and structural lemmas for Local Fourier Schwartz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierSchwartz.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
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
open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section SchwartzBruhat
variable (K) in

def schwartzBruhat : Submodule ℂ (K → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.smul_left (f := fun _ => c)⟩
end SchwartzBruhat
section Fourier
variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
variable (ψ : AddChar K Circle)
def localFourier (f : K → ℂ) (y : K) : ℂ := ∫ x, f x * (ψ (x * y) : ℂ) ∂μ
variable {ψ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1
end Fourier
end GroundTheory.LocalField


