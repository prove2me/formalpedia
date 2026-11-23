-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:41.21964+00:00
-- url     : https://prove2.me/theorems/fae1facf-47da-40ab-8238-90a7da95843f
-- title:
--   Hecke Phi Fourier Transform Rapid Decay
-- statement:
--   Definitions and structural lemmas for Hecke Phi Fourier Transform Rapid Decay, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
namespace GlobalTheory.HeckeTwo.HDecay
end GlobalTheory.HeckeTwo.HDecay
namespace GlobalTheory.HeckeTwo.HDecay
variable (σ : ℂ) (y : ℝ)
def gI (t : ℝ) : ℂ := ((t : ℂ) + (y : ℂ) * I)⁻¹
def hI (t : ℝ) : ℂ := ((t : ℂ) - (y : ℂ) * I)⁻¹
def eF (t : ℝ) : ℂ := Complex.exp (-σ * (Real.log (t ^ 2 + y ^ 2) : ℂ))
def wF (a b : ℕ) (t : ℝ) : ℂ := gI y t ^ (a + 2) * hI y t ^ b * eF σ y t
variable {y}
end GlobalTheory.HeckeTwo.HDecay
namespace GlobalTheory.HeckeTwo.HDecay
variable (σ : ℂ) (y : ℝ)
def wSpan : Submodule ℂ (ℝ → ℂ) := Submodule.span ℂ (Set.range fun p : ℕ × ℕ => wF σ y p.1 p.2)
variable {σ y}
end GlobalTheory.HeckeTwo.HDecay
namespace GlobalTheory.HeckeTwo
end GlobalTheory.HeckeTwo


