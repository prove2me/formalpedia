-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
-- name    : GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:50:36.715692+00:00
-- url     : https://prove2.me/theorems/0e0202d6-87e2-4c48-8c38-c33a1e7dd270
-- title:
--   Elliptic Operators
-- statement:
--   Definitions and structural lemmas for Elliptic Operators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply


set_option autoImplicit false
namespace GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
def HasOrder (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (k : ℝ) : Prop :=
  ∀ s : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : 𝓢'(E, ℂ), MemSobolev s 2 u →
    sob (s - k) (T u) ≤ ENNReal.ofReal C * sob s u
namespace HasOrder
variable {T T₁ T₂ : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {k k₁ k₂ : ℝ}
theorem id : HasOrder (ContinuousLinearMap.id ℂ 𝓢'(E, ℂ)) 0 :=
  fun s ↦ ⟨1, zero_le_one, fun u _ ↦ by simp⟩
end HasOrder
def IsLocal (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) : Prop :=
  ∀ U : Set E, IsOpen U → ∀ u : 𝓢'(E, ℂ), Distribution.IsVanishingOn u U →
    Distribution.IsVanishingOn (T u) U
namespace IsLocal
variable {T T₁ T₂ : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)}
end IsLocal
def comm (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (ψ : 𝓢(E, ℂ)) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  T ∘L smulLeftCLM ℂ (ψ : E → ℂ) - smulLeftCLM ℂ (ψ : E → ℂ) ∘L T
def derivSymb {k : ℕ} (w : Fin k → E) (ξ : E) : ℂ :=
  ∏ j, (2 * Real.pi * Complex.I) * ((inner ℝ ξ (w j) : ℝ) : ℂ)
def prinSymb {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) (ξ : E) : ℂ :=
  ∑ i, c i * ∏ j, ((inner ℝ ξ (w i j) : ℝ) : ℂ)
def prinOp {ι : Type*} [Fintype ι] {m : ℕ} (a : ι → 𝓢(E, ℂ)) (w : ι → Fin m → E) :
    𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  ∑ i, smulLeftCLM ℂ (a i : E → ℂ) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i)
section prinOp
variable {ι : Type*} [Fintype ι] {m : ℕ} (a : ι → 𝓢(E, ℂ)) (w : ι → Fin m → E)
def constOp (c : ι → ℂ) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  ∑ i, c i • iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i)
end prinOp
def IsEllipticAt (T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (m : ℕ) (x₀ : E) : Prop :=
  ∃ (n : ℕ) (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)),
    T = prinOp a w + N ∧ HasOrder N ((m : ℝ) - 1) ∧ IsLocal N ∧
      ∀ ξ : E, ξ ≠ 0 → prinSymb (fun i ↦ a i x₀) w ξ ≠ 0
namespace IsEllipticAt
variable {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} {x₀ : E}
end IsEllipticAt
end
end GroundTheory.Automorphic.Sobolev


