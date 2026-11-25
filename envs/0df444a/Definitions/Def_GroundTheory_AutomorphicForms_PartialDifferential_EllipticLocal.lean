-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
-- name    : GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:28.885863+00:00
-- url     : https://prove2.me/theorems/7ae04448-61c2-4ab8-8b16-32c7ed5fee68
-- title:
--   Elliptic Local
-- statement:
--   Definitions and structural lemmas for Elliptic Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_comp_left
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
section Symbols
variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E)
def symb0 : E → ℂ := fun ξ ↦ (2 * Real.pi * Complex.I) ^ m * prinSymb c w ξ
def rhoSymb (μ : ℝ) : E → ℂ := fun ξ ↦ weight (-2) ((Real.sqrt μ : ℂ) * symb0 c w ξ)
def qSymb (μ : ℝ) : E → ℂ := fun ξ ↦ (μ : ℂ) * starRingEnd ℂ (symb0 c w ξ) * rhoSymb c w μ ξ
def qNSymb (μ : ℝ) (N : ℕ) : E → ℂ :=
  fun ξ ↦ qSymb c w μ ξ * ∑ j ∈ Finset.range N, rhoSymb c w μ ξ ^ j
def rNSymb (μ : ℝ) (N : ℕ) : E → ℂ := fun ξ ↦ rhoSymb c w μ ξ ^ N
end Symbols
section Bounds
variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) {cl Cu : ℝ}
variable (hcl : 0 < cl) (hCu : 0 ≤ Cu) (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 c w ξ‖)
  (hup : ∀ ξ, ‖symb0 c w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup
end Bounds
def bumpR (x₀ : E) {r : ℝ} (hr : 0 < r) : ContDiffBump x₀ := ⟨r, 2 * r, hr, by linarith⟩
def bump (x₀ : E) {r : ℝ} (hr : 0 < r) : 𝓢(E, ℂ) :=
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (bumpR x₀ hr : E → ℝ)) :=
    (bumpR x₀ hr).hasCompactSupport.comp_left rfl
  have h₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ (bumpR x₀ hr : E → ℝ)) :=
    Complex.ofRealCLM.contDiff.comp (bumpR x₀ hr).contDiff
  h₁.toSchwartzMap h₂
section Local
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E)
def locCoeff {δ : ℝ} (hδ : 0 < δ) (i : Fin n) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) (a i) - a i x₀ • bump x₀ hδ
def locM {δ : ℝ} (hδ : 0 < δ) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  prinOp (locCoeff a x₀ hδ) w + smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) ∘L N
def P0 : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) := constOp w (fun i ↦ a i x₀)
end Local
def OpBound (A : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (s t C : ℝ) : Prop :=
  ∀ u : 𝓢'(E, ℂ), MemSobolev s 2 u → sob t (A u) ≤ ENNReal.ofReal C * sob s u
namespace OpBound
variable {A B : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s t r C D : ℝ}
end OpBound
section Q
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (x₀ : E)
def Qop (μ : ℝ) (k : ℕ) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  fourierMultiplierCLM ℂ (qNSymb (fun i ↦ a i x₀) w μ k)
def Rop (μ : ℝ) (k : ℕ) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  fourierMultiplierCLM ℂ (rNSymb (fun i ↦ a i x₀) w μ k)
variable {cl Cu : ℝ} (hcl : 0 < cl) (hCu : 0 ≤ Cu)
  (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 (fun i ↦ a i x₀) w ξ‖)
  (hup : ∀ ξ, ‖symb0 (fun i ↦ a i x₀) w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup
end Q
section Small
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E)
end Small
section Exists
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E) {cl Cu : ℝ} (hcl : 0 < cl) (hCu : 0 ≤ Cu)
  (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 (fun i ↦ a i x₀) w ξ‖)
  (hup : ∀ ξ, ‖symb0 (fun i ↦ a i x₀) w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup
end Exists
end
end GroundTheory.Automorphic.Sobolev


