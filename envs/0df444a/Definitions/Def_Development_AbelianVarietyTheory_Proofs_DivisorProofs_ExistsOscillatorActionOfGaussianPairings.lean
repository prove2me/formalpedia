-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:13.852985+00:00
-- url     : https://prove2.me/theorems/c8afbadb-6d77-42e2-a60f-3ad0069b05bd
-- title:
--   Exists Oscillator Action Of Gaussian Pairings
-- statement:
--   Definitions and structural lemmas for Exists Oscillator Action Of Gaussian Pairings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_twist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
namespace GlobalTheory.RealWeil.Osc
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
def intw (ρ' : V → B →L[ℂ] B) (T : B →L[ℂ] B) (ρ : V → B →L[ℂ] B) (f : B) : B := ∫ w, ρ' w (T (ρ (-w) f))
variable {T : B →L[ℂ] B}
section Norm
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Φ : B →L[ℂ] H}
end Norm
section Group
variable {G : Type} [Group G] {k : G →* (V →L[ℝ] V)} {c : G → ℂ}
abbrev pr (h : IsHeis (omJ J) ρ) (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y) (g : G) : B →L[ℂ] B :=
  proj (h.twist (k g) (hk g))
def vacOp (h : IsHeis (omJ J) ρ) (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y) (c : G → ℂ) (g : G) :
    B →L[ℂ] B := c g • (pr h hk g).comp (proj h)
def osc (h : IsHeis (omJ J) ρ) (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y) (c : G → ℂ) (g : G) (f : B) : B :=
  intw (fun v => ρ (k g v)) (vacOp h hk c g) ρ f
variable (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (hk : ∀ g x y, omJ J (k g x) (k g y) = omJ J x y)
include hJ
end Group
end GlobalTheory.RealWeil.Osc
end


