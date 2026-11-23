-- Prove2me | Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
-- name    : CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:15.857907+00:00
-- url     : https://prove2.me/theorems/64d7d375-168d-478e-ae88-208a8e4bcc5a
-- title:
--   Iso Of Integral
-- statement:
--   Definitions and structural lemmas for Iso Of Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
namespace CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]
abbrev Eu (l : Type) : Type := EuclideanSpace ℝ l
def rf (p q : Eu l) (f : Eu l → ℂ) : Eu l → ℂ :=
  fun x => exp (((2 * π * ⟪q, x⟫ + π * ⟪p, q⟫ : ℝ) : ℂ) * I) * f (x + p)
def Intw (S : Sch l →L[ℂ] Sch l) (p q p' q' : Eu l) : Prop :=
  ∀ f g : Sch l, ⇑g = rf p q f → ⇑(S g) = rf p' q' (S f)
def Iso (S : Sch l →L[ℂ] Sch l) : Prop := ∀ f, ‖schwartzToL2 l (S f)‖ = ‖schwartzToL2 l f‖
def ph (S : Eu l →L[ℝ] Eu l) : Sch l →L[ℂ] Sch l :=
  smulLeftCLM ℂ fun x : Eu l => exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I)
open Classical in

def dil (B : Eu l →L[ℝ] Eu l) : Sch l →L[ℂ] Sch l :=
  if h : IsUnit B then compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.ofUnit h.unit) else 0
def fou (l : Type) [Fintype l] : Sch l →L[ℂ] Sch l := FourierTransform.fourierCLM ℂ (Sch l)
def fouInv (l : Type) [Fintype l] : Sch l →L[ℂ] Sch l := FourierTransform.fourierInvCLM ℂ (Sch l)
def big (Ai B C : Eu l →L[ℝ] Eu l) (c : ℝ) : Sch l →L[ℂ] Sch l :=
  ph (C * Ai) * (((c : ℂ) • dil Ai) * (fou l * (ph (-(Ai * B)) * fouInv l)))
end CompanionTheory.ThKR.LL


