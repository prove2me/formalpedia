-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_CoefMemFlagSec
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_CoefMemFlagSec
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:37:25.320708+00:00
-- url     : https://prove2.me/theorems/04c928f2-53bc-4ce3-ad5f-c95cd42673ec
-- title:
--   Coef Mem Flag Sec
-- statement:
--   Definitions and structural lemmas for Coef Mem Flag Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/CoefMemFlagSec.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
def IsFlagSec (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ P X.dom ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x
def flagSec {K : Type} [Field K] (σ : K →+* ℂ) (X : Data E r) (la : Wt X.Ψ r) :
    Submodule K (FnVia σ (Frame X.Ψ r)) where
  carrier := {P | IsFlagSec X la P ∧ ∀ x, x ∉ X.dom → (show Frame X.Ψ r → ℂ from P) x = 0}
  zero_mem' := ⟨⟨differentiableOn_const (0 : ℂ), fun _ _ _ _ => (mul_zero _).symm⟩, fun _ _ => rfl⟩
  add_mem' := by
    intro P Q hP hQ
    refine ⟨⟨hP.1.1.add hQ.1.1, fun x hx b hb => ?_⟩, fun x hx => ?_⟩
    · change (show Frame X.Ψ r → ℂ from P) (rmul x b) + (show Frame X.Ψ r → ℂ from Q) (rmul x b) =
        bchar la b * ((show Frame X.Ψ r → ℂ from P) x + (show Frame X.Ψ r → ℂ from Q) x)
      rw [mul_add]
      exact congrArg₂ (· + ·) (hP.1.2 x hx b hb) (hQ.1.2 x hx b hb)
    · change (show Frame X.Ψ r → ℂ from P) x + (show Frame X.Ψ r → ℂ from Q) x = 0
      rw [hP.2 x hx, hQ.2 x hx, add_zero]
  smul_mem' := by
    intro a P hP
    refine ⟨⟨hP.1.1.const_mul (σ a), fun x hx b hb => ?_⟩, fun x hx => ?_⟩
    · change σ a * (show Frame X.Ψ r → ℂ from P) (rmul x b) =
        bchar la b * (σ a * (show Frame X.Ψ r → ℂ from P) x)
      rw [mul_left_comm]
      exact congrArg (σ a * ·) (hP.1.2 x hx b hb)
    · change σ a * (show Frame X.Ψ r → ℂ from P) x = 0
      rw [hP.2 x hx, mul_zero]
end GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction


