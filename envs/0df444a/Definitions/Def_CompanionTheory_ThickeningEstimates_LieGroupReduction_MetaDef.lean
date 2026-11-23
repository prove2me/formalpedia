-- Prove2me | Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaDef
-- name    : CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaDef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:07.66185+00:00
-- url     : https://prove2.me/theorems/cc464288-1075-4f54-b0b7-7649b9358ca3
-- title:
--   Meta Def
-- statement:
--   Definitions and structural lemmas for Meta Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaDef.lean

import Definitions.Def_CompanionTheory_ThickeningEstimates_InnerProductFactorization_EqOfInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E
open scoped Real
namespace CompanionTheory.ThKR
def LocalLift : Prop :=
  ∀ (l : Type) [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), X ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∃ (ε : ℝ) (V : ℝ → Sch l →L[ℂ] Sch l) (W : ℝ → Sch l →L[ℂ] Sch l) (c : ℂ), 0 < ε ∧ (∀ f, V 0 f = f) ∧
      (∀ t, |t| < ε → (∀ f, V t (W t f) = f) ∧ (∀ f, W t (V t f) = f) ∧
        Impl (fun w => NormedSpace.exp (t • X) *ᵥ w) (V t).toLinearMap) ∧
      (∀ t, |t| < ε → ∀ f (lam : Sch l →L[ℂ] ℂ), DifferentiableAt ℝ (fun u => lam (V u f)) t) ∧
      ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun u => lam (V u f)) (lam (quad X f + c • f)) 0
end CompanionTheory.ThKR


