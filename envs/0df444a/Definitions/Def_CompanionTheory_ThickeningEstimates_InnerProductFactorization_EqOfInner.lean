-- Prove2me | Definitions.Def_CompanionTheory_ThickeningEstimates_InnerProductFactorization_EqOfInner
-- name    : CompanionTheory_ThickeningEstimates_InnerProductFactorization_EqOfInner
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:16.417389+00:00
-- url     : https://prove2.me/theorems/6e156d84-5aad-4248-821a-8464ed845335
-- title:
--   Eq Of Inner
-- statement:
--   Definitions and structural lemmas for Eq Of Inner, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/InnerProductFactorization/EqOfInner.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Theorems.Thm_GlobalTheory_RealWeil_schwartzToL2_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform
namespace CompanionTheory.ThKF.E
variable {l : Type} [Fintype l] [DecidableEq l]
structure Impl (s : (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (S : Sch l →ₗ[ℂ] Sch l) : Prop where
  norm : ∀ f, ‖(S f).toLp 2 volume‖ = ‖f.toLp 2 volume‖
  impl : ∀ w (f g : Sch l), ⇑g = rhoFun w f → ⇑(S g) = rhoFun (s w) (S f)
theorem Impl.inner {s} {S : Sch l →ₗ[ℂ] Sch l} (h : Impl s S) (f g : Sch l) :
    inner ℂ ((S f).toLp 2 volume) ((S g).toLp 2 volume) = inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  have e : ∀ (u v : Sch l) (c : ℂ), u.toLp 2 volume + c • v.toLp 2 volume = (u + c • v).toLp 2 volume := fun u v c => by
    simp only [← schwartzToL2_apply, map_add, map_smul]
  have e' : ∀ (u v : Sch l) (c : ℂ), u.toLp 2 volume - c • v.toLp 2 volume = (u - c • v).toLp 2 volume := fun u v c => by
    simp only [← schwartzToL2_apply, map_sub, map_smul]
  have e1 := e (S f) (S g) 1
  have e2 := e' (S f) (S g) 1
  have e3 := e f g 1
  have e4 := e' f g 1
  simp only [one_smul] at e1 e2 e3 e4
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, e1, e2, e3, e4, e, e, e', e', ← map_add, ← map_sub,
    ← map_smul, ← map_add, ← map_sub, h.norm, h.norm, h.norm, h.norm]
end CompanionTheory.ThKF.E


