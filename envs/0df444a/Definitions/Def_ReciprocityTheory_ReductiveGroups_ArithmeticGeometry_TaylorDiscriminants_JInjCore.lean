-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JInjCore
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JInjCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:15.549665+00:00
-- url     : https://prove2.me/theorems/61239d8f-49f8-4130-bd7a-432f8a2d4d71
-- title:
--   JInj Core
-- statement:
--   Definitions and structural lemmas for JInj Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/JInjCore.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.TB
def IndepDescentSt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] [Algebra K F] [IsGalois K F] (ι : F →+* ℂ)
    (C : Type) [AddCommGroup C] [Module K C] (Pt : Type) (v : C →ₗ[K] (Pt → F))
    (act : (F ≃ₐ[K] F) → Pt → Pt),
    (∀ g, Function.Bijective (act g)) →
    (∀ g f y, v f (act g y) = g (v f y)) →
    Function.Injective v →
    ∀ (n : ℕ) (b : Fin n → C), LinearIndependent K b →
      LinearIndependent ℂ (fun i => (fun y => ι (v (b i) y) : Pt → ℂ))
example (h : IndepDescentSt) :
    LinearIndependent ℂ (fun _ : Fin 1 => (fun _ => ((1 : ℚ) : ℂ) : Unit → ℂ)) := by
  have hv : Function.Injective (LinearMap.pi (fun _ : Unit => LinearMap.id) : ℚ →ₗ[ℚ] (Unit → ℚ)) := by
    intro x y hxy
    simpa using congrFun hxy ()
  have := h ℚ ℚ (Rat.castHom ℂ) ℚ Unit (LinearMap.pi fun _ => LinearMap.id) (fun _ y => y)
    (fun _ => Function.bijective_id) (fun g f y => by simp) hv 1 (fun _ => 1)
    (linearIndependent_unique_iff.mpr one_ne_zero)
  simpa using this
end ReciprocityTheory.ChartRestriction.G.TB


