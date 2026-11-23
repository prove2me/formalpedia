-- Prove2me | solution 1 for AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.conj_pureA_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:37.21959+00:00
-- url     : https://prove2.me/submissions/151b1451-4f21-4346-adfe-14e443431f7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdelicSchwartzSpaceClosedUnderConjReflection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AdelicReflection
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
open AdelicReflection.GlobalTheory AdelicReflection.GlobalTheory.CompanionTheory AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect
namespace AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect
theorem _root_.solution (F : Type) [Field F] [NumberField F] {κ : Type}
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → AdeleRing (𝓞 F) F) :
    starRingEnd ℂ (GlobalTheory.WeilM.pureA F f g (-x)) =
      GlobalTheory.WeilM.pureA F (fun y => starRingEnd ℂ (f (-y))) (fun y => starRingEnd ℂ (g (-y))) x := by
  simp only [GlobalTheory.WeilM.pureA, map_mul]
  congr 3
  funext i
  rw [Pi.neg_apply, Pi.neg_apply, ← map_neg]
  rfl
end AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect
