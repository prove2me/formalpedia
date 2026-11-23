-- Prove2me | solution 1 for AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.schA_conj_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:03.342943+00:00
-- url     : https://prove2.me/submissions/ed5060a8-d418-4737-ae10-fafe4fa7a6d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdelicSchwartzSpaceClosedUnderConjReflection
import Theorems.Thm_AdelicReflection_GlobalTheory_CompanionTheory_AdelicReflect_conjNeg_mem_SB
import Theorems.Thm_AdelicReflection_GlobalTheory_CompanionTheory_AdelicReflect_conj_pureA_neg

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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ φ hφ
  unfold GlobalTheory.WeilM.schA at hφ ⊢
  induction hφ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    refine Submodule.subset_span ⟨conjNeg f, fun y => starRingEnd ℂ (g (-y)), conjNeg_mem_SB hg, ?_⟩
    funext x
    rw [conj_pureA_neg]
    congr 1
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext x
    simp
  | add a b _ _ ha hb =>
    convert Submodule.add_mem _ ha hb using 1
    funext x
    simp
  | smul c a _ ha =>
    convert Submodule.smul_mem _ (starRingEnd ℂ c) ha using 1
    funext x
    simp
end AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect
