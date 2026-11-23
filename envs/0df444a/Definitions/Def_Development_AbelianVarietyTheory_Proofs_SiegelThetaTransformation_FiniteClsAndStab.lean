-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:55.798634+00:00
-- url     : https://prove2.me/theorems/05eb8b98-a4cb-46a9-9eda-3cf386a315a4
-- title:
--   Finite Cls And Stab
-- statement:
--   Definitions and structural lemmas for Finite Cls And Stab, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClsAndStab.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
import Theorems.Thm_GlobalTheory_SW_Base_mem_stdL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.ClassFin
open GlobalTheory.SW.Base
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
noncomputable def red (M : ℕ) (Λ : Lt E n) (s : ℕ) (h : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n) :
    Λ →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ Ideal.span {(M : 𝓞 E)}) where
  toFun x a := Ideal.Quotient.mk _ ⟨(s : E) * x.1 a, (mem_stdL _).1 (h _ x.2) a⟩
  map_add' x y := by
    funext a
    exact Eq.trans (congrArg _ (Subtype.ext (mul_add _ _ _))) (map_add (Ideal.Quotient.mk _) _ _)
  map_smul' c x := by
    funext a
    refine Eq.trans (congrArg _ ?_) (map_mul (Ideal.Quotient.mk _) c _)
    exact Subtype.ext (mul_left_comm (s : E) (c : E) (x.1 a))
end GlobalTheory.SW.ClassFin
namespace GlobalTheory.SW
end GlobalTheory.SW


