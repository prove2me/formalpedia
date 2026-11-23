-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HormanderLemma
-- name    : ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HormanderLemma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:25:36.905493+00:00
-- url     : https://prove2.me/theorems/2a6a545f-0aef-4db2-a350-e706b8ead1b8
-- title:
--   Hormander Lemma
-- statement:
--   Definitions and structural lemmas for Hormander Lemma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/MinimalSolutions/HormanderLemma.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates
open scoped InnerProductSpace
section WeakAdjLemmas
variable {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
theorem weakAdj_zero (ι : E →ₗ[ℂ] H₁) (t : E →ₗ[ℂ] H₂) : WeakAdj ι t 0 0 := by
  intro g
  simp
theorem WeakAdj.add {ι : E →ₗ[ℂ] H₁} {t : E →ₗ[ℂ] H₂} {f f' : H₂} {w w' : H₁}
    (h : WeakAdj ι t f w) (h' : WeakAdj ι t f' w') : WeakAdj ι t (f + f') (w + w') := by
  intro g
  rw [inner_add_right, inner_add_right, h g, h' g]
theorem WeakAdj.smul {ι : E →ₗ[ℂ] H₁} {t : E →ₗ[ℂ] H₂} {f : H₂} {w : H₁}
    (h : WeakAdj ι t f w) (a : ℂ) : WeakAdj ι t (a • f) (a • w) := by
  intro g
  rw [inner_smul_right, inner_smul_right, h g]
def weakAdjGraph (ι : E →ₗ[ℂ] H₁) (t : E →ₗ[ℂ] H₂) : Submodule ℂ (H₂ × H₁) where
  carrier := {p | WeakAdj ι t p.1 p.2}
  add_mem' := fun ha hb => WeakAdj.add ha hb
  zero_mem' := weakAdj_zero ι t
  smul_mem' := fun a _ hp => WeakAdj.smul hp a
end WeakAdjLemmas
end ReciprocityTheory.L2DbarEstimates


