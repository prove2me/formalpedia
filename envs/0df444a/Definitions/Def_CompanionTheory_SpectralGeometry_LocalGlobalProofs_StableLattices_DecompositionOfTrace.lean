-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfTrace
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfTrace
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T03:45:11.317281+00:00
-- url     : https://prove2.me/theorems/6624fbfc-181f-55ce-a469-2ca93f89d4e4
-- title:
--   Decomposition Of Trace
-- statement:
--   Definitions and structural lemmas for Decomposition Of Trace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DecompositionOfTrace.lean

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
namespace GlobalTheory.CompanionTheory.ZuckDecOfTrace
universe u
variable {O : Type u} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
  {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop}
def homSub (hc : IsLinCat N Hom) (a b : O) : Submodule ℂ (N a →ₗ[ℂ] N b) where
  carrier := {f | Hom a b f}
  add_mem' := fun {f g} hf hg => hc.add a b f g hf hg
  zero_mem' := hc.zero a b
  smul_mem' := fun c f hf => hc.smul a b c f hf
def post (hc : IsLinCat N Hom) (a : O) {b c : O} (f : N b →ₗ[ℂ] N c) (hf : Hom b c f) :
    homSub hc a b →ₗ[ℂ] homSub hc a c where
  toFun w := ⟨f ∘ₗ w.1, hc.comp _ _ _ _ _ w.2 hf⟩
  map_add' v w := Subtype.ext (by simp [LinearMap.comp_add])
  map_smul' c w := Subtype.ext (by simp [LinearMap.comp_smul])
end GlobalTheory.CompanionTheory.ZuckDecOfTrace


