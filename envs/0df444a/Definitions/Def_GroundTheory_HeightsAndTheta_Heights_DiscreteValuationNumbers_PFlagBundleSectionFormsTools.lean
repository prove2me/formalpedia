-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:58.799995+00:00
-- url     : https://prove2.me/theorems/2a9b5fa0-cd2f-46a2-9a48-7188d9457e95
-- title:
--   PFlag Bundle Section Forms Tools
-- statement:
--   Definitions and structural lemmas for PFlag Bundle Section Forms Tools, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleSectionFormsTools.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
set_option linter.unusedSectionVars false
namespace FlagBundleSectionForms
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
def chartPow (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ d k
section Dual
variable {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
end Dual
section Forms
variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
def liftNat (α : K → ℕ) : Option K → ℕ := fun o => Option.elim o 0 α
def chartMono (M : ℕ) (c : ∀ k, ι k) (α : K → ℕ) : MRing (bundleIdx ι M) F :=
  ∏ k, X (⟨some k, c k⟩ : Σ o, bundleIdx ι M o) ^ α k
end Forms
end FlagBundleSectionForms
end
end GroundTheory.Heights₂.Heights.NumbersDVR


