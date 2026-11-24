-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionForms
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineSectionForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:23.683259+00:00
-- url     : https://prove2.me/theorems/714e8c8f-04ff-4f09-a6ba-78aa5e580d9c
-- title:
--   PFlag Line Section Forms
-- statement:
--   Definitions and structural lemmas for PFlag Line Section Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineSectionForms.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineSection
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
namespace FlagLineSectionProof
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type*} [Field Ω]
  {F : Type*} [Field F] [Algebra F Ω] {N M : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
  {Φ : Type*} [Field Φ] [Algebra Ω Φ]
abbrev projMap (F : Type*) [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    MRing (bundleIdx ι M) F →+* MvPolynomial (Option K) Φ :=
  eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω))) (fun p => C (projCoord y w φ t p) * X p.1)
def tMon (α : K → ℕ) : MvPolynomial (Option K) Φ := ∏ k, X (some k) ^ α k
def liftN (α : K → ℕ) : Option K → ℕ := fun o => Option.elim o 0 α
def chartMon (F : Type*) [Field F] (M : ℕ) (c : ∀ k, ι k) (α : K → ℕ) : MRing (bundleIdx ι M) F :=
  ∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ α k
variable (F M) in

def IsChartForm (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (a : Ω) (n : ℕ)
    (A : MRing (bundleIdx ι M) F) : Prop :=
  IsMultiHomog A (liftN fun _ => n) ∧
    projMap F y w φ t A = C (algebraMap Ω Φ (a * segreVec y c ^ n)) * tMon (fun _ => n)
def chartZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℤ) : Ω := ∏ k, y ⟨k, c k⟩ ^ e k
end FlagLineSectionProof
end
end GroundTheory.Heights₂.Heights.NumbersDVR


