-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T17:57:58.160696+00:00
-- url     : https://prove2.me/theorems/f0d9f0a4-9282-48b9-9832-6c80c09eec09
-- title:
--   Inner Eq Zero Of Weight
-- statement:
--   Definitions and structural lemmas for Inner Eq Zero Of Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InnerEqZeroOfWeight.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_cons
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_nil


set_option autoImplicit false
open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open CompanionTheory.D.gk.HwAlg (word word_nil word_cons)
noncomputable section
namespace GlobalTheory.CompanionTheory.KLowSpan
variable {n : ℕ} {ε : Fin n → Bool}
def KLower (ε : Fin n → Bool) (l : List (Fin n × Fin n)) : Prop := ∀ p ∈ l, p.2 < p.1 ∧ ε p.1 = ε p.2
section Alg
variable {U : Type} [AddCommGroup U] [Module ℂ U]
def kLowSpan (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ U) (w : U) : Submodule ℂ U :=
  Submodule.span ℂ {x | ∃ l, KLower ε l ∧ x = word F l w}
variable {F : Fin n → Fin n → Module.End ℂ U} {μ : Fin n → ℝ} {w : U}
def kwt (μ : Fin n → ℝ) (l : List (Fin n × Fin n)) : Fin n → ℝ :=
  μ + (l.map fun p => (Pi.single p.1 1 - Pi.single p.2 1 : Fin n → ℝ)).sum
end Alg
section Unit
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {v : V}
end Unit
end GlobalTheory.CompanionTheory.KLowSpan


