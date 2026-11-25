-- Prove2me | Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeDuality_GlRelTau
-- name    : CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeDuality_GlRelTau
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:30.381597+00:00
-- url     : https://prove2.me/theorems/971d9997-acb3-4210-a4cb-6d369ab1efc1
-- title:
--   Gl Rel Tau
-- statement:
--   Definitions and structural lemmas for Gl Rel Tau, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeDuality/GlRelTau.lean

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
variable {n : ℕ}
theorem glRel_tau (X : GMod n) : GlRel (fun a b => -X.E b a) := by
  intro a b c d
  have h := X.gl b a d c
  simp only [neg_mul_neg]
  rw [h]
  rcases eq_or_ne a d with h1 | h1 <;> rcases eq_or_ne b c with h2 | h2
  · subst h1; subst h2; simp; abel
  · subst h1; simp [h2, Ne.symm h2]
  · subst h2; simp [h1, Ne.symm h1]
  · simp [h1, h2, Ne.symm h1, Ne.symm h2]
def tauMod (X : GMod n) : GMod n := ⟨X.V, fun a b => -X.E b a, glRel_tau X⟩
def QdetTau : Prop :=
  ∀ (n : ℕ) (X : GMod n) (u : ℂ), qdet (tauMod X).E u = ((-1 : ℂ) ^ n) • qdet X.E (-u + ((n : ℂ) - 1))
end CompanionTheory.RgExh.Hk


