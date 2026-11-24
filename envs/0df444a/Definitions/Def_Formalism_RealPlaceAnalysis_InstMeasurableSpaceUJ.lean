-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
-- name    : Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T11:54:15.754418+00:00
-- url     : https://prove2.me/theorems/c706d157-6c6d-42e1-bed6-78f20e355c95
-- title:
--   Inst Measurable Space UJ
-- statement:
--   Definitions and structural lemmas for Inst Measurable Space UJ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/InstMeasurableSpaceUJ.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Theorems.Thm_Formalism_REAL_isClosedEmbeddingMatrix
import Theorems.Thm_Formalism_REAL_uJLocCompact_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace Formalism.REAL
instance instLocallyCompactUJ (n : ℕ) (ε : Fin n → Bool) : LocallyCompactSpace (UJ ε) :=
  uJLocCompact_of isClosedEmbeddingMatrix n ε
instance instMeasurableSpaceUJ (n : ℕ) (ε : Fin n → Bool) : MeasurableSpace (UJ ε) := borel _
instance instBorelSpaceUJ (n : ℕ) (ε : Fin n → Bool) : BorelSpace (UJ ε) := ⟨rfl⟩
instance instSecondCountableUJ (n : ℕ) (ε : Fin n → Bool) : SecondCountableTopology (UJ ε) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact (isClosedEmbeddingMatrix n ε).1.isInducing.secondCountableTopology
def muG {n : ℕ} (ε : Fin n → Bool) : Measure (UJ ε) := Measure.haar
instance instIsHaarMuG (n : ℕ) (ε : Fin n → Bool) : (muG ε).IsHaarMeasure := by
  unfold muG; infer_instance
def hsG {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : ℝ :=
  hs ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
def Unimodular : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : UJ ε), Measure.map (fun x => x * g) (muG ε) = muG ε
def InvInvariant : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), Measure.map (fun x : UJ ε => x⁻¹) (muG ε) = muG ε
def BallFinite : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (R : ℝ), muG ε {g | hsG g ≤ R} < ⊤
def BallPos : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (R : ℝ), (n : ℝ) < R → 0 < muG ε {g | hsG g < R}
def VolGrowth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
    muG ε {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (2 * n ^ 2))
end Formalism.REAL


