-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_Energy
-- name    : ReciprocityTheory_AnalyticForms_LeviForms_Energy
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:33.02806+00:00
-- url     : https://prove2.me/theorems/58e62f2b-6ddf-5284-8906-b76df9c79c2b
-- title:
--   Energy
-- statement:
--   Definitions and structural lemmas for Energy, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/Energy.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.P
open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas
noncomputable section
def MixFamZeroStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (Φ : LocPot X) (w : X → ℝ),
    mixFam e 0 Φ w = fun _ => Φ
def MixFamSuccStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (Φ : LocPot X) (w : X → ℝ) (i : ℕ) (hi : i < e),
    mixFam e (i + 1) Φ w = Function.update (mixFam e i Φ w) ⟨i, hi⟩ (Φ + LocPot.ofFun w) ∧
      mixFam e i Φ w ⟨i, hi⟩ = Φ
def MIntUpdateAddStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (F : Fin (e + 1) → LocPot X) (k : Fin (e + 1)) (P Q : LocPot X),
    (∀ i, IsPotential A (F i)) → IsPotential A P → IsPotential A Q → ∀ g : X → ℝ, Continuous g →
      mInt A (Function.update F k (P + Q)) g =
        mInt A (Function.update F k P) g + mInt A (Function.update F k Q) g
def MIntUpdateNonposStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (F : Fin (e + 1) → LocPot X) (k : Fin (e + 1)) (v : X → ℝ),
    A.Smooth v → (∀ i, IsPotential A (F i)) → (∀ i, i ≠ k → IsPsh A (F i)) →
      mInt A (Function.update F k (LocPot.ofFun v)) v ≤ 0
end
end ReciprocityTheory.AnForm.P


