-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:52:35.077795+00:00
-- url     : https://prove2.me/theorems/491b9cd6-2231-5e11-a0cf-9d3c62324d06
-- title:
--   Exists Translate Jet Ne Zero
-- statement:
--   Definitions and structural lemmas for Exists Translate Jet Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
namespace GlobalTheory
namespace ThetaJet
section Algebra
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
end Algebra
variable {ι : Type} [Fintype ι]
noncomputable def powTorus (Y : GT ι) (k : ℕ) : GT ι :=
  { Y with
    ka := fun γ => Y.ka γ ^ k
    ka_abs := fun x hx => by rw [norm_pow, Y.ka_abs x hx, one_pow] }
def TwistedLaw (Y : GT ι) (k : ℕ) (c : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ γ ∈ lat Y.b, ∀ v, F (v + γ) = Y.ka γ ^ k *
    cexp (k * Real.pi * Hf v γ + Real.pi * Hf c γ + k * Real.pi * Hf γ γ / 2) * F v
theorem analyticAt_of_differentiable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {F : W → ℂ} (hF : Differentiable ℂ F) (x : W) : AnalyticAt ℂ F x :=
  SCV.analyticAt_of_differentiableOn (s := Set.univ) hF.differentiableOn univ_mem
open Classical in

noncomputable def jets (Y : GT ι) (k : ℕ) : Submodule ℂ (MvPowerSeries ι ℂ) where
  carrier := {x | ∃ F ∈ (powTorus Y k).Sec k,
    taylorDir (fun i => EuclideanSpace.single i (1 : ℂ)) F = x}
  add_mem' := by
    rintro _ _ ⟨F, hF, rfl⟩ ⟨G, hG, rfl⟩
    exact ⟨F + G, add_mem hF hG, taylorDir_add _ (analyticAt_of_differentiable hF.1 0)
      (analyticAt_of_differentiable hG.1 0)⟩
  zero_mem' := ⟨0, zero_mem _, taylorDir_zero _⟩
  smul_mem' := by
    rintro c _ ⟨F, hF, rfl⟩
    exact ⟨c • F, Submodule.smul_mem _ c hF,
      taylorDir_smul _ c (analyticAt_of_differentiable hF.1 0)⟩
end ThetaJet
open ThetaJet
end GlobalTheory


