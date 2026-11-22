-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
-- name    : Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:42.129397+00:00
-- url     : https://prove2.me/theorems/d677b457-35c1-4bfa-9f2f-0dd94ec7df6c
-- title:
--   Mem Span Of Norm Le
-- statement:
--   Definitions and structural lemmas for Mem Span Of Norm Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MemSpanOfNormLe.lean

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
namespace Formalism.LT.FrobP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
theorem norm_sigma_le {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp : ‖(p : K)‖ < 1)
    (a : K) (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ q‖ ≤ ‖(p : K)‖ := hσ a ha
  have h2 : ‖a ^ q‖ ≤ 1 := by
    rw [norm_pow]
    first
      | exact pow_le_one₀ (norm_nonneg a) ha
      | exact pow_le_one q (norm_nonneg a) ha
  calc ‖σ a‖ = ‖(σ a - a ^ q) + a ^ q‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ q‖ ‖a ^ q‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (h1.trans hp.le) h2
def sigmaO {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp : ‖(p : K)‖ < 1) :
    unitBall K →+* unitBall K :=
  (σ.comp (unitBall K).subtype).codRestrict (unitBall K)
    (fun x => norm_sigma_le hσ hp x.1 x.2)
def liftO {ι : Type v} (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    MvPowerSeries ι (unitBall K) :=
  fun d => ⟨MvPowerSeries.coeff d A, hA d⟩
end Formalism.LT.FrobP
namespace Formalism.LT
open Formalism.G
end Formalism.LT


