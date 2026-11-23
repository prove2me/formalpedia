-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SemiDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SemiDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:09:17.629304+00:00
-- url     : https://prove2.me/theorems/de20d5cf-3e50-41ba-aa10-663fa3d7984d
-- title:
--   Semi Defs
-- statement:
--   Definitions and structural lemmas for Semi Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/SemiDefs.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
def NormStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∀ h ∈ Hsub (AF F) σ J P, ∀ n ∈ FrameUnipotentSubgroup (AF F) σ J P, h * n * h⁻¹ ∈ FrameUnipotentSubgroup (AF F) σ J P
def ProjStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∃ π : S0 (AF F) σ J P →* Hsub (AF F) σ J P, Continuous π ∧
      (∀ s : S0 (AF F) σ J P, (s : HA (AF F) σ J) ∈ Hsub (AF F) σ J P →
        ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J) = s) ∧
      (∀ s : S0 (AF F) σ J P, (s : HA (AF F) σ J) ∈ FrameUnipotentSubgroup (AF F) σ J P → π s = 1) ∧
      (∀ s : S0 (AF F) σ J P, (s : HA (AF F) σ J) *
        ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J)⁻¹ ∈ FrameUnipotentSubgroup (AF F) σ J P) ∧
      (∀ s : S0 (AF F) σ J P, (s : HA (AF F) σ J) ∈ HFinIn (AF F) σ J →
        ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J) ∈ HFinIn (AF F) σ J)
end PI.VolSemiDirect.W


