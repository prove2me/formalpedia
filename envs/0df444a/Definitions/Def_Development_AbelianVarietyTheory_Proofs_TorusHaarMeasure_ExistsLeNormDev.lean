-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsLeNormDev
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsLeNormDev
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:02.259838+00:00
-- url     : https://prove2.me/theorems/a59bc73b-45f6-44fb-ab53-fff63aa29546
-- title:
--   Exists Le Norm Dev
-- statement:
--   Definitions and structural lemmas for Exists Le Norm Dev, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsLeNormDev.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.GrpSep
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable def dev {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : Frame Ψ r) (γ : GL (Fin r) E) :
    Frame Ψ r :=
  fun τ => ((mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ - 1 :
    Matrix (Fin r) (Fin r) ℂ)
noncomputable def shift {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 M : Frame Ψ r) : Frame Ψ r :=
  fun τ => (mat x0 τ * (mat M τ + 1) : Matrix (Fin r) (Fin r) ℂ)
noncomputable def oneF (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r :=
  fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
end GlobalTheory.GrpSep
namespace GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory


