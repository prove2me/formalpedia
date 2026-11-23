-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:28.386819+00:00
-- url     : https://prove2.me/theorems/42db1484-9e8c-4e5a-8680-6977b9fb9efa
-- title:
--   Has Sum Locally Uniformly On Term
-- statement:
--   Definitions and structural lemmas for Has Sum Locally Uniformly On Term, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
namespace AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
def size (μ : A.X) : ℝ := ∑ i, |((Module.Free.chooseBasis ℤ A.X).repr μ i : ℝ)|
def IsConvLine (T₀ : ℝ) : Prop :=
  ∀ μ : A.X, (A.H (A.ct μ) (A.ct μ)).re / 2 - (A.T μ μ).im ≤ T₀ * A.be μ μ
section Conv
variable {A} {T₀ : ℝ} (hT : A.IsConvLine T₀) {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ}
include hT
variable [NeZero j]
end Conv
end AnArc
end GlobalTheory


