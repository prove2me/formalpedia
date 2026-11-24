-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_RationalWeightSuccMulInvNorm
-- name    : Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_RationalWeightSuccMulInvNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:40.389732+00:00
-- url     : https://prove2.me/theorems/e55bab1b-1ef9-4bb7-af0d-6f195d6c701d
-- title:
--   Rational Weight Succ Mul Inv Norm
-- statement:
--   Definitions and structural lemmas for Rational Weight Succ Mul Inv Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/RationalWeightSuccMulInvNorm.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace ComplexConjugate
variable {ι : Type} [Fintype ι] {n : Type} [Fintype n] {K : Type} [TopologicalSpace K]
abbrev XS (j : Type) : Type := PiLp 2 fun _ : j => ℂ
def pim (ξ : K → ι → n → ℂ) (p : K × (ι → ℂ)) : XS (ι × n) := WithLp.toLp 2 fun j => 2 * (p.2 j.1 * ξ p.1 j.1 j.2)
def bet (ξ : K → ι → n → ℂ) (q : K × XS (ι × n)) : ι → ℂ := fun w => ∑ i, ξ q.1 w i * conj (q.2 (w, i))
end PositivityTheory.ThKG.Loc.Bump
end


