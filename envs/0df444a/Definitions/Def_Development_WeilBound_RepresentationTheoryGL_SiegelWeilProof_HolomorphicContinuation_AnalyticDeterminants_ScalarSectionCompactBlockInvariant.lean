-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:47.204585+00:00
-- url     : https://prove2.me/theorems/aaaedc83-934c-456c-bcc4-ede727caf8fc
-- title:
--   Scalar Section Compact Block Invariant
-- statement:
--   Definitions and structural lemmas for Scalar Section Compact Block Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
namespace PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def Dom (n : ℕ) : Set (M2 n) := {x | IsUnit x.det ∧ (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0 ∧ (ub1 x).det ≠ 0}
def hF (j : ℕ) (p q : ℤ) (y : M2 n) : ℂ := f0 p q y * minorOn (blkA j) (wM y) * minorOn (blkB j) (wM y)⁻¹
def InP (P : M2 n) : Prop := InG P ∧ P.toBlocks₂₁ = 0
def c1 (p q : ℤ) (P : M2 n) : ℂ := P.toBlocks₂₂.det ^ (-p) * P.toBlocks₂₂.det ^ (-q)
def c2 (p q : ℤ) (P : M2 n) : ℂ := P.toBlocks₂₂.det ^ (p - n) * P.toBlocks₂₂.det ^ q * P.toBlocks₁₁.det ^ (n : ℤ)
end PositivityTheory.Rg.Sw.LVs


