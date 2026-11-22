-- Prove2me | Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
-- name    : Formalism_LatticeSlopes_CovolAntiSameRank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:47:53.334645+00:00
-- url     : https://prove2.me/theorems/7126fdb5-0f57-42c4-93d8-cc8bc5ba6cc0
-- title:
--   Covol Anti Same Rank
-- statement:
--   Definitions and structural lemmas for Covol Anti Same Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/CovolAntiSameRank.lean

import Definitions.Def_Formalism_LatticeSlopes_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
namespace Formalism.F
def satur {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L N : Submodule ℤ E) :
    Submodule ℤ E :=
  L ⊓ (Submodule.span ℝ (N : Set E)).restrictScalars ℤ
def SlopesBdd : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E), DiscreteTopology L → BddAbove (slopes L)
def CovolAntiSameRank : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (N N' : Submodule ℤ E), DiscreteTopology N' → N ≤ N' → rk N = rk N' → covol N' ≤ covol N
def SaturProps : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L N : Submodule ℤ E), DiscreteTopology L → N ≤ L →
    IsSaturated L (satur L N) ∧ N ≤ satur L N ∧ rk (satur L N) = rk N
def FiniteSaturated : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E), DiscreteTopology L → ∀ X : ℝ,
    {N : Submodule ℤ E | IsSaturated L N ∧ covol N ≤ X}.Finite
def ShortVector : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E), DiscreteTopology L → L ≠ ⊥ →
    ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ ≤ Real.sqrt (rk L : ℝ) * covol L ^ ((1 : ℝ) / (rk L : ℝ))
end Formalism.F


