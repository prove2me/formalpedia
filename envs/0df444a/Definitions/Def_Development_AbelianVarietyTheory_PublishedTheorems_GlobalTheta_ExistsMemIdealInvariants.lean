-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_ExistsMemIdealInvariants
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_ExistsMemIdealInvariants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:39.882889+00:00
-- url     : https://prove2.me/theorems/c1cf8cbe-8b5f-42f8-816d-a6926975101b
-- title:
--   Exists Mem Ideal Invariants
-- statement:
--   Definitions and structural lemmas for Exists Mem Ideal Invariants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/ExistsMemIdealInvariants.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
namespace GlobalTheory.Published
def idealInvariants (K : Type) [Field K] [NumberField K] [Algebra K ℂ] : Set ℂ :=
  {x | ∃ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair),
    IsIdealLattice 𝔟 L ∧ (latticeCurve L).j = x}
def IdealInvariantsOneOrbitSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ],
    Module.finrank ℚ K = 2 →
    ∀ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair), IsIdealLattice 𝔞 L →
      IsAlgebraic K (latticeCurve L).j ∧
      MulAction.orbit (ℂ ≃ₐ[K] ℂ) (latticeCurve L).j = idealInvariants K
section Use
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
end Use
end GlobalTheory.Published


