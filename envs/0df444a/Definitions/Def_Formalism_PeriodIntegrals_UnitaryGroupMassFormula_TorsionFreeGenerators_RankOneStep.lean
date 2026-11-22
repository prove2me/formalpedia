-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_RankOneStep
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_RankOneStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:01.632094+00:00
-- url     : https://prove2.me/theorems/f4b01669-1a20-40cc-b5be-0fa0a8991030
-- title:
--   Rank One Step
-- statement:
--   Definitions and structural lemmas for Rank One Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorsionFreeGenerators/RankOneStep.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FGTorsionFreeGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.FGTFG
def ProjStep : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M], Module.Projective R M
def SepStep : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] (m : M),
    m ≠ 0 → ∃ g : M →ₗ[R] R, g m ≠ 0
def CopStep : Prop :=
  ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (I J : Ideal R), I ≠ ⊥ → J ≠ ⊥ →
    ∃ a b : R, b ≠ 0 ∧ Ideal.span {a} * J ⊔ Ideal.span {b} * I = Ideal.span {b}
def SplitStep : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M], 2 ≤ Module.finrank R M →
    ∃ (φ : M →ₗ[R] R) (b : R), b ≠ 0 ∧ LinearMap.range φ = Ideal.span {b}
def RankOneStep : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M], Module.finrank R M = 1 →
    ∃ s : Finset M, s.card ≤ 2 ∧ Submodule.span R (s : Set M) = ⊤
end PI.FGTFG


