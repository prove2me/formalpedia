-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:21:58.49673+00:00
-- url     : https://prove2.me/theorems/b27b01a9-0221-4076-908b-fdf810b399cc
-- title:
--   Mem Fix Sub
-- statement:
--   Definitions and structural lemmas for Mem Fix Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/MemFixSub.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace PI.SqPairLocal
def fixSub {R : Type} [CommRing R] (σ : R ≃+* R) : Subring R :=
  (σ : R →+* R).eqLocus (RingHom.id R)
def FixedDVR : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    [Finite (IsLocalRing.ResidueField R)] (σ : R ≃+* R), (∀ x, σ (σ x) = x) →
    ∀ ϖ : R, Irreducible ϖ → σ ϖ = ϖ →
      ∃ (_ : IsDiscreteValuationRing (fixSub σ)) (_ : HenselianLocalRing (fixSub σ))
        (_ : Finite (IsLocalRing.ResidueField (fixSub σ))),
        ∀ h : ϖ ∈ fixSub σ, Irreducible (⟨ϖ, h⟩ : fixSub σ)
def RealUnif : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (cj E) = Q →
      ∃ ϖ : 𝓞 E, cj E ϖ = ϖ ∧ ϖ ∈ Q ∧ ϖ ∉ Q ^ 2
end PI.SqPairLocal


