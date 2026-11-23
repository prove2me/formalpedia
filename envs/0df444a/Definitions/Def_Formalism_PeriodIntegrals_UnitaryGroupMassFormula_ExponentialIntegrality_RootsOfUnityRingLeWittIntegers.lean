-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:04.148931+00:00
-- url     : https://prove2.me/theorems/e43e2283-1b3c-4f67-982e-43f7c8333176
-- title:
--   Roots Of Unity Ring Le Witt Integers
-- statement:
--   Definitions and structural lemmas for Roots Of Unity Ring Le Witt Integers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.ExpIntWProof.Key
abbrev S0 (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}
def Fx {R : Type*} [CommRing R] (p : ℕ) (a : R) : Prop := ∃ f : ℕ, 0 < f ∧ a ^ p ^ f = a
section Frob
variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]
end Frob
variable {p : ℕ} [hp : Fact p.Prime]
end PI.ExpIntWProof.Key
namespace PI.ExpIntWProof
end PI.ExpIntWProof
end


