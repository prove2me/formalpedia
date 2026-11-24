-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:34:54.977149+00:00
-- url     : https://prove2.me/theorems/4e8a4a9f-668f-4c26-9bf2-23759e31b2c1
-- title:
--   Principal Ideal Ring At Prime
-- statement:
--   Definitions and structural lemmas for Principal Ideal Ring At Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/PrincipalIdealRingAtPrime.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
namespace PI.ScRefExists.ApP
open PI.ScRefExists.Sk
abbrev Pz (p : ℕ) : Ideal ℤ := Ideal.span {(p : ℤ)}
theorem pz_prime {p : ℕ} (hp : p.Prime) : (Pz p).IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
instance pz_isPrime (p : ℕ) [hp : Fact p.Prime] : (Pz p).IsPrime := pz_prime hp.out
variable (I : Formalism.MainNotions.S.AutInst)
end PI.ScRefExists.ApP
end


