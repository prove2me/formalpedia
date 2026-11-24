-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:25:58.624812+00:00
-- url     : https://prove2.me/theorems/8158cd2f-97ee-44e2-b018-69fa2af0c02b
-- title:
--   Mu MEval Pow Eq Zero
-- statement:
--   Definitions and structural lemmas for Mu MEval Pow Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/MuMEvalPowEqZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
def muM : Submonoid ℂ_[l] where
  carrier := muP l
  one_mem' := ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), one_pow 1⟩
  mul_mem' := by
    rintro a b ⟨n, hn, hln, ha⟩ ⟨m, hm, hlm, hb⟩
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases ((Fact.out : l.Prime).dvd_mul).1 h with h | h
      · exact hln h
      · exact hlm h
    · rw [mul_pow, pow_mul, ha, one_pow, mul_comm n m, pow_mul, hb, one_pow, one_mul]
def phiM : MonoidAlgebra ℤ (muM l) →ₐ[ℤ] ℂ_[l] := MonoidAlgebra.lift ℤ ℂ_[l] (muM l) (muM l).subtype
def psiM : MonoidAlgebra ℤ (muM l) →ₐ[ℤ] ℂ_[l] :=
  MonoidAlgebra.lift ℤ ℂ_[l] (muM l) ((muM l).subtype.comp (powMonoidHom l))
end ReciprocityTheory.ChartRestriction.L1


