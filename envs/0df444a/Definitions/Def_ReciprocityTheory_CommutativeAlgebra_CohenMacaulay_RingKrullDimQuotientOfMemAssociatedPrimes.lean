-- Prove2me | Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RingKrullDimQuotientOfMemAssociatedPrimes
-- name    : ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RingKrullDimQuotientOfMemAssociatedPrimes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:57.916325+00:00
-- url     : https://prove2.me/theorems/f884bac3-dafa-4997-9007-ed89f84b3a11
-- title:
--   Ring Krull Dim Quotient Of Mem Associated Primes
-- statement:
--   Definitions and structural lemmas for Ring Krull Dim Quotient Of Mem Associated Primes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/RingKrullDimQuotientOfMemAssociatedPrimes.lean

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Unmixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence Pointwise
variable {R : Type*} [CommRing R] [IsLocalRing R]
theorem smul_top_eq_self' (I : Ideal R) : (I • (⊤ : Submodule R R)) = I := by
  exact Ideal.mul_top I
theorem span_singleton_eq_smul_top' (x : R) :
    (x • (⊤ : Submodule R R)) = Ideal.span {x} := by
  rw [← Submodule.ideal_span_singleton_smul, smul_top_eq_self']
noncomputable def quotSMulTopEquivQuot' (x : R) :
    QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
  Submodule.quotEquivOfEq _ _ (span_singleton_eq_smul_top' x)
end ReciprocityTheory.CA


