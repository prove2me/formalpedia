-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_RegSeqQuasiReg
-- name    : Formalism_PeriodIntegrals_RegSeqQuasiReg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:53.89383+00:00
-- url     : https://prove2.me/theorems/392146fc-5fb2-4e1a-b62b-fba6b6669cbf
-- title:
--   Reg Seq Quasi Reg
-- statement:
--   Definitions and structural lemmas for Reg Seq Quasi Reg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/RegSeqQuasiReg.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace PI
def RegSeqQuasiReg : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x) →
    ∀ (k : ℕ) (F : MvPolynomial (Fin n) R), F.IsHomogeneous k →
      MvPolynomial.eval x F ∈ Ideal.span (Set.range x) ^ (k + 1) →
      ∀ m, F.coeff m ∈ Ideal.span (Set.range x)
end PI


