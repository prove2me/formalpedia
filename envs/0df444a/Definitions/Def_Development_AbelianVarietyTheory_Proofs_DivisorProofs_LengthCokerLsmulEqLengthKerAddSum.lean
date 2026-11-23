-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSum
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:12.585578+00:00
-- url     : https://prove2.me/theorems/d4db8ce2-8683-42dd-ab13-262332fa1661
-- title:
--   Length Coker Lsmul Eq Length Ker Add Sum
-- statement:
--   Definitions and structural lemmas for Length Coker Lsmul Eq Length Ker Add Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthCokerLsmulEqLengthKerAddSum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.HerbrandLength
open IsLocalRing
variable {A : Type} [CommRing A]
def Concl (b : A) (P : Finset (PrimeSpectrum A)) (M : Type) [AddCommGroup M] [Module A M] : Prop :=
  Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) ≠ ⊤ ∧
  Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b)) =
    Module.length A (LinearMap.ker (LinearMap.lsmul A M b)) +
      ∑ p ∈ P, Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) * Module.length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b}))
end GlobalTheory.HerbrandLength


