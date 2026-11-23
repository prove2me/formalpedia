-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:02.967486+00:00
-- url     : https://prove2.me/theorems/09af23eb-7a20-4ed5-9c10-48cc41fcabe7
-- title:
--   Mem Adelic Completion Pseudo Basis Iff
-- statement:
--   Definitions and structural lemmas for Mem Adelic Completion Pseudo Basis Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemAdelicCompletionPseudoBasisIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AdLat
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
section
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
def adCoord (e : Module.Basis (Fin n) E (Fin n → E)) (b : Fin n) : (Fin n → RA F E) →+ RA F E where
  toFun w := ∑ i, w i * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b)
  map_zero' := by simp
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
end
end GlobalTheory.AdLat


